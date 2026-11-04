import LspCli.Protocol
import LspCli.ProjectProcess
import Lean.Data.Lsp.Communication
import Std.Async.Timer
import Std.Sync.Channel
import Std.Internal.UV.System
open Lean System Std Std.Async Lean.JsonRpc
namespace LspCli

/-- Absolute monotonic deadline, shared by every phase of an operation. -/
abbrev Deadline := Nat

def remaining (deadline : Deadline) : IO Nat := do
  let now ← IO.monoMsNow
  if now ≥ deadline then throw <| IO.userError "timeout: operation deadline exceeded"
  return deadline - now

def freshNonce : IO String := do
  let bytes ← (Async.ofPromise (Std.Internal.UV.System.random 32)).block
  return String.ofList <| bytes.data.toList.flatMap fun b =>
    ["0123456789abcdef".toList[b.toNat / 16]!, "0123456789abcdef".toList[b.toNat % 16]!]

abbrev Reply := CloseableChannel (Except IO.Error Json)

def awaitReply (ch : Reply) (deadline : Deadline) : IO Json := do
  let ms ← remaining deadline
  let result ← (do
    let timer ← Selector.sleep (.ofInt ms)
    Selectable.one #[
      .case ch.recvSelector (fun r => pure r),
      .case timer (fun _ => pure none)] : Async (Option (Except IO.Error Json))).block
  match result with
  | some r => IO.ofExcept r
  | none => throw <| IO.userError "timeout: operation deadline exceeded"

structure DiagnosticState where
  uri : String
  version : Nat
  diagnostics : Array Json := #[]
  received : Bool := false

structure WireState where
  nextId : Nat := 0
  pending : Array (RequestID × Reply) := #[]
  diagnostics : Array DiagnosticState := #[]
  watchers : Bool := false
  dead : Bool := false
  stderrTail : String := ""

structure Transport where
  child : IO.Process.Child {stdin := .piped, stdout := .piped, stderr := .piped}
  writer : Mutex IO.FS.Stream
  state : Mutex WireState

namespace Transport

def send (t : Transport) (msg : JsonRpc.Message) : IO Unit :=
  t.writer.atomically do (← get).writeLspMessage msg

def notify (t : Transport) (method : String) (params : Json) : IO Unit :=
  t.send (.notification method (Json.toStructured? params).toOption)

def fail (t : Transport) (message : String) : IO Unit := do
  t.state.atomically do
    let s ← get
    set {s with dead := true, pending := #[]}
    for (_, ch) in s.pending do
      discard <| ch.send (.error (IO.userError message))
      ch.close

private def deliver (t : Transport) (id : RequestID) (result : Except IO.Error Json) : IO Unit := do
  t.state.atomically do
    let s ← get
    set {s with pending := s.pending.filter (·.1 != id)}
    if let some (_, ch) := s.pending.find? (·.1 == id) then
      discard <| ch.send result
      ch.close

/-- Register before writing; IDs are never reused, including after cancellation. -/
def request (t : Transport) (method : String) (params : Json) (deadline : Deadline) : IO Json := do
  discard <| remaining deadline
  let ch ← CloseableChannel.new
  let id ← t.state.atomically do
    let s ← get
    if s.dead then throw <| IO.userError "protocol: server closed"
    let id : RequestID := .num s.nextId
    set {s with nextId := s.nextId + 1, pending := s.pending.push (id, ch)}
    pure id
  try
    t.send (.request id method (Json.toStructured? params).toOption)
    awaitReply ch deadline
  catch e =>
    t.state.atomically <| modify fun s => {s with pending := s.pending.filter (·.1 != id)}
    ch.close
    try t.notify "$/cancelRequest" (Json.mkObj [("id", toJson id)]) catch _ => pure ()
    throw e

def track (t : Transport) (uri : String) (version : Nat) : IO Unit :=
  t.state.atomically <| modify fun s => {s with diagnostics := (s.diagnostics.filter (·.uri != uri)).push ({uri, version} : DiagnosticState)}

private def publication (t : Transport) (params : Json) : IO Unit := do
  let .ok p := (fromJson? params : Except String Lean.Lsp.PublishDiagnosticsParams) | return
  let some version := p.version? | return -- unversioned publications cannot establish freshness
  t.state.atomically <| modify fun s => {s with diagnostics := s.diagnostics.map fun d =>
    if d.uri == p.uri && version == (Int.ofNat d.version) then
      {d with received := true, diagnostics :=
        (if p.isIncremental?.getD false then d.diagnostics else #[]) ++ p.diagnostics.map toJson}
    else d}

private def serverRequest (t : Transport) (id : RequestID) (method : String) (params : Json) : IO Unit := do
  if method == "client/registerCapability" then
    let registrations := (params.getObjValAs? (Array Json) "registrations").toOption.getD #[]
    let supported := !registrations.isEmpty && registrations.all fun reg =>
      (reg.getObjValAs? String "method").toOption == some "workspace/didChangeWatchedFiles" &&
      ((reg.getObjVal? "registerOptions").bind (·.getObjValAs? (Array Json) "watchers")).toOption.any (fun ws =>
        !ws.isEmpty && ws.all (fun w => (w.getObjValAs? String "globPattern").toOption.any (fun p => p == "**/*.lean" || p == "**/*.ilean")))
    if supported then
      t.state.atomically <| modify fun s => {s with watchers := true}
      t.send (.response id Json.null)
    else t.send (.responseError id .invalidParams "unsupported watcher registration" none)
  else if method == "workspace/applyEdit" then
    t.send (.response id (Json.mkObj [("applied", toJson false), ("failureReason", toJson "read-only client")]))
  else t.send (.responseError id .methodNotFound "unsupported client request" none)

private partial def reader (t : Transport) : IO Unit := do
  try
    let input := IO.FS.Stream.ofHandle t.child.stdout
    repeat
      match ← input.readLspMessage with
      | .response id result => t.deliver id (.ok result)
      | .responseError id _ message _ => t.deliver id (.error (IO.userError s!"protocol: {message}"))
      | .request id method params => t.serverRequest id method (params.map toJson |>.getD Json.null)
      | .notification method params =>
        if method == "textDocument/publishDiagnostics" then
          t.publication (params.map toJson |>.getD Json.null)
  catch e => t.fail s!"protocol: server reader ended: {e}"

private partial def drain (t : Transport) : IO Unit := do
  try
    repeat
      let bytes ← t.child.stderr.read 4096
      if bytes.isEmpty then break
      let chunk := (String.fromUTF8? bytes).getD "<non-UTF8 stderr>"
      t.state.atomically <| modify fun s =>
        let text := s.stderrTail ++ chunk
        {s with stderrTail := String.ofList (text.toList.drop (text.length - 16384))}
  catch _ => pure ()

/-- Structured launch allows a native fake executable without shell interpretation. -/
def spawn (root : FilePath) (cmd : String := "lake") (args : Array String := #["serve", "--"]) : IO Transport := do
  let cmd ← if cmd == "lake" then ProjectProcess.lake else pure cmd
  let child ← IO.Process.spawn {cmd, args, cwd := some root, stdin := .piped, stdout := .piped, stderr := .piped, setsid := true, env := ProjectProcess.environment}
  let t : Transport := {child, writer := ← Mutex.new (IO.FS.Stream.ofHandle child.stdin), state := ← Mutex.new {}}
  discard <| IO.asTask (t.reader) Task.Priority.dedicated
  discard <| IO.asTask (t.drain) Task.Priority.dedicated
  return t

end Transport
end LspCli
