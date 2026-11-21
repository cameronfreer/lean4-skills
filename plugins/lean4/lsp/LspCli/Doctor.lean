import LspCli.Protocol
import LspCli.ProjectProcess
import Lean.Data.Lsp.Communication
open Lean System Lean.JsonRpc
namespace LspCli

structure DoctorResult where
  toolchainAvailable : Bool
  serverAvailable : Bool
  timedOut : Bool := false
  deriving Repr

private partial def waitUntil (task : Task α) (deadline : Nat) : IO Bool := do
  if ← IO.hasFinished task then return true
  if (← IO.monoMsNow) ≥ deadline then return false
  IO.sleep 10
  waitUntil task deadline

private partial def waitResponse (input output : IO.FS.Stream) (expected : RequestID) : IO Json := do
  match ← input.readLspMessage with
  | .response id result => if id == expected then return result else throw <| IO.userError "unexpected response ID"
  | .responseError .. => throw <| IO.userError "server returned an error"
  | .request id _ _ =>
    output.writeLspMessage (.responseError id .methodNotFound "probe does not register capabilities" none)
    waitResponse input output expected
  | .notification .. => waitResponse input output expected

private def handshake (root : FilePath) (child : IO.Process.Child {stdin := .piped, stdout := .piped, stderr := .null}) : IO Unit := do
  let input := IO.FS.Stream.ofHandle child.stdout
  let output := IO.FS.Stream.ofHandle child.stdin
  let params := Json.mkObj [("processId", Json.null), ("rootUri", toJson (System.Uri.pathToUri root)), ("capabilities", Json.mkObj [])]
  output.writeLspRequest (⟨1, "initialize", params⟩ : Lean.JsonRpc.Request Json)
  let result ← waitResponse input output 1
  unless (result.getObjVal? "capabilities").isOk do throw <| IO.userError "invalid initialize result"
  output.writeLspNotification (⟨"initialized", Json.mkObj []⟩ : Notification Json)
  output.writeLspRequest (⟨2, "shutdown", Json.null⟩ : Lean.JsonRpc.Request Json)
  discard <| waitResponse input output 2
  output.writeLspNotification (⟨"exit", Json.null⟩ : Notification Json)

private def probeServer (root : FilePath) (cmd : String) (deadline : Nat) : IO DoctorResult := do
  try
    let server ← IO.Process.spawn {cmd, args := #["serve", "--"], cwd := some root, stdin := .piped, stdout := .piped, stderr := .null, setsid := true, env := ProjectProcess.environment}
    let task ← IO.asTask (handshake root server) Task.Priority.dedicated
    let finished ← waitUntil task deadline
    let ok := finished && task.get.isOk
    if (← server.tryWait).isNone then
      try server.kill catch _ => pure ()
    discard <| IO.asTask server.wait Task.Priority.dedicated
    return ⟨true, ok, !finished⟩
  catch _ => return ⟨true, false, false⟩

/-- Short-lived project probe. The deadline covers both phases. -/
def probeProject (root : FilePath) (timeoutMs : Nat) (cmd : String := "lake") : IO DoctorResult := do
  let deadline := (← IO.monoMsNow) + timeoutMs
  let cmd ← if cmd == "lake" then ProjectProcess.lake else pure cmd
  try
    let version ← IO.Process.spawn {cmd, args := #["env", "lean", "--version"], cwd := some root, stdin := .null, stdout := .null, stderr := .null, setsid := true, env := ProjectProcess.environment}
    let task ← IO.asTask version.wait Task.Priority.dedicated
    unless ← waitUntil task deadline do
      try version.kill catch _ => pure ()
      return ⟨false, false, true⟩
    unless (← IO.ofExcept task.get) == 0 do return ⟨false, false, false⟩
    return ← probeServer root cmd deadline
  catch _ => return ⟨false, false, false⟩
end LspCli
