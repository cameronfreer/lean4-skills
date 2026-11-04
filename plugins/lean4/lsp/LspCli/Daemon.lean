import LspCli.Trials
import LspCli.Session
import LspCli.Socket
open Lean System Std Std.Async
namespace LspCli.Daemon

structure Descriptor where
  schema : String := "lean4-lsp/v1"
  root : String
  port : Nat
  token : String
  identity : String
  deriving ToJson, FromJson
structure Envelope where
  schema : String := "lean4-lsp/v1"
  root : String
  token : String
  identity : String
  deadline : Nat
  request : Request
  deriving ToJson, FromJson

def cacheDir (root : FilePath) : IO FilePath := do
  let base ← match ← IO.getEnv "XDG_CACHE_HOME" with
    | some p => pure (FilePath.mk p)
    | none => pure ((FilePath.mk ((← IO.getEnv "HOME").getD "/tmp")) / ".cache")
  let parent := base / "lean4-skills-lsp"
  IO.FS.createDirAll parent
  IO.setAccessRights parent {user := {read := true, write := true, execution := true}}
  let dir := parent / toString (hash root.toString)
  IO.FS.createDirAll dir
  IO.setAccessRights dir {user := {read := true, write := true, execution := true}}
  return dir

private def readDescriptor (dir : FilePath) : IO Descriptor := do
  try IO.ofExcept ((Json.parse (← IO.FS.readFile (dir / "session.json"))).bind fromJson?)
  catch _ => throw <| IO.userError "protocol: invalid session descriptor"
private def publish (dir : FilePath) (d : Descriptor) : IO Unit := do
  let temp := dir / s!"session-{d.identity}.tmp"
  IO.FS.writeFile temp (toJson d).compress
  IO.setAccessRights temp {user := {read := true, write := true}}
  IO.FS.rename temp (dir / "session.json")
private def clear (dir : FilePath) (identity : String) : IO Unit := do
  try
    if (← readDescriptor dir).identity == identity then IO.FS.removeFile (dir / "session.json")
  catch _ => pure ()

private def address (port : Nat) : Std.Net.SocketAddress :=
  .v4 {addr := {octets := #v[127, 0, 0, 1]}, port := port.toUInt16}

private def exchange (d : Descriptor) (r : Request) (deadline : Deadline) : IO Response := do
  let root ← resolveProject r.project
  unless d.schema == "lean4-lsp/v1" && d.root == root.toString && d.port > 0 && d.port ≤ 65535 do
    throw <| IO.userError "protocol: descriptor root/version mismatch"
  let envelope : Envelope := {root := root.toString, token := d.token, identity := d.identity, deadline, request := r}
  let result ← Socket.bounded (do
    let client ← TCP.Socket.Client.mk
    try
      client.connect (address d.port)
      Socket.sendJson client (toJson envelope)
      Socket.readJson client deadline
    finally
      client.shutdown) deadline
  let response : Response ← IO.ofExcept (fromJson? result)
  unless response.schema == "lean4-lsp/v1" && response.projectRoot == some root.toString do
    throw <| IO.userError "protocol: handshake root/version mismatch"
  return response

private def rejected (root : FilePath) (message : String) : Response :=
  {ok := false, operation := "handshake", projectRoot := some root.toString, status := "unavailable", error := some ⟨"authentication_failed", message, 3⟩}

/-- One accepted connection is one whole serialized operation. TCP backlog is bounded to eight. -/
private def serve (server : TCP.Socket.Server) (s : Session) (d : Descriptor) (idleMs : Nat) : IO Unit := do
  let mut lastActivity ← IO.monoMsNow
  repeat
    let now ← IO.monoMsNow
    if now - lastActivity ≥ idleMs || (← s.transport.state.atomically get).dead then break
    let some client ← (Socket.acceptWithin server (min 1000 (idleMs - (now - lastActivity)))).block | continue
    let mut stop := false
    let mut authenticated := false
    try
      let wire ← (Socket.readJson client ((← IO.monoMsNow) + 1000)).block
      let envelope : Envelope ← IO.ofExcept (fromJson? wire)
      let valid := envelope.schema == d.schema && envelope.root == d.root && envelope.token == d.token && envelope.identity == d.identity
      authenticated := valid
      let response ← if !valid then pure (rejected s.root "invalid session credentials or root/version")
        else do
          let r := envelope.request
          unless r.project == some s.root do throw <| IO.userError "protocol: request project mismatch"
          let budget := envelope.deadline - (← IO.monoMsNow)
          if budget == 0 then pure (Session.failure r s.root (IO.userError "timeout: queue deadline exceeded"))
          else do
            lastActivity ← IO.monoMsNow
            if r.operation == .stop then
              s.close
              stop := true
              pure {ok := true, operation := "stop", projectRoot := some s.root.toString, status := "stopped"}
            else if r.operation == .attempt then Trials.run s {r with timeoutMs := budget}
            else s.inspect {r with timeoutMs := budget}
      discard <| Socket.bounded (do Socket.sendJson client (toJson response); pure Json.null) ((← IO.monoMsNow) + 1000)
    catch e =>
      -- A bad or stalled unauthenticated peer owns only its connection.
      if authenticated && (e.toString.splitOn "timeout:").length > 1 then
        s.state.atomically <| modify fun st => {st with retired := true}
      let response := Session.failure {operation := .status} s.root e
      try discard <| Socket.bounded (do Socket.sendJson client (toJson response); pure Json.null) ((← IO.monoMsNow) + 200) catch _ => pure ()
    try
      discard <| Socket.bounded (do client.shutdown; pure Json.null) ((← IO.monoMsNow) + 100)
    catch e =>
      -- A bad or stalled unauthenticated peer owns only its connection.
      if authenticated && (e.toString.splitOn "timeout:").length > 1 then
        s.state.atomically <| modify fun st => {st with retired := true}
    if stop || (← s.state.atomically get).retired || (← s.transport.state.atomically get).dead then break
    if authenticated then lastActivity ← IO.monoMsNow

/-- Entry point for the same binary's private daemon mode. Lock inode is never replaced/deleted. -/
def runWithIdle (root : FilePath) (idleMs : Nat := 600000) (startupMs : Nat := 30000) : IO UInt32 := do
  let root ← resolveProject (some root)
  let dir ← cacheDir root
  let lock ← IO.FS.Handle.mk (dir / "owner.lock") .append
  unless ← lock.tryLock do return 0
  try
    let s ← Session.startWith root ((← IO.monoMsNow) + startupMs)
    try
      let server ← TCP.Socket.Server.mk
      server.bind (address 0)
      server.listen 8
      let addr ← server.getSockName
      let port := match addr with | .v4 a => a.port.toNat | .v6 a => a.port.toNat
      let d : Descriptor := {root := root.toString, port, token := ← freshNonce, identity := s.nonce}
      publish dir d
      try serve server s d idleMs finally clear dir d.identity
      return 0
    finally s.close
  finally lock.unlock

def run (root : FilePath) : IO UInt32 := runWithIdle root

private partial def awaitOwner (root dir : FilePath) (deadline : Deadline)
    (launcher : Option (IO.Process.Child {stdin := .null, stdout := .null, stderr := .null}) := none) : IO Descriptor := do
  discard <| remaining deadline
  if ← (dir / "session.json").pathExists then
    let d ← readDescriptor dir
    unless d.schema == "lean4-lsp/v1" && d.root == root.toString do
      throw <| IO.userError "protocol: descriptor root/version mismatch"
    return d
  if let some child := launcher then
    if let some code ← child.tryWait then
      if code != 0 then throw <| IO.userError "protocol: daemon startup failed"
      return ← awaitOwner root dir deadline none
  if launcher.isNone then
    let lock ← IO.FS.Handle.mk (dir / "owner.lock") .append
    if ← lock.tryLock then
      lock.unlock
      throw <| IO.userError "owner_released: retry ownership acquisition"
  IO.sleep 10
  awaitOwner root dir deadline launcher

/-- Resolve ownership under the same lifetime lock; a stale descriptor is never authority to kill. -/
partial def call (request : Request) : IO Response := do
  let root ← resolveProject request.project
  let r := {request with project := some root}
  let deadline := (← IO.monoMsNow) + r.timeoutMs
  try
    let dir ← cacheDir root
    let lock ← IO.FS.Handle.mk (dir / "owner.lock") .append
    let mut launcher := none
    let owns ← lock.tryLock
    if owns then
      -- Holding the inode lock proves that no live daemon owns any descriptor at this key.
      try
        if ← (dir / "session.json").pathExists then IO.FS.removeFile (dir / "session.json")
      finally lock.unlock
      if r.operation == .stop || r.operation == .status then
        return {ok := true, operation := r.operation.name, projectRoot := some root.toString, status := "stopped"}
      let exe ← IO.appPath
      let child ← IO.Process.spawn {cmd := exe.toString, args := #["--daemon", root.toString, "--startup-ms", toString (← remaining deadline)], stdin := .null, stdout := .null, stderr := .null, setsid := true}
      launcher := some child
    let descriptor ← awaitOwner root dir deadline launcher
    exchange descriptor r deadline
  catch e =>
    if (e.toString.splitOn "owner_released:").length > 1 then
      let now ← IO.monoMsNow
      if now < deadline then return ← call {r with timeoutMs := deadline - now}
      return Session.failure r root (IO.userError "timeout: ownership deadline exceeded")
    return Session.failure r root e
end LspCli.Daemon
