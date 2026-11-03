import LspCli.Watcher
import LspCli.Positions
open Lean System Std
namespace LspCli

/-- Exact retained snapshot. Virtual paths need not exist; identities change on eviction. -/
structure Document where
  uri : String
  path : FilePath
  text : String
  version : Nat
  identity : String
  instanceId : Nat
  virtual : Bool := false

structure SessionState where
  documents : Array Document := #[]
  nextInstance : Nat := 0
  versionClock : Nat := 0
  snapshot : Snapshot := {}
  scanMs : Nat := 0
  retired : Bool := false
  closed : Bool := false
  phase : String := "idle"

structure Session where
  root : FilePath
  nonce : String
  transport : Transport
  state : Mutex SessionState
  config : String

namespace Session

def configIdentity (root : FilePath) : IO String := do
  let mut result := ""
  for name in ["lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json"] do
    let path := root / name
    let content ← if ← path.pathExists then IO.FS.readFile path else pure "<absent>"
    result := result ++ name ++ ":" ++ toString content.length ++ ":" ++ content ++ "\n"
  return result

def closeDocument (s : Session) (uri : String) : IO Unit := do
  s.transport.notify "textDocument/didClose" (toJson ({uri} : Lean.Lsp.TextDocumentIdentifier) |> fun d => Json.mkObj [("textDocument", d)])
  s.state.atomically <| modify fun st => {st with documents := st.documents.filter (·.uri != uri)}
  s.transport.state.atomically <| modify fun st => {st with diagnostics := st.diagnostics.filter (·.uri != uri)}

private partial def waitChild (s : Session) (deadline : Deadline) : IO Bool := do
  if (← s.transport.child.tryWait).isSome then return true
  if (← IO.monoMsNow) ≥ deadline then return false
  IO.sleep 10
  waitChild s deadline

/-- Graceful shutdown acknowledges worker termination; fallback signals only our retained child. -/
def close (s : Session) : IO Unit := do
  let already ← s.state.atomically do
    let st ← get
    set {st with retired := true, closed := true}
    pure st.closed
  if already then return
  let completed ← CloseableChannel.new
  discard <| IO.asTask (do
    try
      for d in (← s.state.atomically get).documents do s.closeDocument d.uri
      discard <| s.transport.request "shutdown" Json.null ((← IO.monoMsNow) + 1200)
      s.transport.notify "exit" Json.null
      discard <| completed.send (.ok Json.null)
    catch e => discard <| completed.send (.error e)) Task.Priority.dedicated
  try discard <| awaitReply completed ((← IO.monoMsNow) + 1500) catch _ => pure ()
  completed.close
  unless ← s.waitChild ((← IO.monoMsNow) + 500) do
    try s.transport.child.kill catch _ => pure ()
    unless ← s.waitChild ((← IO.monoMsNow) + 500) do
      discard <| IO.asTask s.transport.child.wait Task.Priority.dedicated
  s.transport.fail "protocol: session closed"

def startWith (root : FilePath) (deadline : Deadline) (cmd : String := "lake") (args : Array String := #["serve", "--"]) : IO Session := do
  let root ← IO.FS.realPath root
  let nonce ← freshNonce
  let config ← configIdentity root
  let snapshot ← Watcher.scan root deadline
  let transport ← Transport.spawn root cmd args
  let s : Session := {root, nonce, config, transport, state := ← Mutex.new {snapshot}}
  try
    let params := Json.mkObj [("processId", Json.null), ("rootUri", toJson (System.Uri.pathToUri root)),
      ("capabilities", Json.mkObj [("lean", Json.mkObj [("incrementalDiagnosticSupport", toJson true)]),
        ("workspace", Json.mkObj [("didChangeWatchedFiles", Json.mkObj [("dynamicRegistration", toJson true)])]),
        ("textDocument", Json.mkObj [("codeAction", Json.mkObj [("dataSupport", toJson true), ("resolveSupport", Json.mkObj [("properties", toJson #["edit"])])])])])]
    let result ← transport.request "initialize" params deadline
    unless (result.getObjVal? "capabilities").isOk do throw <| IO.userError "protocol: invalid initialize response"
    transport.notify "initialized" (Json.mkObj [])
    return {s with config := ← configIdentity root}
  catch e => s.close; throw e

def start (root : FilePath) : IO Session := do
  startWith root ((← IO.monoMsNow) + 30000)

/-- Re-read registered trees before a barrier. A failed/expired scan never updates the snapshot. -/
def refresh (s : Session) (deadline : Deadline) : IO Unit := do
  if (← s.state.atomically get).retired then throw <| IO.userError "protocol: retired session"
  if (← configIdentity s.root) != s.config then throw <| IO.userError "stale_session: toolchain or Lake configuration changed; retry in a new session"
  let start ← IO.monoMsNow
  let after ← Watcher.scan s.root deadline
  let before := (← s.state.atomically get).snapshot
  let changes := Watcher.changes before after
  if !changes.isEmpty then
    -- Lean registers these exact patterns. Even if registration is in flight, delivery is valid LSP.
    s.transport.notify "workspace/didChangeWatchedFiles" (toJson ({changes} : Lean.Lsp.DidChangeWatchedFilesParams))
  discard <| remaining deadline
  let elapsed := (← IO.monoMsNow) - start
  s.state.atomically <| modify fun st => {st with snapshot := after, scanMs := elapsed}

/-- Open/update an explicit snapshot. At most one disk and one virtual worker are retained.
    Calls must be serialized with the enclosing operation; the protocol reader never takes that lock. -/
def openDocument (s : Session) (path : FilePath) (text : String) (virtual : Bool := false) : IO Document := do
  let path := if path.isAbsolute then path else s.root / path
  let existingFile ← path.pathExists
  if virtual && existingFile then throw <| IO.userError "invalid: virtual documents must not name an existing file"
  let path ← if existingFile then IO.FS.realPath path else do
    let some parent := path.parent | throw <| IO.userError "invalid: document has no parent"
    let some name := path.fileName | throw <| IO.userError "invalid: document has no filename"
    pure ((← IO.FS.realPath parent) / name)
  unless (s.root.toString ++ "/").isPrefixOf path.toString do
    throw <| IO.userError "invalid: document is outside project root"
  let uri := System.Uri.pathToUri path
  let st ← s.state.atomically get
  if st.retired then throw <| IO.userError "protocol: retired session"
  let nextVersion := st.versionClock + 1
  if let some old := st.documents.find? (·.uri == uri) then
    if old.virtual != virtual then throw <| IO.userError "invalid: virtual document aliases live source"
    if old.text == text then return old
    let d := {old with text, version := nextVersion, identity := s!"{s.nonce}/{old.instanceId}/{nextVersion}"}
    s.transport.track uri d.version
    s.transport.notify "textDocument/didChange" (toJson ({textDocument := {uri, version? := some d.version}, contentChanges := #[.fullChange text]} : Lean.Lsp.DidChangeTextDocumentParams))
    s.state.atomically <| modify fun st => {st with versionClock := nextVersion, documents := st.documents.map fun x => if x.uri == uri then d else x}
    return d
  for old in st.documents do
    if old.virtual == virtual then s.closeDocument old.uri
  let serial := st.nextInstance + 1
  let d : Document := {uri, path, text, virtual, version := nextVersion, instanceId := serial, identity := s!"{s.nonce}/{serial}/{nextVersion}"}
  s.transport.track uri d.version
  s.transport.notify "textDocument/didOpen" (toJson ({textDocument := {uri, languageId := "lean4", version := nextVersion, text}, dependencyBuildMode? := some .never} : Lean.Lsp.LeanDidOpenTextDocumentParams))
  s.state.atomically <| modify fun st => {st with documents := st.documents.push d, nextInstance := serial, versionClock := nextVersion}
  return d

/-- Current-version completion through the one shared reader; absent publications are not clean. -/
def waitDocument (s : Session) (d : Document) (deadline : Deadline) : IO (Array Json) := do
  discard <| s.transport.request "textDocument/waitForDiagnostics" (toJson ({uri := d.uri, version := d.version} : Lean.Lsp.WaitForDiagnosticsParams)) deadline
  let current := (← s.state.atomically get).documents.find? (·.uri == d.uri)
  unless current.any (·.identity == d.identity) do throw <| IO.userError "stale_input: document changed during barrier"
  let cached := (← s.transport.state.atomically get).diagnostics.find? (fun x => x.uri == d.uri && x.version == d.version)
  let some cached := cached | throw <| IO.userError "protocol: missing diagnostics state"
  unless cached.received do throw <| IO.userError "protocol: diagnostics barrier completed without a versioned publication"
  return cached.diagnostics

/-- Native nullable plain goals; callers must preserve null versus an empty goals array. -/
def plainGoal (s : Session) (d : Document) (pos : PublicPosition) (deadline : Deadline) : IO Json := do
  let position ← IO.ofExcept <| (toLspPosition (FileMap.ofString d.text) pos).mapError (·.message)
  s.transport.request "$/lean/plainGoal" (toJson ({textDocument := {uri := d.uri}, position} : Lean.Lsp.PlainGoalParams)) deadline

def goalStatus (goal : Json) : String :=
  if goal == Json.null then "no_goal_at_position"
  else if (goal.getObjValAs? (Array Json) "goals").toOption.any (·.isEmpty) then "closed_local_goals"
  else "goals_present"

private def hasErrors (ds : Array Json) : Bool :=
  ds.any fun d => (d.getObjValAs? Nat "severity").toOption == some 1
private def staleImports (ds : Array Json) : Bool :=
  ds.any fun d => (d.getObjValAs? String "code").toOption == some "$/lean/staleDependency" ||
    (d.getObjValAs? String "message").toOption.any (fun m => (m.splitOn "Imports are out of date").length > 1)

/-- Map exceptions once, consistently across direct calls and daemon dispatch. -/
def failure (r : Request) (root : FilePath) (e : IO.Error) : Response := Id.run do
  let message := e.toString
  let timeout := (message.splitOn "timeout:").length > 1
  let stale := (message.splitOn "stale_").length > 1
  let staleSession := (message.splitOn "stale_session:").length > 1
  return {ok := false, operation := r.operation.name, projectRoot := some root.toString, data := if r.operation == .search then Json.mkObj [("complete", toJson false)] else Json.null, status := if timeout then "timeout" else if staleSession then "stale_session" else if stale then "stale_input" else "unavailable", error := some ⟨if timeout then "timeout" else if staleSession then "stale_session" else if stale then "stale_input" else "protocol_failure", message, if timeout || stale then 4 else 3⟩}

-- Public range conversion is handled below for every LSP response before it leaves the CLI.
def publicJson (s : Session) (uri : String) (value : Json) : IO Json :=
  Positions.convert (fun uri => do
    if let some d := (← s.state.atomically get).documents.find? (·.uri == uri) then return d.text
    let some path := System.Uri.fileUriToPath? uri | throw <| IO.userError "protocol: cannot resolve response URI"
    IO.FS.readFile path) uri value

private def observe (s : Session) (r : Request) (deadline : Deadline) : IO Response := do
  s.state.atomically <| modify fun st => {st with phase := "scanning"}
  s.refresh deadline
  let base : Response := {ok := true, operation := r.operation.name, projectRoot := some s.root.toString, status := "ok"}
  if r.operation == .status then
    return {base with data := Json.mkObj [("sessionIdentity", toJson s.nonce), ("serverPid", toJson s.transport.child.pid.toNat), ("scanDurationMs", toJson (← s.state.atomically get).scanMs)]}
  if r.operation == .search then
    -- Watched-file events do not update an already open worker's source snapshot.
    -- Synchronize each retained disk document and its index before claiming completeness.
    for previous in (← s.state.atomically get).documents do
      unless previous.virtual do
        let path ← resolveFile s.root previous.path
        let current ← s.openDocument path (← IO.FS.readFile path)
        discard <| s.waitDocument current deadline
        discard <| s.transport.request "$/lean/waitForILeans" (toJson ({uri? := some current.uri, version? := some current.version} : Lean.Lsp.WaitForILeansParams)) deadline
    discard <| s.transport.request "$/lean/waitForILeans" (toJson ({} : Lean.Lsp.WaitForILeansParams)) deadline
    let result ← s.transport.request "workspace/symbol" (toJson ({query := r.query.getD ""} : Lean.Lsp.WorkspaceSymbolParams)) deadline
    let symbols ← IO.ofExcept (result.getArr?)
    return {base with data := Json.mkObj [("symbols", ← s.publicJson "" (toJson (symbols.extract 0 (r.limit.getD 100)))), ("complete", toJson true)]}
  if r.operation == .attempt then throw <| IO.userError "protocol: isolated trials are not installed yet"
  let some file := r.file | throw <| IO.userError "invalid: missing file"
  let path ← resolveFile s.root file
  let d ← s.openDocument path (← IO.FS.readFile path)
  let base := {base with file := some path.toString, documentVersion := some d.version, sourceIdentity := some d.identity}
  if let .error e := checkSourceIdentity r.expectSource (some d.identity) then return {base with ok := false, status := "stale_input", error := some e}
  s.state.atomically <| modify fun st => {st with phase := "elaborating"}
  let diagnostics ← s.waitDocument d deadline
  s.state.atomically <| modify fun st => {st with phase := "query"}
  if staleImports diagnostics then
    return {base with ok := false, status := "stale_dependency", data := ← s.publicJson d.uri (toJson diagnostics), error := some ⟨"stale_dependency", "Imports changed. Run the project's dependency-aware lake build, then stop/restart this session.", 4⟩}
  let error := if hasErrors diagnostics then some (⟨"lean_diagnostics", "Lean reported errors. Missing imports require the project dependency build and a session restart; inspection does not build dependencies.", 1⟩ : CliError) else none
  let base := {base with error, ok := error.isNone}
  if r.operation == .diagnostics then return {base with data := ← s.publicJson d.uri (toJson diagnostics)}
  let publicPos : PublicPosition := ⟨r.line.getD 1, r.column.getD 1⟩
  let position ← match toLspPosition (FileMap.ofString d.text) publicPos with
    | .ok p => pure p
    | .error e => return {base with ok := false, status := "invalid_invocation", error := some e}
  if r.operation == .goal then
    let before ← s.plainGoal d publicPos deadline
    if r.column.isSome then return {base with status := goalStatus before, data := before}
    let line := (d.text.splitOn "\n")[publicPos.line - 1]?.getD ""
    let after ← s.plainGoal d ⟨publicPos.line, line.length + 1⟩ deadline
    return {base with status := goalStatus after, data := Json.mkObj [("before", Json.mkObj [("status", toJson (goalStatus before)), ("goal", before)]), ("after", Json.mkObj [("status", toJson (goalStatus after)), ("goal", after)])]}
  if r.operation == .definition || r.operation == .references then
    discard <| s.transport.request "$/lean/waitForILeans" (toJson ({uri? := some d.uri, version? := some d.version} : Lean.Lsp.WaitForILeansParams)) deadline
  let result ← if r.operation == .codeActions then do
      let params : Lean.Lsp.CodeActionParams := {textDocument := {uri := d.uri}, range := ⟨position, position⟩, context := {diagnostics := ← IO.ofExcept (fromJson? (toJson diagnostics))}}
      let actions ← s.transport.request "textDocument/codeAction" (toJson params) deadline
      let actions : Array Lean.Lsp.CodeAction ← IO.ofExcept (fromJson? actions)
      let resolved ← actions.mapM fun a => if a.data?.isSome then s.transport.request "codeAction/resolve" (toJson a) deadline else pure (toJson a)
      pure (toJson resolved)
    else if r.operation == .references then
      s.transport.request "textDocument/references" (toJson ({textDocument := {uri := d.uri}, position, context := {includeDeclaration := true}} : Lean.Lsp.ReferenceParams)) deadline
    else s.transport.request (if r.operation == .hover then "textDocument/hover" else "textDocument/definition") (toJson ({textDocument := {uri := d.uri}, position} : Lean.Lsp.TextDocumentPositionParams)) deadline
  return {base with data := ← s.publicJson d.uri result}

/-- Bound an entire serialized operation, including filesystem work and writes. On timeout the
    session is retired; the owning daemon must close it before replacing it. Tactic trials reuse
    this wrapper and its absolute deadline with the same reader. -/
def runBounded (s : Session) (r : Request) (action : Deadline → IO Response) : IO Response := do
  let deadline := (← IO.monoMsNow) + r.timeoutMs
  let ch ← CloseableChannel.new
  discard <| IO.asTask (do
    let result ← try pure (.ok (toJson (← action deadline))) catch e => pure (.error e)
    discard <| ch.send result) Task.Priority.dedicated
  try
    IO.ofExcept (fromJson? (← awaitReply ch deadline))
  catch e =>
    let response := failure r s.root e
    let response := if response.status == "timeout" && r.operation == .goal && (← s.state.atomically get).phase == "elaborating" then {response with status := "still_elaborating"} else response
    if response.exitCode == 4 || (← s.transport.state.atomically get).dead then
      s.state.atomically <| modify fun st => {st with retired := true}
    return response
  finally ch.close
/-- The daemon serializes complete operations; this reader-independent wrapper bounds callers. -/
def inspect (s : Session) (r : Request) : IO Response :=
  s.runBounded r (observe s r)
end Session
end LspCli
