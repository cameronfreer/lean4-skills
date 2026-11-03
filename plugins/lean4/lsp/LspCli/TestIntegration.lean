import LspCli.Daemon
open Lean System LspCli
namespace Integration
private def check (label : String) (b : Bool) : IO Unit := do
  unless b do throw <| IO.userError s!"FAIL: {label}"
  IO.println s!"PASS: {(label.splitOn ":").head!}"
private def decode (out : IO.Process.Output) : IO Response :=
  IO.ofExcept ((Json.parse out.stdout.trimAscii.copy).bind fromJson?)

/-- Linux test-only process observation; excludes already exited zombies. -/
def workers (root : FilePath) : IO (Array (FilePath × String)) := do
  let mut result := #[]
  for entry in ← (FilePath.mk "/proc").readDir do
    if entry.fileName.toNat?.isNone then continue
    try
      let cmd ← IO.FS.readFile (entry.path / "cmdline")
      if (cmd.splitOn "--worker").length > 1 && (cmd.splitOn (System.Uri.pathToUri root)).length > 1 then
        result := result.push (entry.path, (← IO.FS.realPath (entry.path / "exe")).toString)
    catch _ => pure ()
  return result

private partial def awaitNoWorkers (root : FilePath) (deadline : Nat) : IO Bool := do
  if (← workers root).isEmpty then return true
  if (← IO.monoMsNow) ≥ deadline then return false
  IO.sleep 30
  awaitNoWorkers root deadline

def run (toolchain : String) : IO Unit := do
  let temporary ← IO.FS.createTempDir
  let root := temporary / "project λ with spaces"
  IO.FS.createDir root
  IO.FS.writeFile (root / "lean-toolchain") toolchain
  IO.FS.writeFile (root / "lakefile.toml") "name = 'fixture'\n[[lean_lib]]\nname = 'A'\n"
  IO.FS.writeFile (root / "Example.lean") "theorem sample (n : Nat) : n = n := by\n  sorry\n"
  let exe := (← IO.currentDir) / ".lake/build/bin/lean4-skills-lsp"
  let invoke := fun (args : Array String) => IO.Process.output {cmd := exe.toString, args := args ++ #["--project", root.toString, "--json", "--timeout-ms", "20000"]}
  try
    let first ← IO.asTask (invoke #["goal", "Example.lean", "--line", "2", "--column", "3"]) Task.Priority.dedicated
    let second ← invoke #["goal", "Example.lean", "--line", "2", "--column", "3"]
    let out ← IO.ofExcept first.get
    let response ← decode out
    let other ← decode second
    check s!"persistent real goal {out.stdout}" (out.exitCode == 0 && response.status == "goals_present")
    check "concurrent launch converges" (response.sourceIdentity == other.sourceIdentity)
    let live ← workers root
    check "one real worker" (live.size == 1)
    let version := (toolchain.splitOn ":v").getLast!
    check s!"actual server toolchain {version}: {live}" (live.all fun p => (p.2.splitOn s!"v{version}").length > 1)
    let doctor ← invoke #["doctor"]
    check "doctor uses target project launch" (doctor.exitCode == 0)
    let initial ← decode (← invoke #["status"])
    let pid ← IO.ofExcept (initial.data.getObjValAs? Nat "serverPid")
    let session ← IO.ofExcept (initial.data.getObjValAs? String "sessionIdentity")
    for _ in [:20] do
      let warm ← decode (← invoke #["goal", "Example.lean", "--line", "2", "--column", "3"])
      check "warm source identity retained" (warm.sourceIdentity == response.sourceIdentity)
    let warm ← decode (← invoke #["status"])
    check "twenty warm requests retain server" ((warm.data.getObjValAs? Nat "serverPid").toOption == some pid)
    let line ← decode (← invoke #["goal", "Example.lean", "--line", "2"])
    check "omitted column observes both sides" ((line.data.getObjVal? "before").isOk && (line.data.getObjVal? "after").isOk)
    let outside ← decode (← invoke #["goal", "Example.lean", "--line", "1", "--column", "1"])
    check "null goals distinct" (outside.status == "no_goal_at_position" && outside.data == Json.null)
    IO.FS.writeFile (root / "Example.lean") "theorem sample (n : Nat) : n = n := by\n  rfl\n"
    let stale ← invoke #["goal", "Example.lean", "--line", "2", "--column", "6", "--expect-source", response.sourceIdentity.getD ""]
    check "stale source rejected" (stale.exitCode == 4 && (← decode stale).status == "stale_input")
    let closed ← decode (← invoke #["goal", "Example.lean", "--line", "2", "--column", "6"])
    check s!"fresh disk edit closes local goals: {closed.status}" (closed.status == "closed_local_goals" && closed.documentVersion == some 2)
    let ds ← decode (← invoke #["diagnostics", "Example.lean"])
    check "clean diagnostics after edit" (ds.ok && ds.data == toJson (#[] : Array Json))
    IO.FS.writeFile (root / "Example.lean") "def unicode : Nat := 1\ndef use : Nat := /- 😀 -/ unicode\n"
    let hover ← decode (← invoke #["hover", "Example.lean", "--line", "2", "--column", "27"])
    check s!"unicode hover: {(toJson hover).compress}" (hover.ok && hover.data != Json.null)
    let definition ← decode (← invoke #["definition", "Example.lean", "--line", "2", "--column", "27"])
    check "definition returns public ranges" (definition.ok && (definition.data.getArr?).toOption.any (fun a => !a.isEmpty && ((a[0]!.getObjVal? "targetSelectionRange").bind (·.getObjVal? "start") |>.bind (·.getObjValAs? Nat "line")).toOption == some 1))
    let refs ← decode (← invoke #["references", "Example.lean", "--line", "1", "--column", "6"])
    check "references loaded index" (refs.ok && (refs.data.getArr?).toOption.any (·.size ≥ 2))
    let search ← decode (← invoke #["search", "unicode"])
    check s!"local symbol search: {(toJson search).compress}" (search.ok && (search.data.getObjValAs? Bool "complete").toOption == some true && (search.data.getObjValAs? (Array Json) "symbols").toOption.any (!·.isEmpty))
    IO.FS.writeFile (root / "Example.lean") "example : True := by\n  simp?\n"
    let actions ← decode (← invoke #["code-actions", "Example.lean", "--line", "2"])
    check s!"resolved code actions: {(toJson actions).compress}" (actions.ok && (actions.data.getArr?).toOption.any (fun a => a.any (fun x => (x.getObjVal? "edit").isOk)))
    check "code actions leave source untouched" ((← IO.FS.readFile (root / "Example.lean")) == "example : True := by\n  simp?\n")
    IO.FS.writeFile (root / "Example.lean") "example : False := by\n  exact True.intro\n"
    let errors ← invoke #["diagnostics", "Example.lean"]
    check "real Lean errors exit one" (errors.exitCode == 1)
    -- Authenticate and validate the descriptor/handshake independently of the CLI parser.
    let dir ← Daemon.cacheDir root
    let d : Daemon.Descriptor ← IO.ofExcept ((Json.parse (← IO.FS.readFile (dir / "session.json"))).bind fromJson?)
    let envelope : Daemon.Envelope := {root := root.toString, token := "wrong", identity := d.identity, deadline := (← IO.monoMsNow) + 2000, request := {operation := .status, project := some root}}
    let rejection ← Socket.bounded (do
      let c ← Std.Async.TCP.Socket.Client.mk
      c.connect (.v4 {addr := {octets := #v[127,0,0,1]}, port := d.port.toUInt16})
      Socket.sendJson c (toJson envelope)
      let result ← Socket.readJson c envelope.deadline
      c.shutdown
      pure result) envelope.deadline
    check "authentication rejects incorrect token" ((rejection.getObjValAs? Bool "ok").toOption == some false && !(rejection.compress.splitOn d.token).length > 1)
    IO.FS.writeFile (root / "Example.lean") "#eval IO.sleep 800\n"
    let slow ← IO.asTask (invoke #["diagnostics", "Example.lean"]) Task.Priority.dedicated
    IO.sleep 100
    let queueStarted ← IO.monoMsNow
    let queued ← IO.Process.output {cmd := exe.toString, args := #["status", "--project", root.toString, "--json", "--timeout-ms", "50"]}
    check "queue wait counts against caller deadline" (queued.exitCode == 4 && (← IO.monoMsNow) - queueStarted < 500)
    check "queued timeout does not corrupt active response" ((← IO.ofExcept slow.get).exitCode == 0)
    try
      IO.FS.writeFile (dir / "session.json") (toJson {d with root := "/wrong-project"}).compress
      let mismatched ← IO.Process.output {cmd := exe.toString, args := #["status", "--project", root.toString, "--json", "--timeout-ms", "100"]}
      check s!"descriptor root mismatch rejected as protocol error: {mismatched.stdout}" (mismatched.exitCode == 3)
    finally IO.FS.writeFile (dir / "session.json") (toJson d).compress
    IO.FS.writeFile (root / "lakefile.toml") "name = 'fixture'\n[[lean_lib]]\nname = 'A'\n# configuration changed\n"
    let invalidated ← invoke #["status"]
    check "config change invalidates session" (invalidated.exitCode == 4)
    IO.sleep 100
    discard <| invoke #["diagnostics", "Example.lean"]
    let restarted ← decode (← invoke #["status"])
    check "replacement identity never reused" ((restarted.data.getObjValAs? String "sessionIdentity").toOption != some session)
    discard <| invoke #["stop"]
    check "stop cleans real workers" (← awaitNoWorkers root ((← IO.monoMsNow) + 3000))
    -- Dependency edits are never silently reported as fresh; rebuilt .ileans update symbols.
    IO.FS.writeFile (root / "A.lean") "def importedValue : Nat := 1\n"
    IO.FS.writeFile (root / "B.lean") "import A\nexample : importedValue = 1 := by rfl\n"
    let build := IO.Process.output {cmd := ← ProjectProcess.lake, args := #["build", "A"], cwd := some root, env := ProjectProcess.environment}
    let built ← build
    check s!"dependency fixture builds: {built.stdout} {built.stderr}" (built.exitCode == 0)
    let original ← decode (← invoke #["diagnostics", "B.lean"])
    check "built dependency starts clean" original.ok
    IO.FS.writeFile (root / "A.lean") "def importedValue : Nat := 2\ndef importedNew : Nat := 3\n"
    let staleDependency ← decode (← invoke #["diagnostics", "B.lean"])
    check s!"import edit is explicit stale_dependency: {(toJson staleDependency).compress}" (staleDependency.status == "stale_dependency" && staleDependency.exitCode == 4)
    check "dependency rebuild succeeds" ((← build).exitCode == 0)
    let imported ← decode (← invoke #["search", "importedNew"])
    check "rebuilt ilean reaches symbol index" (imported.ok && (imported.data.getObjValAs? (Array Json) "symbols").toOption.any (!·.isEmpty))
    discard <| invoke #["stop"]
    let freshDependent ← invoke #["diagnostics", "B.lean"]
    check "reopened dependent observes rebuilt semantics" (freshDependent.exitCode == 1 && (← decode freshDependent).status != "stale_dependency")
    discard <| invoke #["stop"]
    let idle ← IO.Process.spawn {cmd := exe.toString, args := #["--daemon", root.toString, "--idle-ms", "100"], stdin := .null, stdout := .null, stderr := .null}
    let idleStart ← IO.monoMsNow
    repeat
      if (← idle.tryWait).isSome then break
      unless (← IO.monoMsNow) - idleStart < 5000 do
        idle.kill
        check "idle daemon exits bounded" false
      IO.sleep 50
    check "idle expiry removes own descriptor, retains lock inode" (!(← (dir / "session.json").pathExists) && (← (dir / "owner.lock").pathExists))
    let daemon ← IO.Process.spawn {cmd := exe.toString, args := #["--daemon", root.toString], stdin := .null, stdout := .null, stderr := .null, setsid := true}
    let started ← IO.monoMsNow
    repeat
      if ← (dir / "session.json").pathExists then break
      unless (← IO.monoMsNow) - started < 5000 do
        daemon.kill
        check "owned daemon publishes descriptor" false
      IO.sleep 10
    discard <| invoke #["diagnostics", "Example.lean"]
    let beforeCrash ← decode (← invoke #["status"])
    daemon.kill
    discard <| daemon.wait
    check "daemon crash cleans server workers through EOF" (← awaitNoWorkers root ((← IO.monoMsNow) + 3000))
    discard <| invoke #["diagnostics", "Example.lean"]
    let afterCrash ← decode (← invoke #["status"])
    check "stale descriptor recovered after daemon crash" ((beforeCrash.data.getObjValAs? String "sessionIdentity").toOption != (afterCrash.data.getObjValAs? String "sessionIdentity").toOption && afterCrash.ok)
    discard <| invoke #["stop"]
    -- Native owned-process crash: detached workers must exit when watchdog pipes close.
    let owned ← Session.start root
    let d ← owned.openDocument (root / "Example.lean") (← IO.FS.readFile (root / "Example.lean"))
    discard <| owned.waitDocument d ((← IO.monoMsNow) + 10000)
    check "crash fixture starts worker" (!(← workers root).isEmpty)
    owned.transport.child.kill
    check "owned watchdog crash cleans workers through EOF" (← awaitNoWorkers root ((← IO.monoMsNow) + 3000))
    owned.close
    IO.println s!"integration {toolchain} passed"
  finally
    discard <| invoke #["stop"]
    IO.FS.removeDirAll temporary
end Integration

namespace Integration

def mathlib (root : FilePath) : IO Unit := do
  let exe := (← IO.currentDir) / ".lake/build/bin/lean4-skills-lsp"
  let invoke := fun (args : Array String) => IO.Process.output {cmd := exe.toString, args := args ++ #["--project", root.toString, "--json", "--timeout-ms", "30000"]}
  try
    let started ← IO.monoMsNow
    let first ← decode (← invoke #["goal", "MathlibFixture.lean", "--line", "11", "--column", "3"])
    let coldMs := (← IO.monoMsNow) - started
    check s!"real Mathlib goal: {(toJson first).compress}" (first.ok && first.status == "goals_present")
    let started ← IO.monoMsNow
    let warm ← decode (← invoke #["goal", "MathlibFixture.lean", "--line", "11", "--column", "3"])
    let warmMs := (← IO.monoMsNow) - started
    check "Mathlib warm identity retained" (first.sourceIdentity == warm.sourceIdentity)
    let status ← decode (← invoke #["status"])
    let scanMs ← IO.ofExcept (status.data.getObjValAs? Nat "scanDurationMs")
    IO.println s!"Mathlib measurements: cold={coldMs}ms warm={warmMs}ms registered-tree scan={scanMs}ms"
  finally
    discard <| invoke #["stop"]
    check "Mathlib stop leaves no workers" (← awaitNoWorkers root ((← IO.monoMsNow) + 3000))
end Integration
