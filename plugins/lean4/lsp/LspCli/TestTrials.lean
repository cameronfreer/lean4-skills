import LspCli.Daemon
open Lean System LspCli
namespace TrialTests
private def check (label : String) (b : Bool) : IO Unit := do
  unless b do throw <| IO.userError s!"FAIL: {label}"
  IO.println s!"PASS: {label}"
private def decode (out : IO.Process.Output) : IO Response :=
  IO.ofExcept ((Json.parse out.stdout.trimAscii.copy).bind fromJson?)
private def results (r : Response) : Array Json := (r.data.getObjValAs? (Array Json) "candidates").toOption.getD #[]
private def status (j : Json) : String := (j.getObjValAs? String "status").toOption.getD ""

def run (mathlib? : Option FilePath := none) : IO Unit := do
  if let some mathlib := mathlib? then
    unless ← (mathlib / "MathlibFixture.lean").pathExists do
      throw <| IO.userError s!"missing Mathlib trial fixture: {mathlib / "MathlibFixture.lean"}"
  let root ← IO.FS.createTempDir
  IO.FS.writeFile (root / "lean-toolchain") "leanprover/lean4:v4.35.0"
  IO.FS.writeFile (root / "lakefile.toml") "name = 'trials'\n"
  let source := "namespace Example\nset_option autoImplicit false\nexample (n : Nat) : n = n := by\n  sorry\nend Example\n"
  IO.FS.writeFile (root / "Example.lean") source
  IO.FS.writeFile (root / "snippets.json") (toJson (#["rfl", "skip", "exact True.intro", "sorry", "first\n  | rfl\n", "exact n"] : Array String)).compress
  let exe := (← IO.currentDir) / ".lake/build/bin/lean4-skills-lsp"
  let invoke := fun (args : Array String) => IO.Process.output {cmd := exe.toString, args := args ++ #["--project", root.toString, "--json", "--timeout-ms", "30000"]}
  let attempt := fun (extra : Array String) => invoke (#["attempt", "Example.lean", "--range", "4:3-4:8", "--snippets-file", "snippets.json"] ++ extra)
  try
    let original ← decode (← invoke #["goal", "Example.lean", "--line", "4", "--column", "3"])
    let out ← attempt #[]
    let response ← decode out
    let rs := results response
    check "independent batch results" (out.exitCode == 1 && rs.size == 6)
    check "rfl closes local goals" (status rs[0]! == "closed_local_goals")
    check "skip leaves goals" (status rs[1]! == "goals_present")
    check "type error reported" ((rs[2]!.getObjValAs? (Array Json) "diagnostics").toOption.any (·.any fun d => (d.getObjValAs? Nat "severity").toOption == some 1))
    check "placeholder warning reported" ((rs[3]!.getObjValAs? (Array Json) "diagnostics").toOption.any (·.any fun d => (d.getObjValAs? Nat "severity").toOption == some 2))
    check "multiline trailing newline with local context" (status rs[4]! == "closed_local_goals")
    check "physical bytes unchanged" ((← IO.FS.readFile (root / "Example.lean")) == source)
    check "outer identity is live identity" (response.sourceIdentity == original.sourceIdentity && response.documentVersion == original.documentVersion)
    let after ← decode (← invoke #["goal", "Example.lean", "--line", "4", "--column", "3"])
    check "next query retains live goal and identity" (after.sourceIdentity == original.sourceIdentity && after.status == "goals_present")
    let stale ← attempt #["--expect-source", "obsolete"]
    check "stale identity rejected" (stale.exitCode == 4 && (← decode stale).status == "stale_input")
    IO.FS.writeFile (root / "snippets.json") "[\"sorry\"]"
    let placeholder ← decode (← attempt #[])
    check "warning alone has successful batch exit" (placeholder.ok && placeholder.exitCode == 0 && status (results placeholder)[0]! == "closed_local_goals" && ((results placeholder)[0]!.getObjValAs? (Array Json) "diagnostics").toOption.any (!·.isEmpty))
    IO.FS.writeFile (root / "snippets.json") "[]"
    let empty ← attempt #[]
    check "empty candidates rejected" (empty.exitCode == 2)
    IO.FS.writeFile (root / "snippets.json") "[1]"
    let invalid ← attempt #[]
    check "non-string candidates rejected" (invalid.exitCode == 2)
    IO.FS.writeFile (root / "snippets.json") "[\"rfl\"]"
    let badRange ← invoke #["attempt", "Example.lean", "--range", "4:3-9:1", "--snippets-file", "snippets.json"]
    check "out of range rejected" (badRange.exitCode == 2)
    let outside ← invoke #["attempt", "Example.lean", "--range", "1:1-1:1", "--snippets-file", "snippets.json"]
    let outsideR ← decode outside
    check "null goal stays distinct" ((results outsideR)[0]?.any (fun x => status x == "no_goal_at_position" && (x.getObjVal? "goal").toOption == some Json.null))
    IO.FS.writeFile (root / "Example.lean") (source ++ "def broken : Nat := True.intro\n")
    let errors ← decode (← attempt #[])
    check "preexisting errors retained" (errors.exitCode == 1 && (results errors)[0]?.any (fun x => (x.getObjValAs? (Array Json) "diagnostics").toOption.any (·.any fun d => (d.getObjValAs? Nat "severity").toOption == some 1)))
    check "error trial preserves source" ((← IO.FS.readFile (root / "Example.lean")) == source ++ "def broken : Nat := True.intro\n")
    IO.FS.writeFile (root / "Example.lean") source
    for _ in [:4] do
      let repeatResult ← decode (← attempt #[])
      check "repeated trials preserve live snapshot" (repeatResult.sourceIdentity.isSome && (results repeatResult).size == 1 && (← IO.FS.readFile (root / "Example.lean")) == source)
    IO.FS.writeFile (root / "snippets.json") "[\"run_tac Lean.Core.throwError \\\"fail\\\"\"]"
    -- A short global deadline also covers scanning and elaboration.
    let timed ← IO.Process.output {cmd := exe.toString, args := #["attempt", "Example.lean", "--range", "4:3-4:8", "--snippets-file", "snippets.json", "--project", root.toString, "--json", "--timeout-ms", "1"]}
    check "global deadline returns timeout" (timed.exitCode == 4)
    let recovered ← decode (← invoke #["goal", "Example.lean", "--line", "4", "--column", "3"])
    check "next query recovers after cancellation" (recovered.status == "goals_present" && (← IO.FS.readFile (root / "Example.lean")) == source)
    discard <| invoke #["stop"]
    IO.FS.writeFile (root / "snippets.json") "[\"rfl\"]"
    let session ← Session.start root
    try
      for _ in [:4] do
        let trial ← Trials.run session {operation := .attempt, file := some "Example.lean", range := some ⟨⟨4,3⟩,⟨4,8⟩⟩, snippetsFile := some "snippets.json"}
        let documents := (← session.state.atomically get).documents
        check "scratch closes and live document retained" (trial.ok && documents.size == 1 && documents.all (!·.virtual))
      IO.FS.writeFile (root / "Example.lean") ("import Lean\n" ++ source)
      let warm ← session.inspect {operation := .diagnostics, file := some "Example.lean"}
      check "timeout fixture elaborated" warm.ok
      IO.FS.writeFile (root / "snippets.json") (toJson (#["run_tac do\n  liftIO <| IO.sleep 5000"] : Array String)).compress
      let pending ← IO.asTask (Trials.run session {operation := .attempt, file := some "Example.lean", range := some ⟨⟨5,3⟩,⟨5,8⟩⟩, snippetsFile := some "snippets.json", timeoutMs := 1500}) Task.Priority.dedicated
      IO.sleep 500
      let during := (← session.state.atomically get).documents
      check "active trial uses at most two document slots" (during.size ≤ 2 && during.any (·.virtual))
      let timedResult ← IO.ofExcept pending.get
      check s!"active trial deadline retires session: {(toJson timedResult).compress}" (timedResult.exitCode == 4 && (← session.state.atomically get).retired)
    finally session.close
    check "retirement closes scratch and live slots" ((← session.state.atomically get).documents.isEmpty)
    let restarted ← decode (← invoke #["goal", "Example.lean", "--line", "5", "--column", "3"])
    check "normal goal works after active cancellation" (restarted.status == "goals_present" && (← IO.FS.readFile (root / "Example.lean")) == "import Lean\n" ++ source)
    if let some mathlib := mathlib? then
      let before ← IO.FS.readFile (mathlib / "MathlibFixture.lean")
      IO.FS.writeFile (root / "mathlib.json") (toJson (#["exact Nat.add_comm a b", "rfl", "sorry"] : Array String)).compress
      let math := fun (args : Array String) => IO.Process.output {cmd := exe.toString, args := args ++ #["--project", mathlib.toString, "--json", "--timeout-ms", "30000"]}
      try
        let result ← decode (← math #["attempt", "MathlibFixture.lean", "--range", "11:3-11:8", "--snippets-file", (root / "mathlib.json").toString])
        let xs := results result
        check s!"Mathlib candidates preserve observations: {(toJson result).compress}" (xs.size == 3 && status xs[0]! == "closed_local_goals" && result.exitCode == 1)
        check "Mathlib source unchanged" ((← IO.FS.readFile (mathlib / "MathlibFixture.lean")) == before)
        let goal ← decode (← math #["goal", "MathlibFixture.lean", "--line", "11", "--column", "3"])
        check "Mathlib live goal survives" (goal.status == "goals_present" && goal.sourceIdentity == result.sourceIdentity)
      finally discard <| math #["stop"]
    IO.println "trial tests passed"
  finally
    discard <| invoke #["stop"]
    IO.FS.removeDirAll root
end TrialTests
