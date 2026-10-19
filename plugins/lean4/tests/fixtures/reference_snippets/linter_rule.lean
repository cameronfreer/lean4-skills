import Lean

/-!
Core-Lean evidence for `references/linter-authoring.md` (#181): the § Core
Pattern linter, verbatim. `run_core_snippets.sh` copies this file to
`LinterRule.lean` in a scratch directory, compiles it to an `.olean`, and
elaborates `linter_use.lean` (as `LinterUse.lean`) against it with
`-Dweak.linter.myRule=true` — a linter only runs in modules that import it.
-/

open Lean Elab Command

/-- Option to control the linter. -/
register_option linter.myRule : Bool := {
  defValue := false
  descr := "warn about BadIdent"
}

partial def findBad (stx : Syntax) : Array Syntax := Id.run do
  let mut r := #[]
  match stx with
  | .ident _ raw _ _ =>
      if raw.toString == "BadIdent" then r := r.push stx
  | .node _ _ args =>
      for a in args do r := r ++ findBad a
  | _ => pure ()
  return r

/-- Linter run function. -/
def myRuleRun : CommandElab := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.myRule (← Linter.getLinterOptions) do return
  for ident in findBad stx do
    Linter.logLint linter.myRule ident m!"avoid BadIdent; use GoodIdent"

/-- Linter registration. -/
def myRuleLinter : Linter := {
  run := myRuleRun
  name := `MyProject.Linter.myRule
}

initialize addLinter myRuleLinter

-- § File-Based Exclusions helper.
def isBenchOrTest (fileName : String) : Bool :=
  fileName.contains "/Test/" ||
  fileName.contains "/Benchmark/" ||
  fileName.endsWith "Bench.lean"

#guard isBenchOrTest "src/Test/A.lean" && isBenchOrTest "XBench.lean"
#guard !isBenchOrTest "src/Main.lean"

-- ... used in a run function.
def myRuleRunExcluding : CommandElab := fun stx => do
  if isBenchOrTest (← getFileName) then return
  myRuleRun stx
