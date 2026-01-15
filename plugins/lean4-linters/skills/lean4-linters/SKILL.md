---
name: lean4-linters
description: Use when writing or maintaining Lean 4 linters. Covers register_option, syntax traversal, warnings vs errors, and project-wide enablement patterns.
---

# Lean 4 Linters

## When to use

- You want project-specific style or safety checks.
- You want fast feedback before runtime bugs (e.g., wrong types, slow paths).
- You need a consistent policy enforced across the codebase.

## Core pattern

```lean
import Lean

open Lean Elab Command

/-- Option to control the linter. -/
register_option linter.myRule : Bool := {
  defValue := true
  descr := "warn about X"
}

def myRuleEnabled : CommandElabM Bool :=
  return linter.myRule.get (← getOptions)

partial def findBad (stx : Syntax) : Array Syntax := Id.run do
  let mut r := #[]
  match stx with
  | .ident _ raw _ _ =>
      if raw.toString == "BadIdent" then r := r.push stx
  | .node _ _ args =>
      for a in args do r := r ++ findBad a
  | _ => pure ()
  return r

/-- Warning message. -/
def myRuleMsg : MessageData :=
  m!"avoid BadIdent; use GoodIdent"

/-- Linter run function. -/
def myRuleRun (stx : Syntax) : CommandElabM Unit := do
  unless ← myRuleEnabled do return
  for ident in findBad stx do
    logWarningAt ident myRuleMsg

/-- Linter registration. -/
def myRuleLinter : Linter := {
  run := myRuleRun
  name := `MyProject.Linter.myRule
}

initialize addLinter myRuleLinter
```

## Warnings vs errors

- Use `logWarningAt` for style or best-practice rules.
- Use `throwErrorAt` for correctness or safety rules.

## File-based exclusions

If a rule is too noisy for benchmarks or tests, skip by file path:

```lean
private def isBenchOrTest (fileName : String) : Bool :=
  fileName.contains "/Test/" ||
  fileName.contains "/Benchmark/" ||
  fileName.endsWith "Bench.lean"

if isBenchOrTest (← getFileName) then return
```

## Project-wide enablement

- Import linters in a common module (e.g., `Basic.lean`) so they run everywhere.
- Enable them in `lakefile.lean` using weak options:

```lean
leanOptions := #[
  ⟨`weak.linter.myRule, true⟩
]
```

Use `weak.` so builds do not fail when the option is absent.

## Local disable pattern

```lean
set_option linter.myRule false in
-- justify why the exception is needed
```

## Good linter messages

- Explain the why, not just the what.
- Provide a concrete fix snippet.
- Keep the message stable so users can search it.

## Linter test file

Create a small file that demonstrates the warning and how to disable it:

```
MyProject/Linter/MyRuleTest.lean
```

This helps prevent regressions when refactoring syntax traversal.

## Checklist

- Rule has a clear safety or style goal.
- False positives are minimized (or skipped by file path).
- Option exists and defaults to a sensible value.
- Error span is attached to the exact syntax node.

