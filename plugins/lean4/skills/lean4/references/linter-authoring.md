# Linter Authoring

> **Scope:** Not part of the prove/autoprove default loop. Consulted when writing or maintaining project-specific Lean 4 linters.

> **Version metadata:**
> - **Verified on:** Lean reference + release notes through `v4.27.0`
> - **Last validated:** 2026-02-17
> - **Confidence:** medium (docs reviewed; snippets not batch-compiled)

## When to Use

- Project-specific style or safety checks
- Fast feedback before runtime bugs (slow paths, unsafe usage)
- Consistent policy enforcement across a codebase

## Composable Rule Blocks

Build linters from small parts you can reuse:

- `Option`: `register_option linter.myRule`
- `Finder`: `findBad : Syntax -> Array Syntax`
- `Filter`: file or namespace exclusions
- `Action`: `logWarningAt` vs `throwErrorAt`
- `Registration`: `initialize addLinter ...`

Each rule should be a thin layer over these blocks.

## Core Pattern

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

## Warnings vs Errors

- Use `logWarningAt` for style or best-practice rules
- Use `throwErrorAt` for correctness or safety rules

## File-Based Exclusions

If a rule is too noisy for benchmarks or tests, skip by file path:

```lean
private def isBenchOrTest (fileName : String) : Bool :=
  fileName.contains "/Test/" ||
  fileName.contains "/Benchmark/" ||
  fileName.endsWith "Bench.lean"

if isBenchOrTest (← getFileName) then return
```

## Project-Wide Enablement

- Import linters in a common module (e.g., `Basic.lean`) so they run everywhere
- Enable them in `lakefile.lean` using weak options:

```lean
leanOptions := #[
  ⟨`weak.linter.myRule, true⟩
]
```

Use `weak.` so builds do not fail when the option is absent.

## Local Disable Pattern

```lean
set_option linter.myRule false in
-- justify why the exception is needed
```

## Good Linter Messages

- Explain the why, not just the what
- Provide a concrete fix snippet
- Keep the message stable so users can search it

## Linter Test File

Create a small file that demonstrates the warning and how to disable it:

```
MyProject/Linter/MyRuleTest.lean
```

This helps prevent regressions when refactoring syntax traversal.

## Checklist

- Rule has a clear safety or style goal
- Finder returns the smallest offending node
- False positives are minimized (or skipped by file path)
- Option exists and defaults to a sensible value
- Error span is attached to the exact syntax node

## See Also

- [metaprogramming-patterns.md](metaprogramming-patterns.md) — MetaM/TacticM API for building linter logic
- [lean4-custom-syntax.md](lean4-custom-syntax.md) — syntax traversal primitives
