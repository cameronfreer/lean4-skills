# Linter Authoring

> **Scope:** Not part of the prove/autoprove default loop. Consulted when writing or maintaining project-specific Lean 4 linters.

> **Version metadata:**
> - **Verified on:** Lean `v4.33.1` and `v4.35.0` (the Core Pattern compiled as a module and run on an importing module; enablement, local disable, severities and the `weak.` option checked in a Lake project)
> - **Last validated:** 2026-10-19
> - **Confidence:** high for the Core Pattern and the enablement/disable behaviour (run in CI: `tests/fixtures/reference_snippets/linter_rule.lean` + `linter_use.lean`); medium for the style guidance

## When to Use

- Project-specific style or safety checks
- Fast feedback before runtime bugs (slow paths, unsafe usage)
- Consistent policy enforcement across a codebase

## Composable Rule Blocks

Build linters from small parts you can reuse:

- `Option`: `register_option linter.myRule`
- `Finder`: `findBad : Syntax -> Array Syntax`
- `Filter`: file or namespace exclusions
- `Action`: `Linter.logLint` / `logWarningAt` vs `logErrorAt`
- `Registration`: `initialize addLinter ...`

Each rule should be a thin layer over these blocks.

## Core Pattern

```lean
import Lean

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
```

What each piece does:
- **The linter only runs in modules that import this one.** `initialize` registers it when the module is loaded, so put it in its own file and test it from another.
- **`withSetOptionIn` makes the [Local Disable Pattern](#local-disable-pattern) work.** A linter sees the whole command, `set_option … in` included; without the wrapper it reads the outer options and still fires inside `set_option linter.myRule false in`.
- **`Linter.getLinterValue` resolves the option.** It uses the option's explicit value; failing that, `linter.all` if set; otherwise the default (or an enabled linter set). Reading `linter.myRule.get (← getOptions)` directly ignores `linter.all`.
- **`Linter.logLint` emits the warning.** It tags the message as a linter warning and appends "This linter can be disabled with `set_option linter.myRule false`".

## Warnings vs Errors

- Use `Linter.logLint` (a warning) for style or best-practice rules.
- Use `logErrorAt` for correctness or safety rules: it reports every occurrence and fails the build. `throwErrorAt` also fails the build, but stops at the first occurrence and reports it as "linter … failed: …".

## File-Based Exclusions

If a rule is too noisy for benchmarks or tests, skip by file path:

```lean
def isBenchOrTest (fileName : String) : Bool :=
  fileName.contains "/Test/" ||
  fileName.contains "/Benchmark/" ||
  fileName.endsWith "Bench.lean"

-- in the run function:
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

Use `weak.` because a module that does not know the option (including the linter's own module, compiled before the option is registered) would otherwise fail with ``invalid -D parameter, unknown configuration option 'linter.myRule'``. The command-line equivalent is `lean -Dweak.linter.myRule=true`.

## Local Disable Pattern

```lean
set_option linter.myRule false in
-- justify why the exception is needed
def useBad2 : Nat := BadIdent
```

This is honoured only by linters whose run function is wrapped in `withSetOptionIn` (see [Core Pattern](#core-pattern)).

## Good Linter Messages

- Explain the why, not just the what
- Provide a concrete fix snippet
- Keep the message stable so users can search it

## Linter Test File

Create a small file that imports the linter, demonstrates the warning, and shows how to disable it. Pin the messages with `#guard_msgs`; it captures linter warnings:

```
MyProject/Linter/MyRuleTest.lean
```

This helps prevent regressions when refactoring syntax traversal.

## Checklist

- Rule has a clear safety or style goal
- Finder returns the smallest offending node
- False positives are minimized (or skipped by file path)
- Option exists and defaults to a sensible value
- Run function is wrapped in `withSetOptionIn`
- Error span is attached to the exact syntax node

## See Also

- [metaprogramming-patterns.md](metaprogramming-patterns.md) — MetaM/TacticM API for building linter logic
- [lean4-custom-syntax.md](lean4-custom-syntax.md) — syntax traversal primitives
