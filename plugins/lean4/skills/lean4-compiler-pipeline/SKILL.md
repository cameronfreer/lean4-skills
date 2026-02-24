---
name: lean4-compiler-pipeline
description: Use when debugging Lean 4 compiler pipeline behavior (LCNF/IR phases), enabling compiler traces/options, or installing custom `cpass` pass installers in compiler-development workflows.
---

# Lean4 Compiler Pipeline

Use this skill for compiler-internals debugging and controlled pipeline customization.

Grounding for this skill:
- `~/lean4/src/Lean/Compiler/LCNF/Main.lean`
- `~/lean4/src/Lean/Compiler/LCNF/PassManager.lean`
- `~/lean4/src/Lean/Compiler/LCNF/Passes.lean`
- `~/lean4/src/Lean/Compiler/LCNF/ConfigOptions.lean`
- `~/lean4/src/Lean/Compiler/IR.lean`
- `~/lean4/src/Lean/Compiler/Options.lean`

## Pipeline Mental Model

LCNF runs in phases:
- `base`
- `mono` (before and after lambda lifting)
- `impure`

Then IR runs passes in order:
- `init`
- `borrow`
- `boxing`
- `rc`
- optional `expand_reset_reuse`
- `push_proj`
- `result`

Use phase boundaries to localize regressions quickly.

## First Debug Pass

Enable targeted traces and checks before changing code:

```lean
set_option trace.Compiler true
set_option trace.Compiler.result true
set_option trace.compiler.ir.result true
set_option compiler.check true
set_option compiler.checkTypes true
```

If checking fails on heavily dependent code, treat that as a debugging signal and narrow scope before disabling checks.

## High-Value Compiler Options

From compiler options/config:
- `compiler.check` (step checks)
- `compiler.checkMeta` (meta/non-meta boundary checks)
- `compiler.checkTypes` (LCNF type-compat checks)
- `compiler.extract_closed` (closed-term extraction)
- `compiler.reuse` (reset/reuse insertion)
- `compiler.small`, `compiler.maxRecInline`, `compiler.maxRecInlineIfReduce`, `compiler.maxRecSpecialize`

Adjust one option at a time and compare traces.

## cpass Installation Rules

`cpass` declarations must satisfy:
- declaration type is `PassInstaller`
- attribute is global
- declaration is `meta`

Typical operations:
- `installBefore`
- `installAfter`
- `replacePass`
- `installAtEnd`
- `installBeforeEachOccurrence` / `installAfterEach`

Use pass `occurrence` explicitly when target pass appears multiple times.

## Safe Workflow for Pass Changes

1. Capture baseline trace with no pass changes.
2. Add one installer around one target pass occurrence.
3. Re-run with `compiler.check` + relevant trace classes.
4. Confirm phase invariants and pass ordering.
5. Only then expand installer scope.

For templates, trace map, and common failure signatures, read `references/pipeline-playbook.md`.
