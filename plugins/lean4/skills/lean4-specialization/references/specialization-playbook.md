# Lean Compiler Specialization Playbook

## Source Anchors

- Specialization attributes and argument parsing:
  - `~/lean4/src/Lean/Compiler/Specialize.lean`
- Parameter classification and candidate computation:
  - `~/lean4/src/Lean/Compiler/LCNF/SpecInfo.lean`
- Specialization pass behavior and trace classes:
  - `~/lean4/src/Lean/Compiler/LCNF/Specialize.lean`
- Limits and options:
  - `~/lean4/src/Lean/Compiler/LCNF/ConfigOptions.lean`
- Pass ordering (`implementedBy` before `specialize`):
  - `~/lean4/src/Lean/Compiler/LCNF/Passes.lean`

## What Gets Specialized

The LCNF specializer classifies params as:
- `fixedInst` (instance-like)
- `fixedHO` (higher-order function-like)
- `fixedNeutral` (computationally neutral with forward deps)
- `user` (explicitly requested via `@[specialize ...]`)
- `other` (not specialized)

Useful implications:
- `@[specialize]` without args requests default fixedHO/fixedInst behavior.
- `@[specialize f g]` or `@[specialize 1 3]` marks explicit `user` parameters.
- `@[nospecialize]` can suppress specialization pressure at declaration/type boundaries.

## Trace-Driven Workflow

Use these options while iterating:

```lean
set_option trace.Compiler.specialize.info true
set_option trace.Compiler.specialize.step true
set_option trace.Compiler.specialize.candidate true
```

Read output in this order:
1. `info` to see final per-declaration parameter masks.
2. `candidate` to see candidate calls and generated keys.
3. `step` to see cache hits/new specialized decls/termination rounds.

## Recursion Limit and Blowup Control

The pass loops over newly generated declarations and aborts when rounds exceed `compiler.maxRecSpecialize`.

Debug by temporarily lowering the limit:

```lean
set_option compiler.maxRecSpecialize 8
```

If you hit the limit:
- narrow `@[specialize ...]` args
- add `@[nospecialize]` to blocking types/declarations
- remove specialization where traces show no useful ground/HO argument progress

## Common Errors

From `Specialize.elabSpecArgs`:
- index `0` is invalid (indices are 1-based)
- out-of-range indices are rejected
- duplicated argument names/indices are rejected
- unknown argument names are rejected

Compiler runtime failure:
- `Exceeded recursive specialization limit (...)` from LCNF specializer loop.

## Field Patterns Worth Copying

- Use `@[specialize]` on recursive helpers with function parameters to avoid closure overhead when call sites are concrete.
- Use `@[nospecialize]` for heavily reused polymorphic APIs or classes (for example `Inhabited`) when specialization fan-out hurts compile/runtime tradeoffs.
- Keep changes minimal and localized; verify with traces plus focused benchmark/test coverage.
