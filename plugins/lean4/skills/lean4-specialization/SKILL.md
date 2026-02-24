---
name: lean4-specialization
description: Use when tuning or debugging Lean 4 compiler specialization (`@[specialize]`, `@[nospecialize]`, `compiler.maxRecSpecialize`, and specialization traces).
---

# Lean4 Compiler Specialization

Use this skill when deciding where specialization helps, or when specialization creates code-size or compile-time problems.

Grounding for this skill:
- `~/lean4/src/Lean/Compiler/Specialize.lean`
- `~/lean4/src/Lean/Compiler/LCNF/SpecInfo.lean`
- `~/lean4/src/Lean/Compiler/LCNF/Specialize.lean`
- `~/lean4/src/Lean/Compiler/LCNF/ConfigOptions.lean`
- `~/lean4/src/Lean/Compiler/LCNF/Passes.lean`
- `~/lean4/tests/lean/specializeAttr.lean`
- `~/lean4/tests/lean/run/spec_limit.lean`
- `~/lean4/tests/lean/run/specFixedHOParamModuloErased.lean`

## Mental Model

- `@[specialize]` marks declarations for specialization at call sites.
- `@[nospecialize]` blocks specialization for tagged declarations/types.
- In LCNF base passes, `implemented_by` replacement runs before `specialize`.
- Recursive specialization is bounded by `compiler.maxRecSpecialize`.

## Fast Diagnostics

Enable traces to see what the specializer decided:

```lean
set_option trace.Compiler.specialize.info true
set_option trace.Compiler.specialize.step true
set_option trace.Compiler.specialize.candidate true
```

Control recursion for debugging:

```lean
set_option compiler.maxRecSpecialize 64
```

## Attribute Usage Rules

- Start without attributes unless profiling or traces justify changes.
- Use `@[specialize]` for definitions taking higher-order or instance-heavy parameters.
- Narrow specialization with explicit parameter names/indices when full specialization is too broad.
- Use `@[nospecialize]` to stop explosion at declarations or type-class boundaries.

## Known Failure Signatures

- Invalid `@[specialize ...]` indices/names produce elaboration errors.
- Recursive blowups fail with: `Exceeded recursive specialization limit (...)`.
- If specialization does not trigger, inspect traces before adding more attributes.

## Practical Loop

1. Confirm hotspot or missed optimization.
2. Add minimal `@[specialize]` (optionally targeted args).
3. Rebuild and inspect `trace.Compiler.specialize.*` output.
4. If code growth/regressions appear, add `@[nospecialize]` or narrow args.
5. Re-measure and keep only attributes with clear wins.

For concrete patterns and triage details, read `references/specialization-playbook.md`.
