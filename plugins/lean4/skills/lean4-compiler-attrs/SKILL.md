---
name: lean4-compiler-attrs
description: Use when choosing or debugging Lean 4 compiler attributes like `@[implemented_by]`, `@[csimp]`, `@[inline]`, and `@[never_extract]`, especially for performance or unsafe replacement work.
---

# Lean4 Compiler Attributes

Use this skill when performance-driven compiler attributes are on the table. Pick the safest attribute that solves the problem, then validate with a small runtime check.

Grounding for this skill:
- `~/lean4/src/Lean/Compiler/ImplementedByAttr.lean`
- `~/lean4/src/Lean/Compiler/CSimpAttr.lean`
- `~/lean4/src/Lean/Compiler/InlineAttrs.lean`
- `~/lean4/src/Lean/Compiler/NeverExtractAttr.lean`
- Attribute behavior tests in `~/lean4/tests/lean/`

## Attribute Decision Table

- `@[csimp]`: preferred when you can prove `@f = @g` and want a compiler-only replacement.
- `@[implemented_by impl]`: use when you need an unsafe or non-definitional implementation and accept trust/unsoundness risk.
- `@[inline]` / `@[inline_if_reduce]` / `@[always_inline]` / `@[noinline]` / `@[macro_inline]`: use to tune inlining behavior.
- `@[never_extract]`: use when closed-term extraction or CSE would remove intended repeated effects.

## `@[implemented_by]` Workflow

1. Keep public wrapper stable (`def` or `opaque`).
2. Implement alternate function (`unsafe` if needed).
3. Ensure exact type and universe-parameter match.
4. Add `@[implemented_by impl]` to wrapper.
5. Add runtime checks for wrapper behavior in intended call paths.

Constraints:
- implementation cannot be the declaration itself
- type and universe mismatch is rejected
- compiler-related attrs on the original declaration are ignored once replaced

## `@[csimp]` Workflow

Use when you can prove constant replacement:

```lean
@[csimp] theorem f_eq_g : @f = @g := by
  -- proof
```

Constraints:
- theorem has no parameters
- statement shape must be constant replacement (`@f = @g`)
- scoped/local registration can be useful for experimentation before globalizing

## Inlining Workflow

- Start with default behavior.
- Add `@[inline]` only after finding measurable hot call sites.
- Use `@[macro_inline]` only on non-recursive exposed defs.
- Use `@[noinline]` to stop code-size or compile-time blowups.
- Re-check generated behavior with focused tests rather than broad assumptions.

## `@[never_extract]` Workflow

Use for declarations where extracted closed terms or CSE would suppress intended repeated behavior. Keep usage narrow and document why extraction must be disabled.

## Safety Policy

- Prefer `@[csimp]` over `@[implemented_by]` when a proof-backed rewrite is possible.
- Treat `@[implemented_by]` as trusted code boundary; do not use casually in proof-critical paths.
- When in doubt, keep the optimization local and add tests before widening scope.

For concrete examples and failure signatures, read `references/attribute-cases.md`.
