# Lean Compiler Attribute Cases

## Source Anchors

- Attribute implementations:
  - `~/lean4/src/Lean/Compiler/ImplementedByAttr.lean`
  - `~/lean4/src/Lean/Compiler/CSimpAttr.lean`
  - `~/lean4/src/Lean/Compiler/InlineAttrs.lean`
  - `~/lean4/src/Lean/Compiler/NeverExtractAttr.lean`
- Useful tests and examples:
  - `~/lean4/tests/lean/implementedByIssue.lean`
  - `~/lean4/tests/lean/csimpAttr.lean`
  - `~/lean4/tests/lean/run/nativeReflBackdoor.lean`
  - `~/lean4/tests/lean/run/10213.lean`
  - `~/lean4/tests/compiler/StackOverflow.lean`
  - `~/lean4/tests/compiler/StackOverflowTask.lean`

## Failure Signatures to Recognize

### `@[implemented_by]`

- "number of universe parameters do not match"
- "types do not match"
- "Definition cannot be implemented by itself"

Interpretation: replacement target is not type-level identical to the wrapper.

### `@[csimp]`

- "invalid 'csimp' theorem, only constant replacement theorems (e.g., `@f = @g`) are currently supported."

Interpretation: theorem is not parameter-free constant replacement.

## Practical Review Checklist

1. Does this need unsafely trusted replacement (`implemented_by`) or can a proof-backed csimp theorem work?
2. Is the optimization local and benchmarked?
3. Are correctness-critical features protected from unsound replacement paths?
4. Are fallback tests present for both interpreted and compiled execution?

## Suggested Escalation Order

1. Algorithmic/data-structure optimization in ordinary Lean code
2. Inlining knobs (`inline` / `noinline` / `macro_inline`)
3. `@[csimp]` with proof
4. `@[implemented_by]` only if strictly necessary

## Notes on Unsoundness Risk

`@[implemented_by]` changes compiled behavior without kernel equivalence checks. Incorrect implementations can invalidate assumptions in native execution paths. Keep these annotations explicit, rare, and tested.
