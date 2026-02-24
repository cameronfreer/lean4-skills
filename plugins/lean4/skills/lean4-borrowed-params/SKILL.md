---
name: lean4-borrowed-params
description: Use when designing or debugging Lean 4 `@&` borrowed parameters for extern/exported functions, ABI correctness, and reference-count behavior.
---

# Lean4 Borrowed Parameters

Use this skill when `@&` annotations and ownership behavior are involved in native interop or low-level performance work.

Grounding for this skill:
- `~/lean4/src/Lean/Parser/Term.lean`
- `~/lean4/src/Lean/Elab/BuiltinNotation.lean`
- `~/lean4/src/Lean/Compiler/BorrowedAnnotation.lean`
- `~/lean4/src/Lean/Compiler/IR/AddExtern.lean`
- `~/lean4/src/Lean/Compiler/IR/Borrow.lean`
- `~/lean4/tests/compiler/foreign/Main/S.lean`
- `~/lean4/tests/pkg/test_extern/TestExtern/BadExtern.lean`

## Mental Model

- `@&` is parsed/elaborated as a `borrowed` annotation on the parameter type.
- This annotation affects ABI/runtime behavior, not Lean's logical type meaning.
- In extern lowering, borrowed flags are carried into IR params (`Param.borrow`).
- Borrow inference for ordinary IR declarations is heuristic and intentionally constrained for exported functions.

## High-Signal Rules

- Use `@&` for read-only object parameters crossing FFI boundaries.
- Keep extern Lean signature and foreign prototype ownership conventions aligned.
- Do not assume borrow inference will fix exported ABI boundaries.
- If ownership is ambiguous, prefer explicitness and measure before broad rollout.

## Fast Triage

1. Confirm `@&` is present on intended params.
2. Confirm function is actually `@[extern ...]`/native boundary relevant.
3. Check whether declaration is exported (borrow inference policy differs).
4. Validate call paths that reuse the value after call.
5. Re-test for double-free/use-after-free symptoms.

## Common Failure Modes

- Missing `@&` on read-only extern args increases RC churn.
- Incorrect ownership assumption in foreign code can produce memory errors.
- Relying on inferred borrowing for exported wrappers can cause mismatch with wrapper expectations.

## Practical Loop

1. Add or narrow `@&` only on boundary parameters with clear read-only intent.
2. Rebuild and run focused runtime tests.
3. Inspect emitted behavior/IR when needed.
4. Keep changes minimal unless measurements justify expansion.

For concrete examples and diagnostics, read `references/borrowed-playbook.md`.
