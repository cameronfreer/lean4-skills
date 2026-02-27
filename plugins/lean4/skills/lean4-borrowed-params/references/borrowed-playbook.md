# Borrowed Parameter Playbook (`@&`)

## Source Anchors

- Parser + doc comment for `@&`:
  - `~/lean4/src/Lean/Parser/Term.lean`
- Elaboration to compiler annotation:
  - `~/lean4/src/Lean/Elab/BuiltinNotation.lean`
  - `~/lean4/src/Lean/Compiler/BorrowedAnnotation.lean`
- Extern lowering and borrow propagation:
  - `~/lean4/src/Lean/Compiler/IR/AddExtern.lean`
- Borrow inference policy and exported-function caveat:
  - `~/lean4/src/Lean/Compiler/IR/Borrow.lean`
- Real FFI examples:
  - `~/lean4/tests/compiler/foreign/Main/S.lean`
  - `~/lean4/tests/pkg/test_extern/TestExtern/BadExtern.lean`

## What `@&` Means

- `@&` marks a parameter as borrowed.
- The function does not consume/deallocate the value.
- Caller ownership obligations remain in place.
- Lean type checking treats `@& α` as annotation-level runtime metadata, not a distinct logical type.

## Compiler Path

1. Parser accepts `@& term`.
2. Elaboration marks the term with annotation `borrowed`.
3. Extern lowering (`IR/AddExtern`) reads that annotation and sets `Param.borrow`.
4. IR borrow pass may adjust inferred borrows, but exported declarations are handled conservatively.

## Exported Declarations Caveat

`IR/Borrow` explicitly avoids normal borrow inference for exported functions because wrappers must have predictable ownership conventions. Treat exported ABI as explicit contract territory.

## Diagnostic Checklist

1. Did you annotate the intended argument with `@&`?
2. Is this argument truly read-only in foreign code?
3. Is the function exported, and are wrapper expectations explicit?
4. Are repeated calls stable (no leaks, no double frees, no UAF)?
5. Do tests cover both borrowed and owned call paths?

## Usage Patterns

- Commonly used for `String`, structs, handles, and arrays passed to extern functions for read-only access.
- Useful for reducing unnecessary RC traffic in hot FFI paths.
- Not a universal optimization: only apply where ownership semantics are clear.

## Safety Policy

- Make ownership intent explicit at the boundary.
- Keep annotations local and measurable.
- Prefer focused tests over broad assumptions.
