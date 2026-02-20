# Lean 4 FFI Playbook

## Source Anchors

- Compiler attribute semantics:
  - `~/lean4/src/Lean/Compiler/ExternAttr.lean`
  - `~/lean4/src/Lean/Compiler/ExportAttr.lean`
- Lake example (both static + shared linking):
  - `~/lean4/tests/lake/examples/ffi/lib/lakefile.lean`
  - `~/lean4/tests/lake/examples/ffi/lib/lean/FFI/Static.lean`
  - `~/lean4/tests/lake/examples/ffi/lib/lean/FFI/Shared.lean`
  - `~/lean4/tests/lake/examples/ffi/lib/c/ffi_static.c`
  - `~/lean4/tests/lake/examples/ffi/lib/c/ffi_shared.cpp`
- Reverse FFI host embedding:
  - `~/lean4/tests/lake/examples/reverse-ffi/lib/RFFI.lean`
  - `~/lean4/tests/lake/examples/reverse-ffi/main.c`

## Minimal Patterns

### Lean calling C

```lean
@[extern "my_add"]
opaque myAdd : UInt32 -> UInt32 -> UInt32
```

```c
uint32_t my_add(uint32_t a, uint32_t b) { return a + b; }
```

### C calling Lean

```lean
@[export my_length]
def myLength (s : String) : UInt64 :=
  s.length.toUInt64
```

```c
extern uint64_t my_length(lean_obj_arg);
```

## Lake Checklist for Native Artifacts

- Add `input_file` for each C/C++ source
- Build object file targets with `buildO`
- Build library target with `buildStaticLib` or `buildSharedLib`
- Attach to Lean library/executable with:
  - `moreLinkObjs := #[...]`
  - `moreLinkLibs := #[...]`

## Common Failure Modes

- `unknown symbol` at runtime:
  - symbol name mismatch between `@[extern]` and native definition
  - library not linked in `moreLinkObjs` / `moreLinkLibs`
- works in `lake build`, fails in eval/interpreter:
  - missing precompiled module configuration for runtime loading context
- crash when calling exported Lean from C:
  - Lean runtime/module initialization order is wrong

## Practical Verification Loop

1. `lake build` from package root
2. run small executable that touches each boundary symbol
3. if reverse FFI, run C host executable as a separate test
4. only after boundary is stable, optimize wrappers/types
