---
name: lean4-ffi-interop
description: Use when integrating Lean 4 with C/C++ via `@[extern]` or `@[export]`, wiring Lake external libraries, or debugging symbol/link/init issues in Lean FFI builds.
---

# Lean4 FFI Interop

Use this skill for boundary work between Lean and foreign code. Keep the Lean API stable, make symbol names explicit, and verify linkage early.

Grounding for this skill:
- Compiler attributes: `~/lean4/src/Lean/Compiler/ExternAttr.lean`, `~/lean4/src/Lean/Compiler/ExportAttr.lean`
- FFI examples: `~/lean4/tests/lake/examples/ffi/`, `~/lean4/tests/lake/examples/reverse-ffi/`
- Runtime C API: `~/lean4/stage0/src/include/lean/lean.h`

## Direction Selection

- Lean calling foreign code: use `@[extern]` with an `opaque` declaration in Lean.
- Foreign code calling Lean: use `@[export]` on a Lean `def` (or `opaque` wrapper).
- Both directions in one package: keep each boundary in a dedicated module so symbol maps stay obvious.

## Lean -> C/C++ (`@[extern]`)

Use this pattern:

```lean
@[extern "my_add"]
opaque myAdd : UInt32 -> UInt32 -> UInt32
```

Guidelines:
- Match Lean type and native ABI exactly.
- Prefer explicit symbol names (`@[extern "symbol"]`) over adhoc defaults.
- Keep wrappers small and total on the Lean side.

## C/C++ -> Lean (`@[export]`)

Use this pattern:

```lean
@[export my_length]
def myLength (s : String) : UInt64 :=
  s.length.toUInt64
```

Guidelines:
- Export names must be valid C/C++ identifiers.
- Keep exported entry points free of implicit global state where possible.
- If exposing many functions, keep an "exports" module that only contains boundary symbols.

## Lake Wiring Checklist

For external C/C++ artifacts, mirror `tests/lake/examples/ffi/lib/lakefile.lean`:
- Build object targets (`target ... .o`)
- Build static/shared library targets (`buildStaticLib`/`buildSharedLib`)
- Attach via `moreLinkObjs` / `moreLinkLibs`

For interpreter/metaprogram use of extern functions:
- Enable precompiled module loading when needed (`precompileModules := true` in the relevant Lean lib/exe config)

## Reverse-FFI Initialization Checklist

When embedding Lean in a C host (see `tests/lake/examples/reverse-ffi/main.c`):
1. Call `lean_initialize_runtime_module()`
2. Call generated module initializer(s), e.g. `initialize_pkg_Module(...)`
3. Check `lean_io_result_is_ok`
4. Call `lean_io_mark_end_initialization()`
5. Only then call exported Lean functions

Skipping this order causes hard-to-debug runtime failures.

## Debug Order

1. Validate symbol names first (`@[extern "..."]` / `@[export ...]`)
2. Validate Lake linking targets
3. Validate runtime init sequence
4. Only then inspect typing/ownership details in `lean.h`

For concrete snippets and failure signatures, read `references/ffi-playbook.md`.
