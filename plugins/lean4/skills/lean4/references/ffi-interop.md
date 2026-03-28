# FFI Interop Reference

> **Scope:** Not part of the prove/autoprove default loop. Consulted when binding Lean 4 to C/C++ libraries or debugging FFI issues.

> **Version metadata:**
> - **Verified on:** Lean reference + release notes through `v4.27.0`
> - **Last validated:** 2026-03-28
> - **Confidence:** medium (content derived from PR #24 and existing ffi-patterns.md, vetted against current docs)

## When to Use

- Adding a C/C++ dependency
- Exposing Lean functions to a C host
- Debugging symbol, link, or initialization issues
- Needing by-value struct interop or stable ABI layout
- Embedding Lean in a C/C++ application (reverse FFI)

## Direction Selection

- **Lean calling C:** use `@[extern]` with an `opaque` declaration
- **C calling Lean:** use `@[export]` on a Lean `def`
- **Both directions:** keep each boundary in a dedicated module so symbol maps stay obvious

## Lean Calling C (`@[extern]`)

```lean
@[extern "my_add"]
opaque myAdd : UInt32 -> UInt32 -> UInt32
```

Guidelines:
- Match Lean type and native ABI exactly (`UInt32`, `USize`, `Float`, etc.)
- Prefer explicit symbol names (`@[extern "symbol"]`) over ad-hoc defaults
- Keep wrappers small and total on the Lean side

For opaque handle patterns:

```lean
opaque MyHandle : Type

@[extern "my_open"]
constant myOpen (flags : UInt32) : IO MyHandle
```

## C Calling Lean (`@[export]`)

```lean
@[export my_length]
def myLength (s : String) : UInt64 :=
  s.length.toUInt64
```

The export name is an identifier (no quotes). On the C side:

```c
extern uint64_t my_length(lean_obj_arg);
```

Guidelines:
- Export names must be valid C/C++ identifiers
- Keep exported entry points free of implicit global state where possible
- If exposing many functions, keep an "exports" module with only boundary symbols

## Borrowed Parameters (`@&`)

Prefix a parameter type with `@&` to mark it as borrowed — the function will not consume or deallocate the value:

```lean
@[extern "my_fill"]
constant myFill (buf : @& ByteArray) (len : USize) : IO Unit
```

Key points:
- `@&` affects ABI and runtime behavior only, not Lean's logical type system
- Use for read-only object parameters crossing FFI boundaries
- Reduces unnecessary reference-count traffic in hot FFI paths
- Keep extern Lean signature and foreign prototype ownership conventions aligned
- Do not assume borrow inference will fix exported ABI boundaries — treat exported functions as explicit ownership contracts

## Struct Layout

Use `@[cstruct]` when you need C-compatible layout:

```lean
@[cstruct]
structure CPoint where
  x : Int32
  y : Int32
```

Keep fields concrete and avoid Lean-level invariants inside the struct.

## ByteArray-Based Buffers

Prefer `ByteArray` for raw buffers and pass sizes explicitly:

```lean
@[extern "my_fill"]
constant myFill (buf : @& ByteArray) (len : USize) : IO Unit
```

## Lake Wiring

For external C/C++ artifacts:
- Build object targets with `buildO`
- Build library targets with `buildStaticLib` or `buildSharedLib`
- Attach via `moreLinkObjs` / `moreLinkLibs` on the Lean library or executable config

```lean
extern_lib mylib pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "mylib") oFiles
```

For interpreter/metaprogram use of extern functions:
- Enable precompiled module loading: `precompileModules := true` in the relevant Lean lib/exe config

For ObjC on macOS, compile `.m` with system clang and `-framework` flags.

## Reverse-FFI Host Initialization

When embedding Lean in a C host, this initialization sequence is **mandatory** and order-sensitive:

1. `lean_initialize_runtime_module()` — initialize the Lean runtime
2. Call generated module initializer(s), e.g. `initialize_pkg_Module(...)` — initialize your Lean modules
3. Check result with `lean_io_result_is_ok()` — verify initialization succeeded
4. `lean_io_mark_end_initialization()` — signal that init is complete
5. Call exported Lean functions — only safe after step 4

Skipping or reordering these steps causes hard-to-debug runtime failures (missing global state, extension lookup failures, crashes).

## Initialization Mechanisms

> This section covers initialization internals. Most FFI users only need the reverse-FFI sequence above.

Three mechanisms exist:
- **`initialize` command** — default path for registering refs/extensions and one-time setup. Prefer this.
- **`[init]` attribute** — explicit initialization for declarations run on import.
- **`builtin_initialize` / `[builtin_init]`** — compiler/runtime bootstrap path, not for general-purpose app setup.

### Debugging Init-Order Issues

When behavior differs between interpreted and compiled execution:
1. Confirm the initializer is attached to the expected declaration
2. Confirm whether the code path is interpreted or native
3. Confirm module initialization for every imported module has run
4. Check whether one-time global side effects are skipped by duplicate-avoidance state

Symptoms that point to initialization rather than logic errors:
- Exported symbol callable but behaves as if global state is unset
- Extension lookup fails only in host executable
- Behavior differs between `lake env lean` and compiled binary

## Symbol Linkage

> This section covers compiler-level symbol naming. Most FFI users only need explicit `@[extern "name"]` / `@[export name]` and will not encounter these details.

Symbol generation depends on:
- Declaration name mangling (e.g., `Name.mangle`)
- Package-aware prefixing
- Init symbol naming (`initialize_` prefix plus mangled module name)
- Boxed-name variants (e.g., `___boxed` suffix)
- Explicit `@[export]` overrides (bypasses standard naming)

### Debug Order for Linker Issues

1. Check `@[extern]` / `@[export]` attributes on the declaration
2. Check whether the export name bypasses standard stem naming
3. Check Lake linking targets (`moreLinkObjs` / `moreLinkLibs`)
4. Check module initialization function names
5. Inspect generated C output for expected symbols

## Common Failure Modes

| Symptom | Likely cause |
|---------|-------------|
| `unknown symbol` at runtime | Symbol name mismatch or library not linked |
| Works in `lake build`, fails in eval | Missing `precompileModules` for interpreter |
| Crash when calling exported Lean from C | Runtime/module initialization order wrong |
| Global state appears unset in host exe | Missing or misordered `initialize_` call |
| Behavior differs between modes | Init paths mismatched (native vs interpreter) |

## Pitfalls

- Missing `-fPIC` on non-Windows platforms
- Mismatched integer sizes (`Int` vs `Int32` vs `USize`)
- Forgetting to keep buffers alive across FFI calls
- Not exporting symbols with `LEAN_EXPORT` when needed

## Checklist

- Extern name matches the C symbol
- ABI types are exact (`UInt32`, `USize`, `Float`, etc.)
- Structs that cross the boundary use `@[cstruct]`
- Lake builds the static lib for all platforms you support
- `@&` annotations match foreign prototype ownership

## See Also

- [Lean 4 Reference: FFI](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/) — official documentation
- [compiler-internals](compiler-internals.md) — compiler attributes, specialization, pipeline
