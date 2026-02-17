# FFI Patterns

> **Scope:** Not part of the prove/autoprove default loop. Consulted when binding Lean 4 to C/ObjC libraries.

> **Version metadata:**
> - **Verified on:** Lean reference + release notes through `v4.27.0`
> - **Last validated:** 2026-02-17
> - **Confidence:** medium (FFI APIs are stable in concept but have version-specific details)

## When to Use

- Adding a C/ObjC dependency
- Needing by-value struct interop or stable ABI layout
- Wiring a static library via Lake

## Composable Building Blocks

- `OpaqueHandle`: `opaque` + extern open/close
- `BufferIO`: `ByteArray` + explicit length
- `CStruct`: `@[cstruct]` layout for by-value structs
- `Wrapper`: Lean-level safe API (lifetime + error handling)
- `Link`: Lake `extern_lib` static build

Combine blocks rather than writing monolithic FFI code.

## Minimal Extern Binding

```lean
/-- Opaque pointer wrapper. -/
opaque MyHandle : Type

/-- C function: my_open : uint32_t -> MyHandle -/
@[extern "my_open"]
constant myOpen (flags : UInt32) : IO MyHandle
```

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

## Lake Linking (Static Lib)

```lean
extern_lib mylib pkg := do
  -- compile C objects, then build a static lib
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "mylib") oFiles
```

For ObjC on macOS, compile `.m` with system clang and `-framework` flags.

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

## See Also

- [Lean 4 Reference: FFI](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/) — official documentation
