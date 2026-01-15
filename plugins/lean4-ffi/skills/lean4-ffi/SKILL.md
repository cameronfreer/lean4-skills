---
name: lean4-ffi
description: Use when binding Lean 4 to C/ObjC libraries. Covers extern declarations, cstruct layout, and lakefile linking.
---

# Lean 4 FFI

## When to use

- You are adding a C/ObjC dependency.
- You need by-value struct interop or stable ABI layout.
- You are wiring a static library via Lake.

## Minimal extern binding

```lean
/-- Opaque pointer wrapper. -/
opaque MyHandle : Type

/-- C function: my_open : uint32_t -> MyHandle -/
@[extern "my_open"]
constant myOpen (flags : UInt32) : IO MyHandle
```

## Struct layout

Use `@[cstruct]` when you need C-compatible layout:

```lean
@[cstruct]
structure CPoint where
  x : Int32
  y : Int32
```

Keep fields concrete and avoid Lean-level invariants inside the struct.

## ByteArray-based buffers

Prefer `ByteArray` for raw buffers and pass sizes explicitly:

```lean
@[extern "my_fill"]
constant myFill (buf : @& ByteArray) (len : USize) : IO Unit
```

## Lake linking (static lib)

```lean
extern_lib mylib pkg := do
  -- compile C objects, then build a static lib
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "mylib") oFiles
```

For ObjC on macOS, compile `.m` with system clang and `-framework` flags.

## Pitfalls

- Missing `-fPIC` on non-Windows platforms.
- Mismatched integer sizes (`Int` vs `Int32` vs `USize`).
- Forgetting to keep buffers alive across FFI calls.
- Not exporting symbols with `LEAN_EXPORT` when needed.

## Checklist

- Extern name matches the C symbol.
- ABI types are exact (`UInt32`, `USize`, `Float`, etc.).
- Structs that cross the boundary use `@[cstruct]`.
- Lake builds the static lib for all platforms you support.

