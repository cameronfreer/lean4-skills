# Lean Symbol Linkage Playbook

## Source Anchors

- Name mangling and module-init stem construction:
  - `~/lean4/src/Lean/Compiler/NameMangling.lean`
- Package-aware symbol stem:
  - `~/lean4/src/Lean/Compiler/ModPkgExt.lean`
- C emission naming:
  - `~/lean4/src/Lean/Compiler/IR/EmitC.lean`
- Used-declaration and init-collection helpers:
  - `~/lean4/src/Lean/Compiler/IR/EmitUtil.lean`
- Foreign-linking example:
  - `~/lean4/tests/compiler/foreign/README.md`

## Naming Layers

1. Base mangling:
   - `Name.mangle`
2. Package prefix:
   - `mkPackageSymbolPrefix`
3. Symbol stem:
   - `getSymbolStem`
4. Init symbol:
   - `_init_` + stem
5. Boxed variant:
   - `mkMangledBoxedName`
6. Export override:
   - `@[export ...]` path in `EmitC.toCName` / `toCInitName`

## Typical Failure Modes

- Linker error: missing symbol
  - cause: expected mangled stem differs from export override
- Runtime init failure
  - cause: wrong module init function name or package prefix assumption
- Works in one package layout but fails in another
  - cause: `lp_<pkg>_...` prefix changes symbol names
- Boxed lookup mismatch
  - cause: using unboxed symbol where interpreter expects boxed name suffix

## Quick Diagnostic Checklist

1. Is there `@[export]`?
2. Is the declaration in a package context with non-default prefix?
3. Is this an init symbol (`_init_...`) or regular symbol?
4. Is the caller using boxed or unboxed symbol variant?
5. Does generated C output declare the expected symbol?

## Suggested Workflow

1. Compute expected symbol path from source rules.
2. Inspect generated C declarations in emitted output.
3. Compare with linker/runtime complaint.
4. Fix one naming layer only, then rebuild and retest.
