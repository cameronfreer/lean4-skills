---
name: lean4-symbol-linkage
description: Use when debugging Lean 4 native symbol naming/linkage issues (mangled names, `_init_` symbols, boxed-name suffixes, package prefixes, and `@[export]` overrides).
---

# Lean4 Symbol Linkage

Use this skill when native symbol lookup or linker behavior is unclear.

Grounding for this skill:
- `~/lean4/src/Lean/Compiler/NameMangling.lean`
- `~/lean4/src/Lean/Compiler/ModPkgExt.lean`
- `~/lean4/src/Lean/Compiler/IR/EmitC.lean`
- `~/lean4/src/Lean/Compiler/IR/EmitUtil.lean`
- `~/lean4/tests/compiler/foreign/README.md`

## Mental Model

Symbol generation depends on:
- declaration name mangling (`Name.mangle`)
- package-aware prefixing (`mkPackageSymbolPrefix`)
- init naming (`mkModuleInitializationFunctionName`, `_init_...`)
- boxed-name suffixes (`mkMangledBoxedName`, `___boxed`)
- explicit `@[export]` overrides

If a symbol is missing, identify which layer changed it first.

## Fast Triage

1. Check whether declaration uses `@[export]`.
2. If yes, exported symbol may bypass standard stem naming.
3. If no, compute expected stem from package/module context.
4. For init failures, check module initialization function names.
5. For interpreter/runtime mismatch, check boxed-name lookup path.

## Key Rules

- `main` is special-cased in C emission.
- Init symbols use `_init_` prefix on top of stem logic.
- Exported names must satisfy C/C++ identifier constraints.
- Module package context influences prefix (`l_` vs `lp_<pkg>_...`).

## Where to Inspect in Compiler Output

In `IR/EmitC`:
- `toCName`
- `toCInitName`
- `emitFnDecls`
- `emitInitFn`

In environment-level naming:
- `getSymbolStem` in `ModPkgExt`
- name mangling utilities in `NameMangling`

## Practical Debug Order

1. Verify declaration-level attributes (`@[export]`, `@[extern]`).
2. Verify expected stem/prefix under package context.
3. Verify emitted C symbol names in generated output.
4. Verify init function name and call site ordering.
5. Only then debug downstream runtime behavior.

For concrete examples and checks, read `references/symbol-playbook.md`.
