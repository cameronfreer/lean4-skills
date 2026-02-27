---
name: lean4-init-runtime
description: Use when debugging Lean 4 initialization behavior (`initialize`, `[init]`, `builtin_initialize`), module init ordering, or runtime setup for embedded/reverse-FFI hosts.
---

# Lean4 Init Runtime

Use this skill when behavior differs between interpreted and native execution due to initialization order or missing init hooks.

Grounding for this skill:
- `~/lean4/src/Lean/Compiler/InitAttr.lean`
- `~/lean4/src/Lean/Compiler/ModPkgExt.lean`
- `~/lean4/tests/lake/examples/reverse-ffi/main.c`
- `~/lean4/tests/lake/examples/reverse-ffi/lib/RFFI.lean`

## Choose the Right Mechanism

- `initialize` command: default path for registering refs/extensions and one-time setup.
- `[init]`: explicit initialization attribute for declarations run on import.
- `builtin_initialize` / `[builtin_init]`: compiler/runtime bootstrap path, not general-purpose app setup.

Prefer `initialize` unless there is a concrete reason to control init attr behavior directly.

## Debugging Init-Order Issues

When you see "works in one mode, fails in another" symptoms:
1. Confirm the initializer is attached to the declaration you expect.
2. Confirm whether the code path is interpreted or native.
3. Confirm module initialization for every imported module has run.
4. Confirm one-time global side effects are not skipped by duplicate-avoidance state.

Focus first on init ordering and mode, not theorem/proof logic.

## Interpreted vs Native Caveat

`InitAttr` handles both:
- native module initializer entry points
- interpreter fallback for initializers when native init is unavailable

Practical implication: a declaration may appear valid but still fail at runtime if init paths are mismatched across modes.

## Reverse-FFI Host Sequence

When C/C++ embeds Lean and calls exported Lean symbols:
1. `lean_initialize_runtime_module()`
2. call generated module initializer(s) (`initialize_pkg_Module(...)`)
3. check init result object
4. `lean_io_mark_end_initialization()`
5. call exported Lean functions

This order is mandatory for stable behavior.

## Failure Signatures

- exported symbol callable but behaves as if global state is unset
- extension lookup fails only in host executable
- behavior differs between `lake env lean` and compiled binary

These usually indicate missing or misordered initialization, not ordinary type errors.

For concrete traces and source-backed examples, read `references/init-playbook.md`.
