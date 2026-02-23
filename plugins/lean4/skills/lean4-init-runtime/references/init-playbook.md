# Lean Init Runtime Playbook

## Source Anchors

- `~/lean4/src/Lean/Compiler/InitAttr.lean`
- `~/lean4/src/Lean/Compiler/ModPkgExt.lean`
- `~/lean4/tests/lake/examples/reverse-ffi/main.c`
- `~/lean4/tests/lake/examples/reverse-ffi/lib/RFFI.lean`

## Key Model

Initialization in Lean 4 spans:
- declaration-level init metadata (`[init]`, `[builtin_init]`)
- module initializer symbols and package-aware symbol naming
- mode-specific execution path (native initializer vs interpreter fallback)

When runtime state is missing, treat this as an initialization pipeline issue first.

## Practical Checklist

1. Verify the declaration has the expected init annotation.
2. Verify the module providing that declaration is imported in the failing context.
3. Verify module initialization was executed before first use.
4. Verify global side effects are not expected to rerun when deduplicated by init-state tracking.
5. In host-embedded flows, verify C-side runtime/init call order.

## Reverse-FFI Minimal Host Pattern

From the upstream reverse-ffi example:
- initialize Lean runtime module
- initialize target Lean module
- validate init result object
- mark end of initialization
- then invoke exported Lean symbol(s)

Skipping/reshuffling these steps causes subtle state failures.

## Troubleshooting Pattern

If failure appears only:
- in `main.c` host but not in Lean executable, inspect host init order.
- in interpreted mode but not native mode, inspect initializer availability/fallback path.
- after refactors moving declarations across modules, inspect module import/init coverage.

## Escalation Order

1. Fix initializer order and coverage
2. Fix host runtime entry sequence
3. Re-check symbol/package naming assumptions
4. Only then inspect downstream business logic
