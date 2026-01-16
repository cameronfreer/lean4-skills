---
name: lean4-simprocs
description: Use when `simp` needs a deterministic, reusable rewrite. Treat simprocs as part of the simp pipeline.
---

# Lean 4 Simprocs (as part of simp)

## When to use

- `simp` is close but needs a deterministic rewrite.
- You repeat the same rewrite in multiple places.
- A rewrite depends on local computation (e.g., normalization).

## Composable simp pipeline

Think of simprocs as a block inside `simp`.

1) `simp set` (lemmas, simp attributes)
2) `simp config` (zeta, eta, simp theorems)
3) `simproc` (deterministic rewrite)
4) `simp` final normalization

## Minimal simproc shape

```lean
import Lean
open Lean Meta Simp

/-- Example simproc that rewrites `foo x` to `bar x`. -/
@[simp] theorem foo_eq_bar (x) : foo x = bar x := by rfl

-- Use simprocs only when simp lemmas are insufficient.
```

If you need custom logic, use a real simproc:

```lean
open Lean Meta Simp

simproc_decl mySimproc (foo _) := fun e => do
  -- compute a rewrite or return .none
  return .none
```

## Rules of thumb

- Prefer simp lemmas; use simprocs only when needed.
- Keep patterns small and oriented (avoid loops).
- Make simproc deterministic and fast.
- Register locally if the rewrite is not global.

## Checklist

- The simproc rewrite is one-way and terminating.
- `simp` set remains minimal (no noisy lemmas).
- The simproc is only enabled where it helps.

