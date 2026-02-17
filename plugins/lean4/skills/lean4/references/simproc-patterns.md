# Simproc Patterns

> **Scope:** Not part of the prove/autoprove default loop. Consulted when `simp` needs a deterministic, reusable rewrite that simp lemmas alone cannot provide.

> **Version metadata:**
> - **Verified on:** Lean reference + release notes through `v4.27.0`
> - **Last validated:** 2026-02-17
> - **Confidence:** medium (docs reviewed; snippets not batch-compiled)

## When to Use

- `simp` is close but needs a deterministic rewrite
- You repeat the same rewrite in multiple places
- A rewrite depends on local computation (e.g., normalization)

## Composable Simp Pipeline

Think of simprocs as a block inside `simp`:

1. `simp set` (lemmas, simp attributes)
2. `simp config` (zeta, eta, simp theorems)
3. `simproc` (deterministic rewrite)
4. `simp` final normalization

## Minimal Simproc Shape

Start with a plain `@[simp]` lemma when possible:

```lean
import Lean
open Lean Meta Simp

-- Prefer this first: simple deterministic rewrites belong in simp lemmas.
@[simp] theorem foo_eq_bar (x) : foo x = bar x := by rfl
```

Escalate to a real simproc only when the rewrite needs custom computation:

```lean
open Lean Meta Simp

simproc_decl mySimproc (foo _) := fun e => do
  -- compute a rewrite or return .none
  return .none
```

## Rules of Thumb

- Prefer simp lemmas; use simprocs only when needed
- Keep patterns small and oriented (avoid loops)
- Make simproc deterministic and fast
- Register locally if the rewrite is not global

## Checklist

- The simproc rewrite is one-way and terminating
- `simp` set remains minimal (no noisy lemmas)
- The simproc is only enabled where it helps

## See Also

- [simp-hygiene.md](simp-hygiene.md) — simp lemma best practices
- [tactics-reference.md](tactics-reference.md) — tactic catalog including simp deep-dive
