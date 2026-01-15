---
name: lean4-simprocs-grind
description: Use when proofs are stuck due to repetitive rewrites. Focuses on a composable normalization pipeline and simproc design.
---

# Lean 4 Simprocs + Grind

## When to use

- Repeated manual rewrites across the same pattern.
- `simp` is too weak or loops without a targeted rewrite.
- Goals are arithmetic/logic closure after normalization.

## Composable pipeline

1) `Normalize` = `simp?` or `simp (config := { zeta := true })`
2) `Rewrite` = simproc for deterministic, reusable rewrites
3) `Close` = `grind` for closure after normalization
4) `Bound` = `set_option grind.maxSteps` when needed

## Workflow

1. Minimize the goal: try `simp?` or `simp (config := { zeta := true })`.
2. Choose the tool:
   - Simproc if the rewrite is deterministic and reusable.
   - `grind` if the goal should close after normalization and standard lemmas.
3. Simproc path:
   - Keep patterns small and oriented to avoid loops.
   - Prove a correctness lemma.
   - Register with `simp` or invoke explicitly in the local section.
4. Grind path:
   - Normalize with `simp`/`simp?`, then run `grind`.
   - If slow, bound with `set_option grind.maxSteps` or reduce premises.
5. Validate: `lake build` the edited module.

## Common mistakes

- Rewrites that expand terms and loop under `simp`.
- Overly general simproc patterns that match too much.
- Using `grind` before normalization (slow, noisy traces).

## Checklist

- Simproc only rewrites in one direction.
- `simp` set is minimal and non-looping.
- `grind` succeeds with bounded steps if needed.
