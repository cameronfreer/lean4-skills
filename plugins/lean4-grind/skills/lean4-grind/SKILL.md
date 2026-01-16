---
name: lean4-grind
description: Use when goals should close after normalization. Focus on bounded, premise-aware `grind` usage.
---

# Lean 4 Grind

## When to use

- The goal looks like arithmetic/logic closure after normalization.
- `simp` normalizes but does not close.
- You want SMT-style automation with bounded steps.

## Composable pipeline

1) Normalize: `simp?` or `simp (config := { zeta := true })`
2) Close: `grind`
3) Bound: `set_option grind.maxSteps` if it is slow
4) Narrow: use a small lemma set or local context only

## Tips

- Run `grind` after `simp`, not before.
- If `grind` loops or is slow, reduce the context or set bounds.
- Prefer explicit `by_cases` before `grind` if needed.

## Checklist

- `simp` produces a normalized goal.
- `grind` closes within a bounded step budget.
- Premises are minimal and relevant.

