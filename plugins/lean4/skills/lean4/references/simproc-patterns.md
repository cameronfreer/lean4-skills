# Simproc Patterns

> **Scope:** Not part of the prove/autoprove default loop. Consulted when `simp` needs a deterministic, reusable rewrite that simp lemmas alone cannot provide.

> **Version metadata:**
> - **Verified on:** Lean reference + release notes through `v4.27.0`
> - **Last validated:** 2026-02-17
> - **Confidence:** medium (docs reviewed; snippets not batch-compiled)

> **Grounding:** Distilled from the Lean community posts [Fantastic Simprocs and How to Write Them](https://leanprover-community.github.io/blog/posts/simprocs-tutorial/) and [Simprocs for the Working Mathematician](https://leanprover-community.github.io/blog/posts/simprocs-for-the-working-mathematician/).

## Decision Rule

- Start with ordinary `simp` and better `@[simp]` lemmas.
- Use `dsimproc` when the rewrite is definitional computation on explicit data.
- Use `simproc` when you must build proof terms or discharge side conditions.
- Use a pre-simproc when the outer form should simplify before its children.
- Use `grind` or a domain solver when normalization is done and closure is the remaining task.

## When to Use

- `simp` is close but needs a deterministic rewrite
- You repeat the same rewrite in multiple places
- A rewrite depends on local computation over explicit syntax
- You need behavior that is naturally pre-order or post-order within the simp traversal

Good simproc use cases from the community examples:
- evaluating arithmetic on explicit numerals
- proving divisibility or interval-membership facts after extracting concrete naturals
- simplifying `ite`-shaped terms before descending into both branches
- replacing an infinite family of numeral-indexed simp lemmas with one computed rewrite

## Composable Simp Pipeline

Think of simprocs as a block inside `simp`:

1. `simp set` (lemmas, simp attributes)
2. `simp config` (zeta, eta, simp theorems)
3. `simproc` / `dsimproc` (deterministic rewrite)
4. `simp` final normalization

The important mental model from the blog posts is that simprocs are not "extra tactics after simp". They are part of the simplifier's traversal strategy.

## Before Writing a Simproc

Exhaust the simpler options first:

1. Can a plain `@[simp]` lemma express the rewrite?
2. Is a local `simp only [...]` call enough?
3. Is the desired rewrite really a closure step that belongs to `grind`, `omega`, or `linarith`?

Write a simproc only when the missing rewrite depends on inspecting syntax and computing from it.

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
open Lean Meta Qq Simp

-- Sketch only: real code must also build a proof-backed replacement.
simproc_decl mySimproc (foo _) := fun e => do
  let_expr foo arg := e | return .continue
  let some n := arg.nat? | return .continue
  let rhs := mkNatLit (n + 1)
  let result := <construct a proof-backed rewrite to rhs and revisit it>
  pure result
```

The crucial control-flow rule from the tutorial is: when the term is not concrete enough, do nothing. Return `.continue` instead of guessing on symbolic inputs.

## `dsimproc` vs `simproc`

Use `dsimproc` when:
- the simplification is definitional
- you can compute the replacement directly from explicit data
- no nontrivial proof construction is needed

Use `simproc` when:
- the replacement needs a proof witness
- you need the simplifier's discharger for side conditions
- the rewrite is proposition-level, not merely definitional reduction

If in doubt, start with `simproc`; switch to `dsimproc` only when you can clearly justify the stronger definitional story.

## Pre vs Post Procedures

Most simprocs are naturally post-order: simplify children first, then rewrite the parent.

Use a preprocedure when:
- the outer constructor determines the useful rewrite
- descending first would waste work
- an `ite` or match-like shape should collapse before both branches are simplified

The `reduceIte` discussion in the working-mathematician post is the model example: sometimes the right place in the simp pipeline matters as much as the rewrite itself.

## Core Building Blocks

### Pattern Matching

Use `let_expr` to destructure the syntax you care about:

```lean
let_expr HAdd.hAdd _ _ lhs rhs := e | return .continue
```

Prefer explicit, narrow patterns over broad expression surgery.

### Extracting Data

Typical helpers include:
- `Expr.nat?`
- `Nat.fromExpr?`
- `Qq` quotations
- `Lean.toExpr`

Community guidance: extract only explicit data. If the term is symbolic, leave it alone.

### Returning Results

The practical meaning of the common results is:
- `.continue` — no rewrite here
- `.visit` — rewrite succeeded, now resimplify the replacement
- `.done` — rewrite succeeded and the replacement is already final

When unsure between `.visit` and `.done`, prefer `.visit`. It is slower, but easier to trust.

### Discharging Side Conditions

Some rewrites need auxiliary facts such as inequalities or proof obligations. That is where `simproc` outgrows `dsimproc`: it can collaborate with the simplifier's discharger rather than embedding brittle proof search inside the simproc itself.

## Rules of Thumb

- Prefer simp lemmas; use simprocs only when needed
- Keep patterns small and oriented (avoid loops)
- Make simproc deterministic and fast
- Return `.continue` for symbolic inputs you cannot compute on
- Prefer `.visit` over `.done` until you have confidence in the final normal form
- Register locally if the rewrite is not global

## Performance Discipline

- Avoid expensive work on non-matching terms
- Avoid algebraic search inside the simproc body
- Reuse existing simp and discharger machinery rather than duplicating it
- Keep numeral-only procedures numeral-only
- Benchmark against a plain `simp only [...]` baseline when possible

The long-term failure mode is turning simprocs into hidden proof search. Keep them deterministic, boring, and cheap.

## Testing Checklist

- The simproc rewrite is one-way and terminating
- Symbolic inputs return `.continue`
- Explicit-data inputs rewrite correctly
- `.visit`/`.done` choice matches the desired normal form
- The simp set remains minimal (no noisy lemmas)
- The simproc is only enabled where it helps

## Relationship to `grind`

Use simprocs to normalize expressions into better shapes for `simp`.

Use `grind` after that normalization step when the goal is now about closing mixed equalities, inequalities, or congruence facts. Simprocs and `grind` complement each other; they should not try to do each other's jobs.

## See Also

- [simp-hygiene.md](simp-hygiene.md) — simp lemma best practices
- [grind-tactic.md](grind-tactic.md) — closure after normalization
- [tactics-reference.md](tactics-reference.md) — tactic catalog including simp deep-dive
