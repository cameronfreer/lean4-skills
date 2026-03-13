---
name: stuck?
description: "Use when a user is stuck on a Lean goal, tactic proof, or type error and wants the next concrete move. Triage the blocker, inspect goal/diagnostics, try low-cost tactics first (`try?`, `exact?`, `apply?`, `rw?`, `simp?`, `hint` when mathlib is available), then escalate to search, refactoring, or debugging advice."
---

# Lean Stuck Triage

Use this skill when the user says they are stuck, asks what tactic to try next, or wants Lean debugging advice rather than a long autonomous proof search.

## Default Loop

1. Make the blocker concrete with `lean_goal`, `lean_term_goal`, `lean_hover_info`, or `lean_diagnostic_messages`.
2. Classify the blocker before trying tactics:
   - definitional equality / simplification
   - missing intro / constructor / cases step
   - missing rewrite
   - arithmetic / inequalities
   - missing library lemma
   - typeclass / coercion / elaboration issue
   - proof is too large and needs a helper lemma
3. Spend a short budget on cheap tactics and suggestion tools. If 2-3 direct attempts fail, switch strategy instead of thrashing.
4. Replace exploratory tactics with explicit proof code once something works. Do not leave `try?`, `exact?`, `apply?`, `rw?`, or `simp?` in the final proof.

## Cheap Tactic Pass

Start with low-cost, local tactics:

`rfl` → `simp` / `simpa` → `rw [...]` → `change` / `show` → `constructor` / `refine` → `intro` / `cases` / `rcases` / `obtain` → `subst` / `have` / `specialize`

Then use Lean's suggestion tactics:

- `try?` when you want a concrete candidate script.
- `exact?` when one lemma or hypothesis might close the goal.
- `apply?` when a known theorem shape likely reduces the goal to manageable subgoals.
- `rw?` when the next move is "some rewrite exists, but I do not know its name."
- `simp?` to discover which lemmas `simp` wants before committing to `simp only [...]`.
- `omega` for Presburger-style arithmetic over naturals and integers.
- `grind` for mixed equality / constructor / local-hypothesis cleanup after the context is in the right shape.
- `decide` or `native_decide` for finite decidable goals.

## If Mathlib Is Available

If the file imports `Mathlib` or the project clearly depends on mathlib, add mathlib-heavy tactics to the first pass:

- `hint` for a quick "kitchen sink" pass over registered hint tactics.
- `linarith` / `nlinarith` for linear or mildly nonlinear arithmetic.
- `norm_num` for explicit numeral goals.
- `ring` / `ring_nf` for polynomial normalization.
- `positivity` for positivity side conditions.
- `aesop` when the goal is mostly structural search over local facts and tagged lemmas.
- `field_simp` or `field` for rational-function equalities over fields.

Do not assume mathlib-only tactics exist in core Lean projects. Check imports before suggesting them.

## Search Before More Tactics

When the direct tactic pass stalls, search rather than guessing:

- `lean_local_search` for exact names or prefixes.
- `lean_loogle` for type-shaped search.
- `lean_leansearch` for natural-language mathlib search.
- `lean_leanfinder` for semantic search from the goal text.
- `lean_hammer_premise` when you want candidate lemmas for `simp only [...]`, `grind [...]`, or `aesop`.
- `lean_multi_attempt` to compare a small set of candidate tactics without editing the file.

If a tool suggests something plausible, test it quickly and then write the explicit proof term or tactic sequence.

## Structural Advice

If the proof still feels stuck, the issue is usually structure, not one more tactic:

- Shrink the goal with `have`, `suffices`, or `refine`.
- Put the target into the right shape with `change` or `show`.
- Turn an opaque local fact into named intermediate facts with `have h1 := ...`.
- Destructure hypotheses early with `rcases`, `cases`, or `obtain`.
- For rewrite-heavy goals, normalize one side first and only then search for the key lemma.
- For typeclass failures, inspect binder order and missing outer instances before adding `haveI` / `letI`.
- For coercion problems, compare hovered types exactly; avoid random casts.
- For finite concrete goals, prefer computation (`decide`, `native_decide`) over proof search.

## Communication Pattern

When helping the user, always explain:

1. what kind of blocker this is,
2. what the next 1-3 concrete things to try are,
3. why those steps come before heavier search or refactoring.

If you cannot justify the next tactic from the goal state, stop and inspect more instead of guessing.

## Escalation

This skill is for short unblock loops. If the task turns into broader proof development, hand off to the main [lean4](../lean4/SKILL.md) skill or the `/lean4:prove` / `/lean4:autoprove` commands.

## References

- [lean4](../lean4/SKILL.md) - Full Lean proving workflow
- [tactics-reference](../lean4/references/tactics-reference.md) - Compact tactic catalog
- [lean-lsp-tools-api](../lean4/references/lean-lsp-tools-api.md) - Search and inspection tools
- [Lean Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) - Core suggestion tactics such as `exact?`, `apply?`, `rw?`, and `try?`
- [Mathlib `hint` tactic docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Hint.html) - Mathlib's registered-hint tactic
