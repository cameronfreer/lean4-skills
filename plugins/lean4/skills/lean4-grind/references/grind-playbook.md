# Grind Playbook

## Good Fits for `grind`

Use `grind` when normalization leaves goals that are mostly:
- propositional closure (`And`/`Or`/implications/cases),
- equalities or inequalities over standard algebraic types,
- arithmetic/order facts that should follow from existing hypotheses.

## Prep Patterns Before `grind`

- Run `simp?` to see obvious simplifications.
- Run `simp (config := {zeta := true})` when `let` bindings hide structure.
- Use `rw`/`simp` to expose canonical forms before search-heavy automation.

Typical pattern:

```lean
simp (config := {zeta := true}) at *
grind
```

## If `grind` Fails

1. Inspect unsolved goals (new `lean_goal` call).
2. Classify:
   - arithmetic closure missing facts: try `linarith`/`nlinarith`/`omega`;
   - rewrite mismatch: add local helper lemma and run `simp` then `grind`;
   - huge context: reduce hypotheses and retry.
3. Retry with a smaller, clearer context rather than stacking many expensive tactics.

## If `grind` Is Slow

- Keep the invocation local to the hardest subgoal.
- Simplify hypotheses before invoking.
- Limit search budget locally:

```lean
set_option grind.maxSteps 2000 in
  grind
```

Increase the limit only when the goal is known to be close and deterministic.

## Simproc Checklist

Create a simproc only when all are true:
- the same rewrite pattern recurs,
- `simp` lemmas are noisy/fragile/expensive,
- the reduction is deterministic and terminating.

For each simproc:
- guard on expression head/arity,
- return `.continue` when not applicable,
- prefer definitional reduction via `whnf`,
- keep the scope local unless reuse is proven.

## Anti-Patterns

- Running `grind` first on unsimplified goals with large contexts.
- Adding broad global simp lemmas to "help" one stubborn goal.
- Introducing simprocs for one-off rewrites.
- Keeping fallback tactic chains in final proof scripts.
