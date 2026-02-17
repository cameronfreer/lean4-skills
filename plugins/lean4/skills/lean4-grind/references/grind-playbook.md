# Grind Playbook

This playbook is aligned with:
- Lean reference manual section on `grind`
- Lean 4 source under `src/Init/Grind/*` and `src/Lean/Meta/Tactic/Grind/*` at commit `c4d85b7`

## Good Fits for `grind`

Use `grind` when normalization leaves goals that are mostly:
- propositional closure (`And`/`Or`/implications/cases),
- equalities or inequalities over standard algebraic types,
- arithmetic/order facts that should follow from existing hypotheses.

## Minimize Calls First

Prefer this order:
1. Try `grind?` to get a suggested tactic.
2. Replace broad calls with `grind only [...]` when possible.
3. Keep only declarations/patterns that are needed for the current file.

Example:

```lean
grind?
-- then adopt the suggested `grind only [...]` shape
```

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
- Lower search budgets before adding new automation:

```lean
grind (splits := 4) (ematch := 3) (instances := 300) (gen := 5)
```

- Disable expensive branches selectively when debugging:

```lean
grind -splitIte -splitMatch -lia -linarith -ring -ac
```

For arithmetic-heavy debugging, also try:

```lean
grind +qlia
```

This is faster but incomplete for integer arithmetic.

## Pattern Controls

When inferred matching is poor, use explicit patterns:

```lean
grind_pattern myThm => f x, g y
```

Useful constraints:
- `x =/= t` / `x =?= t`
- `size x < n`
- `depth x < n`
- `is_ground x`
- `is_value x` / `is_strict_value x`
- `not_value x` / `not_strict_value x`
- `gen < n`
- `max_insts < n`
- `guard p`
- `check p`

Use `trace.grind.ematch.instance` to inspect theorem-instance generation.

## Case Analysis Controls

- `grind (splits := n)` controls split depth.
- `-splitIte` / `-splitMatch` reduce automatic branching.
- `+splitImp` enables implication-based splitting.
- In interactive mode (`grind => ...`), use `cases?`/`cases #...` to select a specific split.

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

## Diagnostics and Traces

Use these when behavior is unclear:

```lean
set_option trace.grind.ematch.instance true in
set_option trace.grind.split true in
grind
```

For broader perf diagnostics:

```lean
set_option diagnostics true in
grind
```

## Anti-Patterns

- Running `grind` first on unsimplified goals with large contexts.
- Adding broad global simp lemmas to "help" one stubborn goal.
- Introducing simprocs for one-off rewrites.
- Keeping fallback tactic chains in final proof scripts.
