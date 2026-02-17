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
1. Develop in interactive mode (`grind => ...`) so you can inspect progress and inject `have` facts.
2. Try `grind?` to get a suggested minimized tactic.
3. Replace broad calls with `grind only [...]` when possible.
4. Keep only declarations/patterns that are needed for the current file.

Example:

```lean
grind =>
  show_state
  instantiate
  finish
-- then use `grind?` and adopt the suggested `grind only [...]` shape
```

## Prototype -> Harden Pipeline

When building out new API automation:
1. Prototype aggressively:

```lean
grind +suggestions +locals
```

2. Minimize:
   - run `grind?`,
   - keep only needed theorem arguments (`grind only [...]` when practical).
3. Stabilize:
   - convert repeatedly selected lemmas into `@[local grind ...]` / `@[local simp]`,
   - escalate to global annotations only after repeated success across files.

This keeps early exploration fast while converging to deterministic proofs.

## Library Design Template (`grind_indexmap`)

Use `~/lean4/tests/lean/run/grind_indexmap_pre.lean` and `~/lean4/tests/lean/run/grind_indexmap.lean` as the canonical before/after example:

1. Start with direct definitions and unresolved obligations.
2. Use `grind => ...` and temporary `have` bridges to discover missing facts.
3. Convert repeated bridges into local grind annotations (`@[local grind ...]`, `@[local grind =]`) and `grind_pattern` where needed.
4. Target short API proofs of the form `by grind +locals`.
5. Promote only mature, widely useful theorems to global `@[grind]`/`@[grind =]`.

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

If the failure is "missing bridge fact", add a temporary `have` in `grind => ...` mode, then back-port it into annotations or a `grind_pattern` so the final proof does not depend on ad-hoc interactive scaffolding.

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

Interactive skeleton:

```lean
grind =>
  show_state
  instantiate
  first
    (cases_next)
    (skip)
  finish
```

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

For search-space diagnosis, compare:
1. baseline `grind`
2. reduced branching `grind (splits := 4) -splitIte -splitMatch`
3. reduced instantiation `grind (ematch := 3) (gen := 5) (instances := 300)`
4. solver-isolated runs (`-lia -linarith -ring -ac`) and re-enable one by one

## `try?` Fallback Policy

When manual loops stall, run `try?`:
- it probes multiple grind configurations and other tactics,
- it can already leverage suggestion/local-library paths,
- it often returns a useful first script quickly.
- see `~/lean4/tests/lean/run/try_first_par.lean` for a representative test.

Then harden:
1. extract the successful grind-relevant core,
2. minimize with `grind?`,
3. replace repeated explicit premises with local/global annotations.

## Anti-Patterns

- Running `grind` first on unsimplified goals with large contexts.
- Adding broad global simp lemmas to "help" one stubborn goal.
- Introducing simprocs for one-off rewrites.
- Keeping fallback tactic chains in final proof scripts.
- Keeping long-term dependence on `+suggestions` when stable annotations would make proofs deterministic.
