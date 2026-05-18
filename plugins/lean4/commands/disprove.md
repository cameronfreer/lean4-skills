---
name: disprove
description: Search for counterexamples and produce a certified Lean refutation
user_invocable: true
argument-hint: '<File.lean:LINE | Namespace.theoremName> [--max-cycles=N] [--max-stuck-cycles=N] [--max-runtime=DURATION] [--negation-policy=counterexample-only] [--commit=auto|ask|never]'
---

# Lean4 Disprove

Search for a counterexample to a target proposition and, when possible,
produce a Lean proof of its negation. Reports `FALSE` only when Lean
certifies the refutation; otherwise `WITNESS_UNCERTIFIED` (a candidate was
found but Lean refused to certify it) or `INCONCLUSIVE` (no candidate
found within budgets).

`/lean4:disprove` is **always interactive** — disprove is an exploratory
search, and the workflow prompts you at each cycle's Plan phase to choose
a search method and configure its parameters.

## Usage

```
/lean4:disprove Foo.lean:42                       # File + line (sorry/declaration site)
/lean4:disprove MyNs.SubNs.myThm                  # Qualified theorem name
/lean4:disprove Foo.lean:42 --max-cycles=5
/lean4:disprove Foo.lean:42 --commit=never
```

## Prime Directive

Report `FALSE` **only** when a Lean term of the negation typechecks under
`lake env lean` with no `sorry` or `admit`. Fast witnesses and informal
heuristics are *hypotheses* until Lean certifies them. See
[disprove-engine.md § Prime Directive](../skills/lean4/references/disprove-engine.md#prime-directive--epistemological-strictness).

## Invocation Contract

Interpret this command's inputs per the
[Command Invocation Contract](../skills/lean4/references/command-invocation.md).

**Primary path (hook-validated):** If a `validated-invocation` block for this
command appears in context, treat it as the authoritative interpretation of
parser-decidable inputs and do **not** re-parse the raw invocation text for
those inputs. Start by reading all parser-decided fields from the block. Emit
the final **Resolved Inputs** summary from the block values.
See [Validated Invocation Block](../skills/lean4/references/command-invocation.md#validated-invocation-block-host-provided).

**Fallback path (other hosts):** If no `validated-invocation` block is present,
parse the raw invocation text against this command's input table before
Phase 1.

Startup requirements:

1. Emit a **Resolved Inputs** block with explicit values, defaults,
   coercions, ignored flags, and startup validation errors.
2. Refuse to start on startup validation errors.
3. Call `bash "$LEAN4_SCRIPTS/cycle_tracker.sh" init` with resolved
   numeric values for `--max-cycles`, `--max-stuck-cycles`, and
   `--max-runtime`. Disprove has no deep mode in v1; omit the deep
   args and let the tracker default them (they remain inert because
   disprove never calls `can-deep` / `deep`). A failed init (exit 2)
   is a startup validation error — do not proceed.
4. The cycle-tracker state file is the single source of truth for session
   counters. Read counters from `tick`/`status` output, not from
   conversational memory.

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| target | Yes | — | `File.lean:LINE` or `Namespace.theoremName`. Inline Props not supported in v1. |
| --max-cycles | No | 3 | Max widening passes. Each cycle picks one method via the Step 1 menu and configures its parameters via Step 2 prompts. |
| --max-stuck-cycles | No | 2 | Bail after this many consecutive cycles where Replan has no remaining widening lever. |
| --max-runtime | No | 5m | Best-effort wall-clock session budget across all cycles. |
| --negation-policy | No | counterexample-only | v1: locked. Reserved for future `with-salvage`. |
| --commit | No | ask | Per-cycle Checkpoint behavior. `ask` prompts before each commit; `auto` commits without prompting; `never` skips committing (leave staging to `/lean4:checkpoint`). |

Per-method parameters (e.g. enumerate's range, `native_decide` opt-in,
sample count for `plausible`, external-solver choice) are **runtime
prompts** in each cycle's Plan phase, not top-level flags. See
[disprove-engine.md § Step 2 — Per-Method Configuration](../skills/lean4/references/disprove-engine.md#step-2--per-method-configuration).

## Two-Step Method Selection

Every cycle's Plan phase prompts the user in two steps:

1. **Step 1 — Method menu.** Choose one of: decide-cascade, mine,
   enumerate, plausible, tactics, lookup, external (v1 stub), or stop.
   Cycle ≥2 marks exhausted methods and pre-selects Replan's
   recommendation.
2. **Step 2 — Per-method configuration.** Method-specific prompts (e.g.,
   for `enumerate`: range type, start, end, atom tactic; for
   `decide-cascade`: include `native_decide`?).

Pre-fill order for any prompted value: (1) Replan's recommendation for
this cycle, (2) the method's default.

See [disprove-engine.md § Phase 1 — Plan](../skills/lean4/references/disprove-engine.md#phase-1--plan)
for the full menu and per-method prompts.

## Actions

Six phases — see [disprove-engine.md](../skills/lean4/references/disprove-engine.md) for full mechanics.

### Phase 1: Plan

See [disprove-engine.md § Phase 1 — Plan](../skills/lean4/references/disprove-engine.md#phase-1--plan). Cycle 1 resolves the TARGET, normalizes shape, and prints the Search-Space Estimate; every cycle prompts Step 1 (method) + Step 2 (config), with Replan's recommendations pre-filling cycle ≥2.

### Phase 2: Work

See [disprove-engine.md § Phase 2 — Work](../skills/lean4/references/disprove-engine.md#phase-2--work). Run the chosen method, pre-screen candidates via `lean_multi_attempt`, record outcomes (`certified` / `near-miss` / `exhausted-no-witness` / `no-candidate`).

### Phase 3: Checkpoint

See [disprove-engine.md § Phase 3 — Checkpoint](../skills/lean4/references/disprove-engine.md#phase-3--checkpoint). On certification, append `T_counterexample` via `disprove_emit_artifact.py`, then run `lake env lean <target-file>` from the project root.

**Commit prompt** (when `--commit=ask`):

```
Commit T_counterexample to <file>? [yes / yes-all / no / never]
```

- `yes` — commit this cycle's artifact; prompt again next cycle.
- `yes-all` — switch to `auto` for the rest of the session.
- `no` — unstage; don't commit this cycle.
- `never` — switch to `never` for the rest of the session.

### Phase 4: Review

See [disprove-engine.md § Phase 4 — Review](../skills/lean4/references/disprove-engine.md#phase-4--review). Classifies the cycle's outcome and captures the residual error signature on near-misses for Replan.

### Phase 5: Replan

See [disprove-engine.md § Replan Rules](../skills/lean4/references/disprove-engine.md#replan-rules). Widens the just-tried method's parameters (e.g., doubles `enumerate`'s range end) or recommends a different method based on Review. If no widening lever remains, the cycle is marked stuck.

### Phase 6: Continue / Stop

See [disprove-engine.md § Phase 6 — Continue / Stop](../skills/lean4/references/disprove-engine.md#phase-6--continue--stop). Always prompts the user:

```
Cycle N complete (outcome: <outcome>).
Replan recommends: <method> with <config>.
- [continue] — run cycle N+1 with Replan's recommendation
- [stop]     — accept the current outcome and exit
- [adjust]   — change Replan's recommendation before the next cycle
```

## Stop Conditions

The cycle-tracker enforces budgets at each `tick` boundary. The session
stops on the **first** of:

1. **FALSE outcome** — a cycle produced a certified counterexample
2. **Max stuck cycles** — `--max-stuck-cycles` consecutive stuck cycles
3. **Max cycles** — `--max-cycles` total cycles run
4. **Max runtime** — wall-clock budget reached (best-effort, checked at cycle boundaries)
5. **User stop** — user chose `stop` at a Continue/Stop prompt

## Disprove Summary

When the command stops (any branch), emit:

```text
## Disprove Summary

**Outcome:** [FALSE | WITNESS_UNCERTIFIED | INCONCLUSIVE]

| Metric | Value |
|--------|-------|
| Target | <resolved descriptor> |
| Witness | <Lean term or "—"> |
| Artifact theorem | T_counterexample (or "—") |
| Artifact file | <path or "—"> |
| Build gate | passed | failed | skipped |
| Cycles run | <N> |
| Stuck cycles | <N> |
| Time elapsed | <T> |

**Per-cycle attempts:**

| # | Method | Config | Outcome |
|---|--------|--------|---------|
| 1 | <method> | <method-specific key=value list> | <outcome> |
| 2 | <method> | <...> | <outcome> |
| ... | | | |

The `Config` column mirrors each method's Step 2 prompts — for example
`native_decide=off` for `decide-cascade`; `range=[a,b), atom=<tactic>`
for `enumerate`; `samples=N, seed=<int>` for `plausible`. See
[disprove-engine.md § Step 2 — Per-Method Configuration](../skills/lean4/references/disprove-engine.md#step-2--per-method-configuration).
A method that fired (produced `certified`) is the row whose `Outcome` is
`certified`; "methods attempted" is just the column.

[FALSE]
  Counterexample certified.
  Recommended: /lean4:checkpoint to commit.

[WITNESS_UNCERTIFIED]
  Candidate witness w0 = <value>; Lean error <signature>.
  Recommended: /lean4:prove <target> --deep=stuck, or rerun and pick
               `tactics` in Step 1, or enable native_decide in Step 2.

[INCONCLUSIVE]
  Coverage: <e.g. enumerate covered [0, 128); plausible sampled 200>
  Stop reason: max-cycles | max-stuck | max-runtime | user-stop
  Recommended: rerun with --max-cycles=<higher> and pick `lookup` from the
               Step 1 menu, or hand off to /lean4:prove for a positive proof
               attempt.
```

## Safety

- **Append-only.** Never rewrite an existing `theorem T : P := by sorry`
  declaration to `: ¬ P`. The artifact emitter refuses to modify existing
  declarations.
- **No `native_decide` without opt-in.** Each cycle's Step 2 for the
  `decide-cascade` method asks whether to enable `native_decide` (it adds
  the `Lean.ofReduceBool` axiom and is audit-worthy). Default off.
- **No `FALSE` without compile gate.** `lean_multi_attempt` is the cheap
  pre-screen; only `lake env lean <path>` from the project root licenses
  the `FALSE` claim.
- **Line width.** Follow mathlib 100-char line width — do not wrap lines at 80 when they fit within 100.

## See Also

- `/lean4:prove` — Guided cycle-by-cycle proving
- `/lean4:autoprove` — Autonomous multi-cycle proving
- `/lean4:checkpoint` — Manual save point
- [Disprove Engine](../skills/lean4/references/disprove-engine.md) — Phase mechanics, Step 1 / Step 2 menus, Per-Shape Recipes, Replan rules
- [Examples](../skills/lean4/references/command-examples.md#disprove)
