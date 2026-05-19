---
name: disprove
description: Search for counterexamples and produce a certified Lean refutation
user_invocable: true
argument-hint: '<File.lean:LINE | Namespace.theoremName> [--max-cycles=N] [--max-stuck-cycles=N] [--max-runtime=DURATION] [--negation-policy=counterexample-only] [--commit=auto|ask|never] [--knowledge-search-budget=N]'
---

# Lean4 Disprove

Search for a counterexample to a target proposition and, when possible,
produce a Lean proof of its negation. Reports `FALSE` only when Lean
certifies the refutation; otherwise `WITNESS_UNCERTIFIED` (a candidate was
found but Lean refused to certify it) or `INCONCLUSIVE` (no candidate
found within budgets).

`/lean4:disprove` is **always interactive** — disprove is an exploratory
search, and the workflow generates three dynamic menus each cycle
(Step 0 knowledge search, Step 1 method, Step 2 config) seeded by
accumulated evidence and the Target Profile.

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
   numeric values for `--max-cycles`, `--max-stuck-cycles`,
   `--max-runtime`, and
   `--max-knowledge-search-per-cycle=<--knowledge-search-budget>`.
   Disprove has no deep mode in v1; omit the deep args and let the
   tracker default them (they remain inert because disprove never
   calls `can-deep` / `deep`). A failed init (exit 2) is a startup
   validation error — do not proceed.
4. The cycle-tracker state file is the single source of truth for session
   counters. Read counters from `tick`/`status` output, not from
   conversational memory.

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| target | Yes | — | `File.lean:LINE` or `Namespace.theoremName`. Inline Props not supported in v1. |
| --max-cycles | No | 3 | Max widening passes. Each cycle picks one method via the Step 1 menu and configures its parameters via the Step 2 menu. |
| --max-stuck-cycles | No | 2 | Bail after this many consecutive cycles where the next cycle's Step 1 menu has no non-failed `(family, config)` pair to place in its top 3 (no remaining widening lever). |
| --max-runtime | No | 5m | Best-effort wall-clock session budget across all cycles. |
| --negation-policy | No | counterexample-only | v1: locked. Reserved for future `with-salvage`. |
| --commit | No | ask | Per-cycle Checkpoint behavior. `ask` prompts before each commit; `auto` commits without prompting; `never` skips committing (leave staging to `/lean4:checkpoint`). |
| --knowledge-search-budget | No | 3 | Max Step 0 (knowledge search) visits per cycle. Cycle 1 always runs Step 0 once; later cycles only re-enter Step 0 if their Step 1 menu surfaces `knowledge search` and the user picks it. After the Nth visit completes, `knowledge search` is disabled in that cycle's Step 1 menu. |

Per-method parameters (e.g. enumerate's range, `native_decide` opt-in,
sample count for `plausible`) are surfaced as **dynamic Step 2
candidates** in each cycle's Plan phase, not top-level flags. See
[disprove-engine.md § Step 2 — Config Menu](../skills/lean4/references/disprove-engine.md#step-2--config-menu).

## Plan-Phase Menus (Step 0 / 1 / 2)

Every cycle's Plan phase generates **dynamic menus** seeded by accumulated
Step 0 evidence + the Target Profile + the prior cycle's Review:

- **Step 0 — Knowledge Search Menu.** Runs once in Cycle 1 by default;
  later cycles re-enter only if Step 1 surfaces `knowledge search` and
  the user picks it. The cycling LLM proposes a menu of search tasks
  (multi-select; lean/local/web rows, and `[custom]` and
  `[llm]`; all pre-selected); each row shows the source/tool, tier tag (`[lean]`
  / `[local]` / `[web]`), and executable query the LLM derives from the
  TARGET (for `[custom]`, the LLM interprets the user's free-form
  intent instead). The user approves / edits / reduces before selected
  rows fire. Cap = `--knowledge-search-budget`.
- **Step 1 — Method Menu.** The cycling LLM proposes 3–10 method
  candidates each cycle (single-select), informed by accumulated
  Step 0 evidence, prior-cycle outcomes, and the Target Profile. It
  picks which of the six registry families to surface and how many
  entries per family (e.g. two `enumerate` rows with different ranges).
  Per-entry display: stable `family` id, LLM-emitted free-text `label`,
  one-line description, reasoning, cost class. Always-present extras:
  `knowledge search` (disabled after the cycle's Nth Step 0 visit) and
  `custom method` (free-form description; the LLM maps it to the
  nearest registry `family` and synthesizes a config).
- **Step 2 — Config Menu.** If Step 1 picked `knowledge search`,
  Step 2 is a multi-select of Step 0 items and returns to Step 0
  (counting against the visit cap). Otherwise: the cycling LLM
  proposes 3–10 candidate configs for the picked family
  (single-select). Each candidate is a concrete instantiation of the
  picked family's params (not a re-ordering of pre-defined configs),
  informed by the family's parameter schema + Step 0 digest +
  prior-cycle outcomes + Target Profile. Always-present extra:
  `custom-config` (free-text, schema-validated against the family's
  params).

The Method Registry is the canonical vocabulary the cycling LLM draws
from — see [`lib/data/disprove_methods.toml`](../lib/data/disprove_methods.toml)
and [disprove-engine.md § Method Registry](../skills/lean4/references/disprove-engine.md#method-registry).

## Actions

Six phases — see [disprove-engine.md](../skills/lean4/references/disprove-engine.md) for full mechanics.

### Phase 1: Plan

See [disprove-engine.md § Phase 1 — Plan](../skills/lean4/references/disprove-engine.md#phase-1--plan). Cycle 1 resolves the TARGET, normalizes shape, builds the Target Profile, runs Step 0 once, and presents the Step 1 + Step 2 menus. Cycle ≥2 re-enters Step 0 only if Step 1 surfaces `knowledge search` and the user picks it.

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

For provenance, the commit message body includes the relevant audit
field from the cycle's Phase 5 evidence record:

- If the cycle's method was `custom method`:
  `derived-from-custom="<user text>"`.
- If the family was `external`: `external_script_path="<path under
  $LEAN4_SESSION_DIR/scripts/>"` (the script remains for re-run /
  audit).
- If the entry was `[verify-known-cex]`:
  `derived-from-verify-known-cex="<source_url or repo-relative path>"`.

### Phase 4: Review

See [disprove-engine.md § Phase 4 — Review](../skills/lean4/references/disprove-engine.md#phase-4--review). Classifies the cycle's outcome and captures the residual error signature on near-misses for the next cycle's menus.

### Phase 5: Accumulate

See [disprove-engine.md § Phase 5 — Accumulate](../skills/lean4/references/disprove-engine.md#phase-5--accumulate). Appends the cycle's `(family, config, outcome, near-miss_signature)` to session evidence. No hardcoded recommendation table — the next cycle's Step 0 / Step 1 / Step 2 menus absorb the recommendation logic. A cycle is **stuck** when it produced no `certified` outcome AND the next cycle's Step 1 menu has no non-failed `(family, config)` pair to place in its top 3.

### Phase 6: Continue / Stop

See [disprove-engine.md § Phase 6 — Continue / Stop](../skills/lean4/references/disprove-engine.md#phase-6--continue--stop). Always prompts the user:

```
Cycle N complete (outcome: <outcome>).
Next cycle's Step 1 preview: <top-ranked entry's family + config>.
- [continue] — run cycle N+1 with the preview pre-selected at Step 1
- [stop]     — accept the current outcome and exit
```

To override the preview, pick a different entry (any registry family,
`knowledge search`, or `custom method`) when the next cycle's Step 1
menu opens.

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

| # | Method (family) | Config | Outcome | URL |
|---|-----------------|--------|---------|-----|
| 1 | <family> | <key=value list> | <outcome> | <URL or —> |
| 2 | <family> | <...> | <outcome> | <URL or —> |
| ... | | | | |

The `Method (family)` column shows the stable id from the registry; the
`Config` column mirrors the cycle's Step 2 choices — for example
`native_decide=off` for `decide-cascade`; `range=[a,b), atom=<tactic>`
for `enumerate`; `samples=N, seed=<int>` for `plausible`. The `URL`
column is populated **only** for cycles whose certifying witness was
elevated via `[verify-known-cex]` (the URL is the verified `source_url`
of the originating Step 0 finding); all other cycles show `—`. See
[disprove-engine.md § Step 2 — Config Menu](../skills/lean4/references/disprove-engine.md#step-2--config-menu).

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
  Recommended: rerun with --max-cycles=<higher> and pick `knowledge
               search` in Step 1 (widens with fresh evidence), or hand
               off to /lean4:prove for a positive proof attempt.
```

## Safety

- **Append-only.** Never rewrite an existing `theorem T : P := by sorry`
  declaration to `: ¬ P`. The artifact emitter refuses to modify existing
  declarations.
- **No `native_decide` without opt-in.** The cycling LLM surfaces
  `native_decide=on` in the Step 2 menu as an explicit opt-in candidate
  (`audit_worthy=true` in the registry). Enabling adds the
  `Lean.ofReduceBool` axiom and is audit-worthy. Default off.
- **No `FALSE` without compile gate.** `lean_multi_attempt` is the cheap
  pre-screen; only `lake env lean <path>` from the project root licenses
  the `FALSE` claim.
- **No Step 0 findings without `source_url`.** Findings produced without
  a citable URL or repo-relative path are dropped at write time. Web
  counterexample candidates require `WebFetch` verification before
  elevation to `[verify-known-cex]`. If `WebFetch` is unavailable in the
  host, web findings are dropped, not elevated.
- **Line width.** Follow mathlib 100-char line width — do not wrap lines at 80 when they fit within 100.

## See Also

- `/lean4:prove` — Guided cycle-by-cycle proving
- `/lean4:autoprove` — Autonomous multi-cycle proving
- `/lean4:checkpoint` — Manual save point
- [Disprove Engine](../skills/lean4/references/disprove-engine.md) — Phase mechanics, Step 0 / 1 / 2 menus (Knowledge Search / Method / Config), Per-Shape Recipes
- [Method Registry](../lib/data/disprove_methods.toml) — Stable method ids, parameter schemas, cost classes
- [Examples](../skills/lean4/references/command-examples.md#disprove)
