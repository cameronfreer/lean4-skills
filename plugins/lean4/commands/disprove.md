---
name: disprove
description: Guided counterexample search with certified refutation
user_invocable: true
argument-hint: '<File.lean:LINE | Namespace.theoremName> [--max-cycles=N] [--max-stuck-cycles=N] [--max-runtime=DURATION] [--commit=auto|ask|never] [--knowledge-search-budget=N]'
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
`lake env lean` with no `sorry` or `admit` **and** its axiom set is within the
allowed whitelist (`propext`, `Classical.choice`, `Quot.sound`; plus
`Lean.ofReduceBool` only under an explicit `native_decide` opt-in this cycle).
Fast witnesses and informal heuristics are *hypotheses* until Lean certifies
them. See
[disprove-engine.md § Prime Directive](../skills/lean4/references/disprove-engine.md#prime-directive--epistemological-strictness).

`FALSE` is licensed by a **checked closed term of type `¬ TARGET`**, not by the
artifact's surface form: `T_counterexample` may be a direct `¬ TARGET` theorem **or**
a witness theorem whose named per-shape wrapper (also axiom-checked) derives
`¬ TARGET`.

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

**Runtime requirement:** `/lean4:disprove` requires **Python 3.11+** — its method
registry loader (`lib/disprove_methods.py`) uses the stdlib `tomllib` parser. The rest
of the lean4 plugin targets Python 3.10+. On an older interpreter the command fails fast
with a clear "requires Python 3.11+" error rather than an opaque `ImportError`.

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
| target | Yes | — | `File.lean:LINE` or `Namespace.theoremName`. Inline Props not supported in v1. A qualified name containing a prime (`'`) or an escaped `«…»` identifier is not accepted in v1 — use a `File.lean:LINE` target for that declaration. |
| --max-cycles | No | 3 | Max widening passes. Each cycle picks one method via the Step 1 menu and configures its parameters via the Step 2 menu. |
| --max-stuck-cycles | No | 2 | Bail after this many consecutive cycles where the next cycle's Step 1 menu has no non-failed `(family, config)` pair to place in its top 3 (no remaining widening lever). |
| --max-runtime | No | 5m | Best-effort wall-clock session budget across all cycles. |
| --negation-policy | No | counterexample-only | Reserved for future salvage modes; locked in v1. |
| --commit | No | ask | Per-cycle Checkpoint behavior. `ask` prompts before each commit; `auto` commits without prompting; `never` skips committing (leave staging to `/lean4:checkpoint`). |
| --knowledge-search-budget | No | 3 | Max Step 0 (knowledge search) visits per cycle. Cycle 1 always runs Step 0 once; later cycles only re-enter Step 0 if their Step 1 menu surfaces `knowledge search` and the user picks it. After the Nth visit completes, `knowledge search` is disabled in that cycle's Step 1 menu. |

Per-method parameters (e.g. enumerate's range, `native_decide` opt-in,
sample count for `plausible`) are surfaced as **dynamic Step 2
candidates** in each cycle's Plan phase, not top-level flags. See
[disprove-engine.md § Step 2 — Config Menu](../skills/lean4/references/disprove-engine.md#step-2--config-menu).

## Actions

Six phases — see [disprove-engine.md](../skills/lean4/references/disprove-engine.md) for full mechanics.

### Phase 1: Plan

During Plan, the cycle builds three dynamic menus from accumulated evidence, the
Target Profile, and the prior cycle's Review:

- **Step 0 — Knowledge Search** ([engine](../skills/lean4/references/disprove-engine.md#step-0--knowledge-search-menu))
- **Step 1 — Method** ([engine](../skills/lean4/references/disprove-engine.md#step-1--method-menu))
- **Step 2 — Config** ([engine](../skills/lean4/references/disprove-engine.md#step-2--config-menu))

Keep only the selected entries and their rationale in the cycle record. Cycle 1
also resolves the TARGET, normalizes shape, builds the Target Profile, and runs
Step 0 once; cycle ≥2 re-enters Step 0 only if Step 1 surfaces `knowledge search`
and the user picks it. A qualified-name target must resolve to a **writable source
file** (the declaration's file); if it resolves only to a read-only dependency, the
session refuses before Phase 2 (use a `File.lean:LINE` target instead).

Full menu mechanics, invariants, and the findings schema live in
[disprove-engine.md § Phase 1 — Plan](../skills/lean4/references/disprove-engine.md#phase-1--plan).

### Phase 2: Work

See [disprove-engine.md § Phase 2 — Work](../skills/lean4/references/disprove-engine.md#phase-2--work). Run the chosen method and pre-screen candidates via `lean_multi_attempt`; Work yields a pre-screen-passing candidate (or none). The cycle outcome (`certified` / `near-miss` / `exhausted-no-witness` / `no-candidate`) is finalized by the Phase 3 gate, not in Work.

### Phase 3: Checkpoint

See [disprove-engine.md § Phase 3 — Checkpoint](../skills/lean4/references/disprove-engine.md#phase-3--checkpoint). On a **pre-screen-passing candidate**, open a transaction (`txn=$(${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/disprove_artifact_txn.py" begin)`) and append `T_counterexample` via its `append --txn=$txn --role=artifact` subcommand (witness shapes also append the gate-only `*_negates_target` with `--role=gate`), run `lake env lean <target-file>` from the project root, then **inspect the axioms of the declaration carrying `¬ TARGET`** (`T_counterexample` for direct shapes, `T_counterexample_negates_target` for witness shapes) via `lean_verify` / `#print axioms`. Report `FALSE` only if it typechecks **and** that declaration's axioms ⊆ `{propext, Classical.choice, Quot.sound}` (plus `Lean.ofReduceBool` only under an explicit `native_decide` opt-in this cycle): on `FALSE`, `drop-role --txn=$txn --role=gate` (witness shapes) and commit only `T_counterexample`. Otherwise `rollback --txn=$txn` (reverts every declaration appended this cycle), distinguishing the non-FALSE outcomes: a **typecheck failure** is a `near-miss` cycle outcome (capture the error signature for the next cycle), while a **non-whitelisted axiom or inconclusive axiom inspection** is `WITNESS_UNCERTIFIED`. `<target-file>` is the resolved source file — for a qualified-name target, the declaration's **writable** source file from Phase 1 (disprove refuses if it resolves only to a read-only dependency).

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
| Axiom gate | <axioms listed, e.g. "propext, Classical.choice, Quot.sound" \| failed \| skipped> |
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
  - If already committed (`--commit=auto`, or `ask` accepted): committed as
    `disprove: T_counterexample — cycle N` (see `git log -1`).
  - If not committed (`--commit=never`, or `ask` declined): Recommended:
    /lean4:checkpoint to commit.

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

- **Append-only, transactional.** Never rewrite an existing
  `theorem T : P := by sorry` declaration to `: ¬ P`. Cycle artifacts are written
  through `$LEAN4_SCRIPTS/disprove_artifact_txn.py` (over the collision-safe
  `$LEAN4_SCRIPTS/disprove_emit_artifact.py`): each append is wrapped in txn-id markers and
  refuses to modify or clobber an existing declaration; the cycle's writes are
  reverted as a unit via `rollback` / `drop-role` on failure or wrapper drop.
- **No `native_decide` without opt-in (any method).** `native_decide`
  defaults off and is not in the `tactics` method's default list. Anywhere
  it can appear — `decide-cascade`'s `native_decide=on`, a custom `tactics`
  list, or a `custom-config` — it is the same explicit, audit-worthy opt-in:
  the cycling LLM surfaces it as such in Step 2 and records it in the
  cycle's evidence. Enabling admits the `Lean.ofReduceBool` axiom, which the
  compile/axiom gate then permits only for that cycle.
- **No `FALSE` without compile gate + axiom gate.** `lean_multi_attempt` is the
  cheap pre-screen; `FALSE` requires `lake env lean <path>` from the project root
  to typecheck (no `sorry`/`admit`) **and** the `¬ TARGET` declaration's axioms
  (`T_counterexample`, or `T_counterexample_negates_target` for witness shapes) ⊆
  `{propext, Classical.choice, Quot.sound}` (plus `Lean.ofReduceBool` only under
  an explicit `native_decide` opt-in). A non-whitelisted axiom, or inconclusive
  axiom inspection, → revert any declarations appended this cycle and report
  `WITNESS_UNCERTIFIED`.
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
- [Implementation Status](../skills/lean4/references/disprove-engine.md#implementation-status) — what is deterministic script vs model-mediated vs deferred
- [Method Registry](../lib/data/disprove_methods.toml) — Stable method ids, parameter schemas, cost classes
- [Examples](../skills/lean4/references/command-examples.md#disprove)
- [Benchmark](https://github.com/jancio/l4s-disprove-benchmark) — 16-target evaluation suite (certified refutations) from the disprove paper

## Citation

The `/lean4:disprove` skill is described in:

```bibtex
@inproceedings{ondras2026disprove,
  title     = {Disprove Skill: Certified Counterexample Search for {AI}-Assisted Formal Mathematics},
  author    = {Jan Ondras and Cameron Freer},
  booktitle = {3rd AI for Math Workshop: Toward Self-Evolving Scientific Agents},
  note      = {Workshop at ICML 2026},
  year      = {2026},
  url       = {https://openreview.net/forum?id=5ck1jRE65S}
}
```
