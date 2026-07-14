# Disprove Engine Reference

> Disprove-specific specialization of [cycle-engine.md](cycle-engine.md).
> Inherits the shared 6-phase cycle vocabulary
> (Plan → Work → Checkpoint → Review → Accumulate → Continue/Stop), the
> LSP-first protocol, the compile-gate contract, and the
> [Falsification Artifacts](cycle-engine.md#falsification-artifacts)
> templates. Adds disprove-only mechanics: the
> [Method Registry](#method-registry) (data file), the Phase 1 menus
> (Step 0 — Knowledge Search Menu, Step 1 — Method Menu, Step 2 —
> Config Menu), the Per-Shape Recipes, and the per-cycle Accumulate
> state update.
>
> `/lean4:disprove` is always interactive: the workflow prompts the user
> in each cycle's Plan phase to (re-)run Step 0 when applicable, then
> choose a search method from a dynamic Step 1 menu and configure it via
> a dynamic Step 2 menu.

## Contents

- [Prime Directive — Epistemological Strictness](#prime-directive--epistemological-strictness)
- [Implementation Status](#implementation-status)
- [Six-Phase Cycle](#six-phase-cycle)
- [Phase 1 — Plan](#phase-1--plan)
  - [Target Resolution Flow](#target-resolution-flow)
  - [Shape Normalization](#shape-normalization)
  - [Target Profile](#target-profile)
  - [Cycle-Tracker init](#cycle-tracker-init)
  - [Step 0 — Knowledge Search Menu](#step-0--knowledge-search-menu)
  - [Step 1 — Method Menu](#step-1--method-menu)
  - [Step 2 — Config Menu](#step-2--config-menu)
- [Phase 2 — Work](#phase-2--work)
  - [External family — Work-phase execution](#external-family--work-phase-execution)
  - [Method Registry](#method-registry)
- [Phase 3 — Checkpoint](#phase-3--checkpoint)
  - [Per-Shape Recipes](#per-shape-recipes)
- [Phase 4 — Review](#phase-4--review)
- [Phase 5 — Accumulate](#phase-5--accumulate)
  - [Stuck Definition for Disprove](#stuck-definition-for-disprove)
- [Phase 6 — Continue / Stop](#phase-6--continue--stop)
- [Disprove Summary](#disprove-summary)
- [Safety](#safety)

## Prime Directive — Epistemological Strictness

`/lean4:disprove` reports `REFUTED` **only** when it produces a Lean term of
the negation that typechecks under `lake env lean` without `sorry` or
`admit` **and** whose axiom set is within the allowed whitelist
(`propext`, `Classical.choice`, `Quot.sound`; plus `Lean.ofReduceBool`
**only** when `native_decide` was explicitly opted in this cycle — see
[Phase 3](#phase-3--checkpoint)). Fast witnesses and informal heuristics
are *hypotheses* until Lean certifies them. Anything weaker — including a
term that typechecks but pulls in a non-whitelisted axiom — is reported as
`WITNESS_UNCERTIFIED` or `INCONCLUSIVE`. This invariant is non-negotiable.

Certification is by the **term, not its surface form**: `REFUTED` is licensed when
Lean checks a **closed** term of type `¬ TARGET` (no `sorry`/`admit`, axioms ⊆
whitelist). The emitted `T_counterexample` artifact may be that `¬ TARGET` theorem
directly, **or** a witness theorem from which `¬ TARGET` is derived by a named
per-shape wrapper that is itself typecheck- and axiom-checked (see
[Per-Shape Recipes](#per-shape-recipes) and [Phase 3](#phase-3--checkpoint)).

## Implementation Status

What in this reference is a deterministic script vs. performed by the cycling LLM
(LSP/judgment) vs. deferred. Honest about the script-vs-LSP boundary.

| Capability | Status | Where |
|------------|--------|-------|
| Target classification + grep source-resolution + path-class/writable + dependency refusal | **implemented (deterministic)** | `disprove_target_profile.py` (grep is non-authoritative; LLM confirms via `lean_declaration_file`) |
| Shape / decidability / type / free-vars / candidate-grid | **model-mediated (LSP)** | LLM fills the profile's `_lsp_filled` fields |
| Method registry (6 families: schemas, shapes, costs) | **implemented (deterministic)** | `lib/data/disprove_methods.toml` + `lib/disprove_methods.py` |
| Method applicability + availability filter | **implemented (deterministic)** | `disprove_method_probe.py` (registry + profile + `shutil.which`) |
| Step 0/1/2 menu proposal + evidence-driven ranking | **model-mediated (LLM)** | cycling LLM (no hardcoded escalation table) |
| Knowledge search + WebFetch verification | **model-mediated (LLM)** | advisory; never bypasses the kernel gate |
| Collision-safe artifact writer | **implemented (deterministic)** | `disprove_emit_artifact.py` |
| Transactional append / drop-gate / rollback | **implemented (deterministic)** | `disprove_artifact_txn.py` (txn-id markers) |
| Compile gate (`lake env lean`) + axiom-whitelist gate | **model-mediated (tool calls)** | Checkpoint runs `lake env lean` + `#print axioms` / `lean_verify` |
| Cycle tracker / stop budgets | **implemented (deterministic)** | `lib/scripts/cycle_tracker.sh` |
| Artifact naming `T_counterexample` | **implemented (fixed, v1)** | schematic, one artifact per file (see note) |
| Target-derived artifact names | **deferred (future)** | collision gate already makes the fixed name safe |
| Capability-escalation benchmark + certified-term fixtures | **released (external repo)** | [`l4s-disprove-benchmark`](https://github.com/jancio/l4s-disprove-benchmark) — 16 targets (15 false + 1 true control), paper §5 |
| External-SMT (Z3) deterministic fixture | **released (external repo)** | `SmtBad.lean` in [`l4s-disprove-benchmark`](https://github.com/jancio/l4s-disprove-benchmark) (Z3 model (−4,3), kernel-rechecked) |

**`T_counterexample` is schematic and fixed in v1.** A file holds one disprove
artifact under this name; the collision gate (and the transaction layer) refuse a
conflicting reuse. Target-derived names (`<decl>_counterexample`) are deferred.

## Six-Phase Cycle

```
Plan → Work → Checkpoint → Review → Accumulate → Continue/Stop
```

A cycle is a **widening pass** over the same target. Each cycle picks one
method (via the Step 1 menu) with one config (via the Step 2 menu) and
either certifies a counterexample or appends the cycle's outcome to
session evidence so the next cycle's menus can re-rank.

| Phase | Disprove-specific behavior |
|-------|----------------------------|
| 1. Plan | Cycle 1 resolves TARGET, normalizes shape, builds the Target Profile, runs Step 0 (Knowledge Search) once. Every cycle: Step 1 menu + Step 2 menu. Later cycles re-enter Step 0 only if Step 1 picks `knowledge search`. |
| 2. Work | Run the chosen method with the chosen config. Pre-screen candidates via `lean_multi_attempt`. |
| 3. Checkpoint | If Work produced a **pre-screen-passing candidate**: append `T_counterexample`, run `lake env lean` + axiom check (⊆ whitelist) → `certified` (`REFUTED`) only if both pass, else revert hunk → `near-miss`/`WITNESS_UNCERTIFIED`; stage + commit per `--commit`. If no candidate: no artifact. |
| 4. Review | Classify the cycle's outcome (certified / near-miss / exhausted / no-candidate). Capture error signatures. |
| 5. Accumulate | Append `(family, config, outcome, near-miss_signature)` to session evidence. No hardcoded recommendation table — the next cycle's menus absorb the logic. |
| 6. Continue/Stop | Always prompt the user: `continue / stop`. |

## Phase 1 — Plan

Cycle 1's Plan does the full one-time setup (Target Resolution Flow,
Shape Normalization, Target Profile, Cycle-Tracker init, then Step 0)
before the Step 1 + Step 2 menus. Cycle ≥2 skips the setup sub-sections
(TARGET, shape, Target Profile, tracker are reused) and enters Step 1
directly; Step 0 is re-entered only when Step 1 surfaces `knowledge
search` and the user picks it (subject to the per-cycle visit cap).

Each of Step 0, Step 1, and Step 2 is one inline call to the cycling
LLM (no subagent): the LLM proposes a menu of candidates, the user
reviews and approves (with edit / reduce affordances), and the selected
items fire. **Pre-flight context** (per
[cycle-engine.md § Pre-flight Context](cycle-engine.md#pre-flight-context-for-subagent-dispatch)):
Target Profile + prior cycle's Review block + the structured Step 0
digest are pre-loaded into the cycling LLM's input each cycle; the
cross-cycle digest is cached so only new evidence is re-integrated.

### Target Resolution Flow

```text
target = (validated-invocation block) | positional argument
        ↓
lean4-skills-disprove-target-resolve → {kind, file?, line?, name?}
        ↓
   file-line ──→ lean_diagnostic_messages(file)
              → lean_goal(file, line)         ← extracts the Prop
              → lean_hover_info(file, line, col)  ← if goal is empty
        ↓
   qualified-name ──→ lean_local_search(name) → lean_hover_info on hit
                   → lean_declaration_file(name)  ← source file + line of the decl
                   → fallback: one lean_leansearch query
        ↓
   if still no type:
              → lean_run_code with `#check @<name>` (or `#check (<expr>)`)
              → parse the diagnostic for the inferred type
```

The resolved TARGET is reused for the entire session — subsequent cycles
do not re-resolve.

**LSP-call budget for target resolution:** cap at 4 LSP calls and ~10s
wall-clock. If the type is still unknown after that, treat as a startup
validation failure and refuse the session rather than entering Phase 2
with a partially-resolved target. (Mirrors prove's "up to 3 LSP search
tools (~30s)" planning-phase budget; see `commands/prove.md:93`.)

**Qualified-name targets must resolve to a writable project source file.**
For a `Namespace.name` target, resolution must yield not just the inferred
type but the declaration's **source file + line** (via `lean_declaration_file`,
or the `lean_local_search` hit's location). That resolved file is the
`<target-file>` Phase 3 appends `T_counterexample` to and runs `lake env lean`
against — the artifact is checked in the target's real source context. If the
declaration resolves only to a **read-only dependency** (e.g. under `.lake/` or
mathlib) or no source file can be located, **refuse before Phase 2** with:
*"qualified-name target resolved, but no writable source file is available; use
a `File.lean:LINE` target in a writable file."* There is no silent scratch-file
fallback in v1.

The **deterministic** half of this — target classification, best-effort grep
resolution of a qualified name to a *single unambiguous* project source location
(0 or ≥2 hits → `needs_lsp_resolution`; grep is non-authoritative), `path_class`
(project vs read-only `dependency`) + `writable`, and the dependency-path refusal
— is produced by `lean4-skills-disprove-target-profile` as one JSON envelope.
The cycling LLM then fills the LSP/kernel fields it lists under `_lsp_filled`
(`shape`, `decidable`, `type`, `free_vars`, `candidate_grid`) and confirms an
ambiguous/unresolved name via `lean_declaration_file`. (A merely read-only
*project* file is reported `writable:false` but not refused here — the artifact
emitter fails at append time.)

**v1 grammar limitation.** Qualified-name targets containing a prime (`'`, e.g.
`Nat.foo'`) or an escaped `«…»` identifier are **not accepted in v1** (the shared
tokenizer/parser rejects them before resolution). Target such declarations by
`File.lean:LINE` instead. Broader name grammar is deferred.

### Shape Normalization

Strip a leading prefix of binders from the inferred type and reclassify
the body. The seven canonical shapes:

| # | Shape | Disproof goal | Default method family (cycle-1 LLM hint) |
|---|-------|---------------|---------------------------------------------|
| 1 | `∀ x : α, P x` | `∃ x, ¬ P x` | decide-cascade → mine → enumerate |
| 2 | `∀ x, P x → Q x` | `∃ x, P x ∧ ¬ Q x` | decide-cascade → mine → enumerate |
| 3 | `∃ x : α, P x` | `∀ x, ¬ P x` | decide-cascade (needs `Fintype α`, `DecidablePred P`) |
| 4 | `P ∧ Q` | `¬ P ∨ ¬ Q` | recurse on each conjunct |
| 5 | `P ∨ Q` | `¬ P ∧ ¬ Q` | recurse on both |
| 6 | `a = b` / arithmetic ineq | `a ≠ b` / `¬ (a ≤ b)` | decide-cascade (norm_num / omega) |
| 7 | Decidable atom `P` | `¬ P` | decide-cascade |

Mixed-quantifier prefixes (`∀ n m, …`) peel one layer at a time;
re-classify after each `intro`.

### Target Profile

The Target Profile is the one-time, cycle-1 summary the cycling LLM
reads at every Step 0 / Step 1 / Step 2 invocation. It carries only
LSP/kernel facts.

```
Target Profile
  shape          : <one of the seven from Shape Normalization>
  free_vars      : <name : type (fintype_size?)>, ...
  fintype_size   : <int | ∞>
  decidable      : yes | no | unknown
  candidate_grid : <bound string for display>   e.g. "Fin 8 × Fin 8 = 64",
                                                       "[0, 64) default window",
                                                       "atomic"
```

**`decidable` probe** — a single `lean_run_code` `inferInstance` check
per the resolved shape, capped at 3s wall-clock:

| Shape | Probe |
|-------|-------|
| 1, 2  | `#check (inferInstance : Decidable (∀ x : α, P x))` (or the curried `P x → Q x` form) |
| 3     | `#check (inferInstance : Decidable (∃ x : α, P x))` |
| 4, 5  | Probe each component separately; `decidable=yes` iff both probes pass |
| 6, 7  | `#check (inferInstance : Decidable <atom>)` |

Outcomes:

- `yes` — probe succeeded; the decide-family `must-appear-in-top-3`
  menu invariant (see Step 1) is in force.
- `no` — probe reports `failed to synthesize Decidable …`.
- `unknown` — probe timed out, the file failed to load, or elaboration
  aborted for non-synthesis reasons. Treated as `no` for menu purposes
  (does not force the decide-family entry), but recorded distinctly for
  audit so the user sees the probe was inconclusive rather than negative.

**`candidate_grid`** — a derived, human-readable bound, not a hard search
budget. Used to ground the user's intuition during Step 1; the actual
search budget is per-method (`enumerate.range_end`, `plausible.samples`,
etc.). Examples per shape:

- Shape 1 over `Fin n`: `"Fin n = <n>"`.
- Shape 1 over `Nat`/`Int`: `"[0, 64) default window"`.
- Shape 1/2 with two `Fin` binders: `"Fin a × Fin b = a*b"`.
- Shape 7: `"atomic"`.

### Cycle-Tracker init

```bash
lean4-skills-cycle-tracker init \
  --max-cycles=<resolved> --max-stuck-cycles=<resolved> \
  --max-runtime=<resolved> \
  --max-knowledge-search-per-cycle=<resolved --knowledge-search-budget>
```

Disprove has no deep mode in v1: it never calls `can-deep` / `deep`,
so the deep counters maintained internally by the tracker are inert.
Omit the deep flags from `init` — passing `=0` would be rejected by
the tracker's `_require_positive_int` validation.

`--max-knowledge-search-per-cycle` enforces the per-cycle visit cap for
Step 0 (see below). The tracker's `kw-search-can` / `kw-search` actions
gate entry to Step 0.

### Step 0 — Knowledge Search Menu

Step 0 runs **once in Cycle 1** by default. It re-runs only when a later
cycle's Step 1 menu surfaces the `knowledge search` entry **and the
user picks it**, subject to the per-cycle visit cap
(`--knowledge-search-budget`, default 3). After the Nth visit in a cycle
completes, `knowledge search` is disabled in that cycle's Step 1 menu;
the cap resets at each `tick`.

The cycling LLM proposes a menu of knowledge-search tasks each visit.
Multi-select; the standard rows (lean/local/web tiers), and `[custom]` and `[llm]`. Each row shows what will fire if it
stays selected: the tool/source, the tier tag, and the executable query
string the LLM derives from the TARGET. The user reviews — editing
query text or reducing the selection — and approves; only after
approval do the selected rows fire. Tier semantics: `[lean]` = Lean /
mathlib name lookup, `[local]` = target-file or repo grep, `[web]` =
open-web literature.

**Menu items.** The `[lean]` and `[local]` rows (plus `[custom]`/`[llm]`) are
**pre-selected by default**; the `[web]` rows are **available but pre-selected only
when the target has searchable names** (a recognizable named constant/operator or
mathematical content) — knowledge search is advisory and host-dependent, so web
isn't fired every cycle by default. The user can select any row.

- `[lean]`   `lean_leansearch`  *(pre-selected)*
- `[local]`  mathlib `Counterexamples/` grep  *(pre-selected)*
- `[local]`  repo grep `*_counterexample` / `*_counter` / "false" comments  *(pre-selected)*
- `[web]`    websearch — known counterexample search methods  *(pre-selected only if searchable)*
- `[web]`    websearch — known NON-counterexamples  *(available; not pre-selected by default)*
- `[web]`    websearch — known counterexamples  *(pre-selected only if searchable)*
- `[custom]` user-supplied free-form intent — at fire time the LLM
  interprets the user's text into an executable query and picks the
  tier, then dispatches the matching tool. The interpretation is
  recorded in the finding's `source_tier` + `query` fields (and shown
  in the Disprove Summary's per-cycle table).
- `[llm]`    LLM-proposed query — the LLM emits both the query and
  its tier (`(none)` if the LLM has no proposal beyond the rows above).

**Findings schema** (one record per surviving finding):

```json
{
  "cycle":         "<int>",
  "source_tier":   "lean | local | web",
  "query":         "<the literal query that produced this finding>",
  "claim":         "<one-line summary>",
  "source_url":    "<URL or repo-relative path>",
  "retrieved_at":  "<ISO-8601 UTC>",
  "verified_via":  "webfetch:<url> | none",
  "confidence":    "high | medium | low"
}
```

- **`source_url` is required.** Findings produced without a citable URL
  or repo-relative path are dropped at write time — they never surface
  in the Step 1 input.
- **Web-tier counterexample candidates are spot-verified** via
  `WebFetch` on the cited URL before being elevated to a
  `[verify-known-cex]` candidate (sets `verified_via=webfetch:<URL>`).
  Verification passes when the fetched content names
  the specific witness (the value, expression, or counterexample
  index) **and** the predicate or conjecture it refutes, and the
  claim is not disputed in-context. Failure modes that drop the
  finding: HTTP 4xx/5xx, paywall/login wall, off-topic landing page,
  cited witness not present on the fetched page. If `WebFetch` is
  unavailable in the host, web findings are dropped, not elevated. Report all failures to user.

**Persistence (dual):**

- **Inline conversation digest** — what the cycling LLM reads on each
  Step 1 / Step 2 invocation. Compact; only new evidence since the last
  cycle is re-integrated.
- **`$LEAN4_SESSION_DIR/findings.jsonl`** — append-only, one record per
  line. Seeds the inline digest on resume **within the same ephemeral session
  directory only**; cited by the Disprove Summary's per-cycle URL column. This is
  online adaptation *within* a session — **no state persists across independent
  runs by default** (a fresh run starts a fresh session dir).

**Outcomes feed:**

- Counterexample-search-method hits — findings about *how to look*
  for a counterexample, surfaced by any tier (e.g. a websearch hit
  describing a Diophantine-grid sieve, a SAT-with-blocking-clauses
  approach, or a `lean_leansearch` hit naming a tactic combinator;
  the dedicated Step 0 item is `[web] websearch — known counterexample
  search methods`). The LLM **maps the discovered method to the
  nearest registry family** (e.g. `enumerate` with a window and
  atom tactic tuned to the cited technique; `external` for SAT/SMT
  references, custom Python/other scripts; `tactics` for a tactic-combinator pointer) and
  synthesizes a specialized Step 1 entry (or entries) whose label and reasoning
  cite the source.
- Non-counterexample ranges (e.g. a web finding that the statement
  holds for `n ≤ 1000`) → inform Step 2's range / sample-size defaults
  so the search doesn't waste budget on regions already known true.
- Cited counterexample candidates → generate a `[verify-known-cex]`
  entry pre-selected at rank 1 of the next Step 1 menu. Per-tier
  gating:
  - **Web-tier** candidates require WebFetch verification first (per
    the spot-verify rule above).
  - **Lean / local-tier** candidates are elevated on a **strong
    match** — the hit's identifier or doc-comment names the same
    predicate / operator / constant that appears in the TARGET
    (e.g. the TARGET mentions `Nat.Prime` and the hit's declaration
    is `Nat.Prime` adjacent). No WebFetch needed; the source is
    already in the Lean ecosystem. Weaker matches feed the cycling
    LLM's reasoning but don't trigger rank-1 elevation.

### Step 1 — Method Menu

The cycling LLM proposes a menu of 3–10 method candidates each cycle,
single-select. It specializes from the registry's six stable families
(`decide-cascade`, `mine`, `enumerate`, `plausible`, `tactics`,
`external`) — picking which families to surface, how many entries per
family (e.g. two `external` rows with different counterexample search
methods using external solvers), and emitting a free-text `label` per
entry — then orders the entries by expected payoff under the current
evidence. Inputs the cycling LLM receives:

- The [Method Registry](#method-registry) (data file)
- Accumulated Step 0 findings digest
- Prior cycle's Review block + accumulated `(family, config, outcome)` log
- Target Profile
- LLM judgment

**Per-entry display:**

```
N. <label>  [family: <stable-id>]   [<cost-class>]
   Description: <one-line method description>
   Reasoning:   <why this entry given the evidence>
   Cost (~wall-clock):    <coarse wall-clock estimate, e.g. "~1s", "~30s",
                "~1m", "~5m">
```

The `family` is the stable id from the registry (e.g. `decide-cascade`,
`enumerate`); `label` is the LLM-emitted free-text variant name
(e.g. `"enumerate Nat, Lander–Parkin window 27…145"`).

`Cost (~wall-clock)` is a *coarse* wall-clock estimate for the config skeleton
implied by the `label` — Step 2 will refine it. The cycling LLM
derives it from the registry's `budget_hint_seconds × expected
candidate count` (or `× 1` for single-shot families like
`decide-cascade`). Cross-cycle calibration: the prior cycle's Review
block carries `(estimated, actual)` time pairs the LLM uses to adjust
future estimates.

**Applicability & availability filtering.** Only registry-backed methods that are
**both applicable and available** are listed as numbered, selectable entries:

- *applicable* — the registry `applies_to_shapes` includes the current Target
  Profile shape;
- *available* — prerequisites are met (cheap probes): e.g. `decide-cascade` needs a
  `Decidable` instance, `plausible` a `SampleableExt` instance. `external` is
  approval-gated (generic Python/bash scripts) and stays selectable; solver-backed
  configs additionally need z3/cvc5 on `$PATH` (reported, not gated).

`lean4-skills-disprove-method-probe --profile=<profile.json>` computes this
deterministically — `{method: {selectable, reason}}` from the registry's
`applies_to_shapes` (vs `profile.shape`), the profile's `decidable`/`sampleable`
hints, and a `shutil.which` solver check that is **advisory** for `external`
(surfaced in the reason, not an availability gate). The cycling LLM renders the
selectable set as the menu and the rest under "Unavailable this cycle".

A method that is inapplicable or unavailable is **not numbered**; render it under a
separate **"Unavailable this cycle"** block with a one-line reason drawn from the
registry `false_negative_notes` or the failed probe:

```
Unavailable this cycle:
- decide-cascade — target not Decidable in current imports
- plausible      — no SampleableExt instance for the binder type
```

(`external` is not listed here for a missing solver — it stays selectable; the probe
reports solver presence in its reason instead.)

This filtering applies **only to registry-backed method entries**. The
always-present special entries below are governed by their own rules, not by this
filter (e.g. `knowledge search` stays shown but disabled after the Step 0 visit cap).

**Always-present extras:**

- `knowledge search` — disabled (and visibly so) after the cycle's Nth
  Step 0 visit.
- `custom method` — free-form description. The cycling LLM maps the user's
  description to the nearest registry `family` and synthesizes a `config`.
  Audit trail records: `family=<X>, config={...}, derived-from-custom="<user text>"`.

**Menu invariants** (3–10 items total):

1. If a verified `[verify-known-cex]` candidate exists, it occupies
   **rank 1**, pre-selected.
2. **No wasted work in the top 3.** Every top-3 entry must explore
   territory not already covered by the failed-evidence set
   (`failed` = any `(family, config)` recorded in Phase 5 evidence
   with `outcome ≠ "certified"`):
   - **No exact-pair repeats**: top-3 `(family, config)` is not in the
     failed-evidence set under strict tuple equality.
   - **No overlapping search spaces**: the proposed config's coverage
     must be **disjoint** from any already-failed config's coverage —
     widening must explore **new** territory only. For range-shaped
     families (`enumerate`), this means widening as
     `range=[prev_end, new_end)`, NOT `range=[0, new_end)` (the latter
     re-searches `[0, prev_end)`). For discrete-set families
     (`tactics`, `decide-cascade`, `external`), the new set's elements
     must exclude already-tried elements. For probabilistic families
     (`plausible`) with fresh `seed`, draws are inherently new — overlap
     is N/A.
   - **Failed pairs MAY appear at ranks 4–10** as a user-override
     option (e.g. "retry only after a code change"); the top-3
     constraint protects the default-pick zone.

   The cycling LLM applies this **semantically**, not by strict tuple
   equality alone — it judges per-family config coverage from the
   evidence log.
3. If `Target Profile.decidable == yes` AND no decide-family success has
   been recorded yet, a decide-family entry **must appear in the top 3**
   (not necessarily rank 1 — rule 1 wins precedence).

### Step 2 — Config Menu

**If Step 1 picked `knowledge search`:** Step 2 is overloaded — it is a
**multi-select of the Step 0 items** for a re-run. On confirm, return
directly to Step 0; this re-entry counts against the
`--knowledge-search-budget` visit cap. After Step 0 completes, control
returns to Step 1 with the freshly accumulated findings digest.

**Otherwise (any concrete family):** The cycling LLM proposes a menu of
3–10 config candidates for the picked family, single-select. Each
candidate is a concrete instantiation of the family's params from the
registry (e.g. for `enumerate`: specific `range_start`, `range_end`,
and `atom_tactic` values) — not a re-ordering of pre-defined configs.
The registry's per-param `default` is a **seed value**, not a UI
default: the cycling LLM is expected to override it when Target Profile
or Step 0 evidence justifies (e.g. `enumerate.range_end` seeds at `64`,
but for `∀ n : Fin 16, …` the LLM should propose candidates with
`range_end = 16` to match the target's cardinality). Inputs the
cycling LLM receives: picked family's parameter schema, Step 0 digest,
prior-cycle outcomes, Target Profile, LLM judgment.

**Per-entry display:**

```
N. <config summary, e.g. "range=[5,64), atom=decide">
   Reasoning:           <why this config given the evidence>
   Cost (~wall-clock):  <refined estimate, e.g. "~64s", "~30s", "~1m">
   Coverage:            <<mode>: <K> [of <denominator from candidate_grid>]>
                        <e.g. "exhaustive: 16/16 over Fin 16",
                              "window: 59/∞ over Nat",
                              "sampled: 200 random of unbounded",
                              "list: 10 named candidates">
```

**Cost vs Coverage**: the two axes are independent. `Cost` is the
expected wall-clock time the cycling LLM derives from the registry's
`budget_hint_seconds × candidate count` (or family-equivalent —
`samples` for `plausible`, `len(tactics)` for `tactics`, etc.).
`Coverage` is the *shape* of the search the config performs, expressed
as `<mode>: <K>` plus (when meaningful) `of <denominator>` taken from
the Target Profile's `candidate_grid`. Modes: `exhaustive` (covers all
of a finite set), `window` (covers a sub-interval of a larger or
infinite set), `sampled` (probabilistic draws — coverage is
distributional, not enumerative), `list` (a named candidate set, as in
`mine`), `atomic` (single proposition decided in one shot — no
enumeration, as in `decide-cascade`), `cited` (adopts an
externally-cited witness or lemma, as in `[verify-known-cex]`
entries). The cross-cycle calibration loop (Phase 4 Review's
`(estimated, actual)` time pair) lets the LLM tighten `Cost` over the
session.

**Always-present extra:** `custom-config` — free-text. Schema-validated
against the picked family's `params` table in
[disprove_methods.toml](../../../lib/data/disprove_methods.toml).

On confirm → Phase 2.

## Phase 2 — Work

Run the chosen method with the chosen Step 2 config. For each candidate
witness:

1. Construct a per-shape Lean snippet
   ([Per-Shape Recipes](#per-shape-recipes) below).
2. Pre-screen via `lean_multi_attempt(file, line, snippets=[snippet])`.
3. On pass, advance to Checkpoint.
4. On fail, record the residual error signature (used by Review).

Post-gate cycle outcomes (assigned after the Phase 3 typecheck + axiom gate, consumed by Review):

| Outcome | Meaning |
|---------|---------|
| `certified` | A candidate passed pre-screen, the file typecheck gate, AND the axiom gate (axioms ⊆ whitelist — see Phase 3). |
| `near-miss` | A candidate passed pre-screen but the Phase 3 gate rejected it — `lake env lean` failed, OR a non-whitelisted axiom appeared / axiom inspection was inconclusive (→ `WITNESS_UNCERTIFIED`). The error signature is captured. |
| `exhausted-no-witness` | The method's budget was spent; no candidate was produced. |
| `no-candidate` | The method produced zero candidates (e.g., enumerate hit no `DecidablePred`, or an external script timed out / failed to parse). |

### External family — Work-phase execution

When the picked Step 2 config has `family = "external"`, Phase 2 Work
runs an LLM-emitted script before constructing the per-shape Lean
snippet:

1. **Emit script.** The cycling LLM writes a script to
   `$LEAN4_SESSION_DIR/scripts/cycle-<N>-trial-<M>.<ext>` — extension
   determined by `config.language` (`.py`, `.sh`, `.smt2`, …). The
   script implements the methodology the Step 1 entry cited (e.g. a
   Diophantine-grid sieve, a SAT encoding of the target's negation,
   a custom shell pipeline), parameterised by the Step 2 config and
   the Target Profile.
2. **Confirmation prompt.** Phase 2 displays the full script to the
   user with a one-line summary and prompts for explicit approval
   before execution:
   ```
   Run cycle-3-trial-1.py? [yes / show-full / skip]
   ```
   The cycling LLM also flags any noteworthy capabilities the script
   uses (network access, local solver invocation, file writes outside
   the scripts dir).
3. **Execute.** On approval, run via the `Bash` tool with `timeout`
   set from the picked entry's `Cost (~wall-clock)` estimate:
   ```bash
   timeout <Cost-seconds> python3 $LEAN4_SESSION_DIR/scripts/cycle-N-trial-M.py
   ```
   For `bash`, run the file directly. For `sat-z3` / `sat-cvc5` /
   `smt-z3` / `smt-cvc5`, dispatch the `.smt2` file via the matching
   solver binary if installed; if the solver isn't on `$PATH`, fall
   through to `outcome = no-candidate` with the binary-missing reason
   captured.
4. **Parse stdout for witnesses.** The cycling LLM judges the output
   — there is no hard-coded format. Convention: emit lines like
   `WITNESS: <value>` (one per line) so parsing is mechanical, but
   the LLM may extract from richer or solver-specific output (e.g.,
   z3 `(model …)` blocks) too.
5. **Wrap each witness through Per-Shape Recipes**, then
   `lean_multi_attempt(file, line, snippets=[per-shape-recipe(w)])`.
   The witness flows through the existing pre-screen + Checkpoint
   pipeline unchanged.

**Outcomes for external**:
- Script timeout, non-zero exit, witness-parse failure, no witnesses
  in stdout → `outcome = no-candidate`; reason captured in
  `near_miss_signature` (e.g. `"external: timeout after 60s"`).
- At least one witness produced AND one passes pre-screen → standard
  Checkpoint flow → `outcome = certified` only if the Phase 3 typecheck
  **and** axiom gate both pass (otherwise `near-miss` → `WITNESS_UNCERTIFIED`
  per the Phase 3 failure rule).
- Witness produced but pre-screen rejects all → `outcome = near-miss`
  with the Lean error signature.

The saved script path is recorded in Phase 5 evidence as
`external_script_path` for audit / re-run.

### Method Registry

The Method Registry is a structured data file:
[`plugins/lean4/lib/data/disprove_methods.toml`](../../../lib/data/disprove_methods.toml).
It is the canonical source of stable method ids, applies-to-shape
filters, parameter schemas, cost classes, and per-method false-negative
notes that the cycling LLM draws from when proposing the Step 1 / Step 2
menus.

Schema per entry (see the file's top-of-file comment for the field
reference): `id`, `display_name`, `applies_to_shapes` ⊆ {1..7},
`cost_class` ∈ {cheap, medium, expensive}, `budget_hint_seconds`,
`false_negative_notes`, `cert_template_ref` (anchors into Per-Shape
Recipes below), and `params` (per-parameter schema for `custom-config`
validation).

The registry ships six methods: `decide-cascade`, `mine`, `enumerate`,
`plausible`, `tactics`, `external`. Known-counterexample adoption
flows through the Step 1 menu's `[verify-known-cex]` entry, which is
generated when Step 0 yields a verified web finding (see Phase 1 §
Step 0). The `external` family runs LLM-emitted scripts in Phase 2
Work — see [§ External family — Work-phase execution](#external-family--work-phase-execution).

Renames and additions are governed by the registry's schema tests
(`tests/test_disprove_methods.py`); changes to `cert_template_ref` must
keep the anchor resolvable against this file's
[Per-Shape Recipes](#per-shape-recipes) section.

## Phase 3 — Checkpoint

If Work produced a **pre-screen-passing candidate** this cycle (`<target-file>` is the target's
source file: the `File.lean` for a file-line target, or the writable source file
the qualified-name target resolved to in Phase 1):

1. Construct the per-shape `T_counterexample` Lean snippet
   ([Per-Shape Recipes](#per-shape-recipes) below). Apply atom-slot
   hot-swap if the first cert tactic fails (see the cascade order
   documented with the recipes). For **witness shapes** (1/2), also build the
   named, gate-only `T_counterexample_negates_target : ¬ TARGET := <shape-specific
   wrapper>` (see the Per-Shape Recipes intro) — this is the declaration that
   actually carries the `¬ TARGET` type.
2. Append within a **transaction** so the cycle's writes are revertible by id.
   Open one with `txn=$(lean4-skills-disprove-artifact-txn begin)`,
   then append the artifact (snippet on stdin):
   `lean4-skills-disprove-artifact-txn append --scope-file=<target-file> --txn=$txn --role=artifact --decl=T_counterexample --cycle=<N>`.
   For witness shapes, append the gate-only declaration under the same txn with
   `--role=gate --decl=T_counterexample_negates_target`. Each append is wrapped in
   `-- lean4:disprove-begin/-end txn=… role=…` markers and refuses to clobber a decl
   already declared outside the txn. (The standalone collision-safe writer
   `lean4-skills-disprove-emit-artifact` remains for non-transactional appends.)
3. Run `lake env lean <target-file>` from the project root (typecheck gate).
4. **Axiom gate.** Inspect the axioms via `lean_verify` (or `#print axioms`) of the
   declaration that carries the `¬ TARGET` type — `T_counterexample` for direct
   shapes, or `T_counterexample_negates_target` for witness shapes. The allowed set
   is `{propext, Classical.choice, Quot.sound}`, plus `Lean.ofReduceBool` **only**
   when `native_decide` was explicitly opted in for this cycle (recorded in the
   evidence record).
5. License the outcome:
   - **`certified` (→ `REFUTED`)** only if the `¬ TARGET`-typed declaration
     typechecked (no `sorry`/`admit`) **and** its axiom set ⊆ the allowed whitelist.
     For witness shapes, `lean4-skills-disprove-artifact-txn drop-role --scope-file=<target-file> --txn=$txn --role=gate`
     **before** the commit, then from the project root re-run
     `lake env lean <target-file>` on the wrapper-free file, so the committed state
     (`T_counterexample` alone, which still typechecks) is itself gate-verified — the
     committed file equals the gate-checked file. Commit only `T_counterexample`;
     proceed to Review.
   - **Typecheck fails** → `lean4-skills-disprove-artifact-txn rollback --scope-file=<target-file> --txn=$txn`
     (removes the artifact and, for witness shapes, the gate-only wrapper — only this
     txn's marker blocks); downgrade to `near-miss`, capture the error signature.
   - **A non-whitelisted axiom appears, or axiom inspection is unavailable /
     inconclusive** → `rollback --scope-file=<target-file> --txn=$txn` (never touches
     pre-existing or other-txn declarations), do **not** commit, downgrade to
     `WITNESS_UNCERTIFIED` — never `REFUTED`.

Per `--commit`:
- `auto` — stage the modified file (`git add <target-file>`, never `-A`)
  and commit `disprove: T_counterexample — cycle N`. When the certifying
  cycle adopted a `custom method` from Step 1, include
  `derived-from-custom="<user text>"` in the commit message body for
  provenance.
- `ask` — show the diff and prompt the user.
- `never` — leave staging to `/lean4:checkpoint`.

If Work produced no pre-screen-passing candidate: no artifact, no rollback —
nothing was written this cycle.

### Per-Shape Recipes

Snippets shown as `example : …` below are pre-screen / certification **templates**;
the emitted-and-committed artifact is named `T_counterexample`. Phase 3 typecheck-
and axiom-checks the declaration carrying `¬ TARGET` **by name** — `T_counterexample`
itself for direct shapes, or the temporary `T_counterexample_negates_target` wrapper
for witness shapes. The emitted `T_counterexample` must be
a **closed** term — Shapes 4/5 must inline/apply their sub-counterproofs (never a
partially-applied wrapper). For **witness-shaped** artifacts (Shapes 1/2, whose
`T_counterexample` is existential, not `¬ TARGET`), Phase 3 additionally typecheck-
and axiom-checks a **named** derived-negation declaration built with the
shape-specific wrapper — e.g.
`T_counterexample_negates_target : ¬ TARGET := not_forall.mpr T_counterexample`
(Shape 2 uses the `∃ w, P w ∧ ¬ Q w` → `¬ (∀ x, P x → Q x)` wrapper). That
`*_negates_target` declaration is a temporary, gate-only certification — not a
committed artifact; if inserted into the file for the gate it uses the same
collision-safe handling and is excluded from the commit.

**Shape 1 — `∀ x : α, P x` with witness `w0`:**

```lean
theorem T_counterexample : ∃ w : α, ¬ P w := by
  refine ⟨w0, ?_⟩
  -- atom slot: by decide | by norm_num | by omega
```

To produce `¬ ∀ x, P x` directly, follow with
`not_forall.mpr T_counterexample`.

**Shape 2 — `∀ x, P x → Q x` with witness `w0`:**

```lean
theorem T_counterexample : ∃ w, P w ∧ ¬ Q w := by
  refine ⟨w0, ?_, ?_⟩
  -- atom slot 1: by decide  (P w0)
  -- atom slot 2: by decide  (¬ Q w0)
```

**Shape 7 — Decidable atom `P`:**

```lean
example : ¬ P := by decide
-- escalations: native_decide (only if enabled this cycle) → norm_num → omega
```

**Shape 3 — `∃ x : α, P x` with `[Fintype α]`:**

Primary path (when the `Decidable (∃ x : α, P x)` instance synthesises):

```lean
example : ¬ (∃ x : α, P x) := by decide
```

Fallback when `decide` reports a synthesis failure or hits the elaborator
budget — destructure and case-split on the (finite) carrier, then apply
the cascade atom-by-atom:

```lean
example : ¬ (∃ x : α, P x) := by
  intro ⟨x, hx⟩
  fin_cases x <;> exact absurd hx (by decide)
```

Checkpoint emits the primary form first; on hot-swap failure it
substitutes the fallback before re-running `lean_multi_attempt`. The
per-case atom slot follows the same cascade as Shapes 1, 2, 7
(`decide → native_decide` (only if enabled this cycle) `→ norm_num → omega → simp → rfl`).

**Shape 4 — `P ∧ Q` (disprove one conjunct):**

Pick whichever conjunct yields the smaller search; obtain `h : ¬ P` (or
`h : ¬ Q`) via the matching Shape 1/2/7 recipe, then wrap by pattern
match:

```lean
theorem T_counterexample (h : ¬ P) : ¬ (P ∧ Q) := fun ⟨hp, _⟩ ↦ h hp
-- mirror with `fun ⟨_, hq⟩ ↦ h hq` when disproving Q
```

**Shape 5 — `P ∨ Q` (disprove both disjuncts):**

Recurse on both — obtain `hp : ¬ P` and `hq : ¬ Q` via the matching
Shape 1/2/7 recipes, then combine:

```lean
theorem T_counterexample (hp : ¬ P) (hq : ¬ Q) : ¬ (P ∨ Q) :=
  fun h ↦ h.elim hp hq
```

**Shape 6 — `a = b` or `a ≤ b` / arithmetic ineq:**

Atom case — same shape as Shape 7 but the cascade typically lands on
`norm_num` (concrete arithmetic) or `omega` (linear arithmetic over
`ℤ`/`ℕ`) before falling back to `decide`:

```lean
example : ¬ (2 + 2 = 5) := by norm_num    -- or `by decide`
example : ¬ (10 ≤ 3)    := by omega        -- or `by decide`
```

**Atom-slot cascade order** (used by Phase 3's hot-swap when the first
cert tactic fails): `decide → native_decide` (only if enabled this
cycle) `→ norm_num → omega → simp → rfl`. Re-run `lean_multi_attempt`
after each swap. If the cascade is exhausted, downgrade the cycle
outcome to `near-miss` and capture the residual error signature.

## Phase 4 — Review

Emit a short Review block per cycle:

```
Review (cycle N):
  Method            : <family>
  Config            : <method-specific key=value list>   e.g. "range=[5,64), atom=decide"
  Outcome           : certified | near-miss | exhausted-no-witness | no-candidate
  Candidates tried  : <K>
  Time              : actual <T>  (estimated <E>; from picked Step 2 entry's Cost)
  Near-miss signature (if any) : <error-key>  e.g. "decide: failed to reduce ¬ (n^2 + n + 41).Prime"
  Step 0 visits     : <kw_search_this_cycle>/<max_kw_search_per_cycle>
```

The `(estimated, actual)` time pair persists into Phase 5 evidence and
is read by the next cycle's menus to calibrate their `Cost` estimates
(see Step 1 / Step 2 per-entry display).

Review feeds Accumulate (Phase 5), which appends the structured record
to session evidence for the next cycle's menus.

## Phase 5 — Accumulate

After a cycle that didn't certify, Accumulate is a pure state update:
append the cycle's evidence record to the session digest. No hardcoded
recommendation table — the next cycle's Step 0 / Step 1 / Step 2 menus
absorb the recommendation logic from the accumulated evidence.

**Re-ranking signals (advisory, not a fixed escalation table).** When the next
cycle's menus re-rank from this evidence, the cycling LLM weighs — but is not bound
by — signals such as:

- **Deprioritize the failed-evidence set** — `(family, config)` pairs recorded with
  `outcome ≠ certified` drop in rank (and are excluded from the top-3 per the Step 1
  menu invariants).
- **Boost a verified `[verify-known-cex]`** — a WebFetch/strong-match-verified cited
  counterexample takes rank 1.
- **Prefer non-overlapping widening** — extend coverage into untried territory
  (e.g. `range=[prev_end, new_end)`), never re-search a covered window.
- **Surface a neighboring family** when the current family's widening lever is
  exhausted (e.g. `enumerate` → `plausible`/`external`).

These are heuristics for the LLM's judgment; they deliberately do **not** encode a
rigid ordering.

Session evidence record (appended once per cycle):

```json
{
  "cycle":                          "<int>",
  "family":                         "<id from Method Registry>",
  "config":                         { /* per-method config snapshot */ },
  "outcome":                        "certified | near-miss | exhausted-no-witness | no-candidate",
  "near_miss_signature":            "<error key, or null>",
  "estimated_time_seconds":         "<int from picked Step 2 entry's Cost>",
  "actual_time_seconds":            "<int wall-clock>",
  "derived_from_custom":            "<user text, if custom method>",
  "derived_from_verify_known_cex":  "<source_url or repo-relative path, if [verify-known-cex]>",
  "external_script_path":           "<path under $LEAN4_SESSION_DIR/scripts/, if family=external>",

  // Reproducibility fields (recorded for a certified REFUTED):
  "target_hash":                    "<hash of the normalized target>",
  "normalized_target_type":         "<the resolved/profiled type>",
  "artifact_file":                  "<target source file>",
  "artifact_decl":                  "<committed artifact name, e.g. T_counterexample>",
  "negation_decl":                  "<the ¬TARGET decl checked: artifact (direct) or the gate-only wrapper>",
  "artifact_hash":                  "<hash of the artifact text>",
  "negation_wrapper_hash":          "<hash of the gate-only wrapper text, if a witness shape>",
  "lake_env_lean_ok":               "<bool: typecheck gate passed>",
  "axioms":                         ["propext", "Classical.choice", "Quot.sound"],
  "native_decide_opt_in":           "<bool>",
  "lean_version":                   "<toolchain version>",
  "mathlib_revision":               "<rev>",
  "external_solver":                "<z3 | cvc5 | null>",
  "external_solver_version":        "<version, if external>"
}
```

The gate-only `*_negates_target` wrapper is **not committed**, so when it (not the
artifact) is the declaration that licensed `REFUTED`, its text/hash MUST be captured
here (`negation_decl` + `negation_wrapper_hash`) — that is the only durable record of
the term the kernel actually accepted.

`estimated_time_seconds` / `actual_time_seconds` form the calibration
pair the next cycle's menus read when computing their `Cost` lines —
persistent across cycles so calibration tightens over a long session,
not just within one Phase 4 → Phase 5 hop.

`[verify-known-cex]` entries map to the nearest registry `family` at
fire time — typically `tactics` for adopting a Lean-ecosystem lemma
(`config = {tactics: ["exact NS.X_counterexample"]}`), or the family
whose `config` best operationalizes the cited witness (e.g.
`enumerate` with `range_start = range_end = <witness>` for a concrete
numeric witness). The `config` field captures the resolved
instantiation; `derived_from_verify_known_cex` records the originating
`source_url` / repo path, mirroring how `derived_from_custom` records
the user's free-form text. Example values:
`"https://en.wikipedia.org/wiki/Formula_for_primes#Euler_polynomial"`
(web tier, WebFetch-verified) or
`"Mathlib/Counterexamples/Phillips.lean#Phillips.PhillipsExample"`
(lean / local tier — repo-relative path with `#<theorem-name>` anchor).

Step 0 visits do not produce evidence records themselves; their
findings live in the Step 0 digest (and `findings.jsonl`).

### Stuck Definition for Disprove

Under Accumulate, the stuck definition is **evidence-based**:

A cycle is **stuck** when **both** hold:

- It produced no `certified` outcome (Review = near-miss /
  exhausted-no-witness / no-candidate), AND
- The next cycle's Step 1 menu has **no non-failed `(family, config)`
  pair** to place in its top 3 — per invariant 2's definition of
  "failed" (exact-pair repeat OR overlapping search space). Every
  viable `(family, config)` combination for the current Target Profile
  has been tried, with no remaining widening lever — non-overlapping
  range extension, additional plausible samples (fresh seed),
  un-tried tactics, neighboring family — for the cycling LLM to
  specialize.

Two consecutive stuck cycles → the session bails with `INCONCLUSIVE` on
the next Continue/Stop boundary.

## Phase 6 — Continue / Stop

Always prompt the user:

```
Cycle N complete.
  Outcome: <certified | near-miss | exhausted-no-witness | no-candidate>
  Next cycle's Step 1 preview: <top-ranked entry's family + config>

- [continue] — run cycle N+1 with the preview pre-selected at Step 1
- [stop]     — accept current outcome, emit Disprove Summary
```

To override the preview, pick a different entry (any registry family,
`knowledge search`, or `custom method`) when the next cycle's Step 1
menu opens.

After the user decides:

```bash
# At every cycle boundary:
lean4-skills-cycle-tracker tick --stuck=<yes|no>

# Just before emitting the Disprove Summary (on session stop):
lean4-skills-cycle-tracker status
lean4-skills-cycle-tracker stop
```

`tick` enforces `--max-cycles` and `--max-stuck-cycles` at the cycle
boundary and resets `kw_search_this_cycle` to 0. `--max-runtime` is
checked here too (best-effort).

## Disprove Summary

The Disprove Summary is a single tri-state report: `REFUTED`,
`WITNESS_UNCERTIFIED`, or `INCONCLUSIVE`. For the full template and the
per-outcome handoff bullets, see
[commands/disprove.md § Disprove Summary](../../../commands/disprove.md#disprove-summary)
— it is the canonical source.

The per-cycle attempts table includes a `URL` column populated for any
cycle whose certifying witness was elevated via `[verify-known-cex]`
(the URL is the verified `source_url` of the originating Step 0
finding). For all other cycles the column is `—`.

## Safety

- **Append-only, transactional.** Never rewrite an existing
  `theorem T : P := by sorry` declaration to `: ¬ P`. Cycle artifacts are
  written through `lean4-skills-disprove-artifact-txn` (over the collision-safe
  `lean4-skills-disprove-emit-artifact`): each append is wrapped in txn-id markers and
  refuses to modify or duplicate an existing declaration; the cycle's writes
  are reverted as a unit via `rollback` (failure) or `drop-role` (gate-only
  wrapper before commit), never touching pre-existing or other-txn declarations.
- **No `native_decide` without opt-in (any method).** `native_decide`
  defaults off and is excluded from the `tactics` method's default list.
  Wherever it can appear — the `decide-cascade` family's
  `native_decide=true` param, a custom `tactics` list, or a
  `custom-config` — it counts as the **same** audit-worthy opt-in: the
  Step 2 menu must surface it explicitly as audit-worthy and the cycle's
  evidence record must log it. Enabling admits the `Lean.ofReduceBool`
  axiom, which the Phase 3 axiom gate then allows **only** for that cycle
  (see Phase 3).
- **No claim of `REFUTED` without compile gate + axiom gate.** Pre-screen via
  `lean_multi_attempt` is necessary but not sufficient. `REFUTED` requires
  **both** `lake env lean <path>` from the project root (typecheck, no
  `sorry`/`admit`) **and** an
  axiom set ⊆ `{propext, Classical.choice, Quot.sound}` (plus `Lean.ofReduceBool`
  only under an explicit `native_decide` opt-in this cycle). A term that
  typechecks but pulls a non-whitelisted axiom — or any cycle where axiom
  inspection is unavailable/inconclusive — is `WITNESS_UNCERTIFIED`, and the
  appended hunk (if any) is reverted (see Phase 3).
- **No Step 0 findings without `source_url`.** Findings produced without
  a citable URL or repo-relative path are dropped at write time. Web
  counterexample candidates require `WebFetch` verification before
  elevation to `[verify-known-cex]`. If `WebFetch` is unavailable in
  the host, web findings are dropped, not elevated.
- **External-family script execution gate.** When Phase 2 Work
  executes an LLM-emitted script (`family = "external"`), the full
  script body is shown to the user and explicit approval is required
  before execution. Scripts are written to
  `$LEAN4_SESSION_DIR/scripts/` and run via the `Bash` tool with
  `timeout` set from the entry's `Cost (~wall-clock)` estimate.
  Scripts may make network calls or invoke local solvers if available
  — the cycling LLM must call this out in the confirmation prompt.
  The scripts directory survives the run for audit; each cycle's
  script is referenced by the Phase 5 evidence record's
  `external_script_path` field.

## Reference

The `/lean4:disprove` skill is described in: Jan Ondras and Cameron Freer,
"Lean Disprove: Certified Counterexample Search for AI-Assisted Formal
Mathematics," 3rd AI for Math Workshop: Toward Self-Evolving Scientific Agents (ICML 2026). <https://openreview.net/forum?id=5ck1jRE65S>
(BibTeX in [`commands/disprove.md`](../../../commands/disprove.md#citation).)
