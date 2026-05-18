# Disprove Engine Reference

> Disprove-specific specialization of [cycle-engine.md](cycle-engine.md).
> Inherits the shared 6-phase cycle vocabulary
> (Plan → Work → Checkpoint → Review → Replan → Continue/Stop), the
> LSP-first protocol, the compile-gate contract, and the
> [Falsification Artifacts](cycle-engine.md#falsification-artifacts)
> templates. Adds disprove-only mechanics: the Method Registry, the
> two-step Step 1 / Step 2 prompts, the Per-Shape Recipes, and the
> Replan Rules table.
>
> `/lean4:disprove` is always interactive: the workflow prompts the user
> in each cycle's Plan phase to choose a search method (Step 1) and
> configure its parameters (Step 2).

## Prime Directive — Epistemological Strictness

`/lean4:disprove` reports `FALSE` **only** when it produces a Lean term of
the negation that typechecks under `lake env lean` without `sorry` or
`admit`. Fast witnesses and informal heuristics are *hypotheses* until
Lean certifies them. Anything weaker is reported as `WITNESS_UNCERTIFIED`
or `INCONCLUSIVE`. This invariant is non-negotiable.

## Six-Phase Cycle

```
Plan → Work → Checkpoint → Review → Replan → Continue/Stop
```

A cycle is a **widening pass** over the same target. Each cycle picks one
method (via Step 1) with its own parameters (via Step 2) and either
certifies a counterexample or feeds Review and Replan to widen the
search in the next cycle.

| Phase | Disprove-specific behavior |
|-------|----------------------------|
| 1. Plan | Cycle 1 resolves TARGET, normalizes shape, prints Search-Space Estimate. Every cycle: Step 1 menu + Step 2 prompts (Replan's recommendation pre-fills cycle ≥2). |
| 2. Work | Run the chosen method with the chosen config. Pre-screen candidates via `lean_multi_attempt`. |
| 3. Checkpoint | If a candidate certified: append `T_counterexample`, run `lake env lean`, stage + commit per `--commit`. If not: no artifact. |
| 4. Review | Classify the cycle's outcome (certified / near-miss / exhausted / no-candidate). Capture error signatures. |
| 5. Replan | Apply per-method widening rules; recommend next cycle's method + Step 2 pre-fills. If no lever remains, mark this cycle stuck. |
| 6. Continue/Stop | Always prompt the user: `continue / stop / adjust`. |

## Phase 1 — Plan

Cycle 1's Plan does the full one-time setup (Target Resolution Flow,
Shape Normalization, Search-Space Estimate, Cycle-Tracker init) and
then enters the Step 1 + Step 2 prompts. Cycle ≥2 skips the setup
sub-sections (TARGET, shape, search-space, tracker are reused) and
re-enters only the Step 1 + Step 2 prompts, with Replan's
recommendations pre-filling the answers.

### Target Resolution Flow

```text
target = (validated-invocation block) | positional argument
        ↓
disprove_target_resolve.py → {kind, file?, line?, name?}
        ↓
   file-line ──→ lean_diagnostic_messages(file)
              → lean_goal(file, line)         ← extracts the Prop
              → lean_hover_info(file, line, col)  ← if goal is empty
        ↓
   qualified-name ──→ lean_local_search(name) → lean_hover_info on hit
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

### Shape Normalization

Strip a leading prefix of binders from the inferred type and reclassify
the body. The seven canonical shapes:

| # | Shape | Disproof goal | Default method (Replan pre-fill) |
|---|-------|---------------|-----------------------------------|
| 1 | `∀ x : α, P x` | `∃ x, ¬ P x` | decide-cascade → mine → enumerate |
| 2 | `∀ x, P x → Q x` | `∃ x, P x ∧ ¬ Q x` | decide-cascade → mine → enumerate |
| 3 | `∃ x : α, P x` | `∀ x, ¬ P x` | decide-cascade (needs `Fintype α`, `DecidablePred P`) |
| 4 | `P ∧ Q` | `¬ P ∨ ¬ Q` | recurse on each conjunct |
| 5 | `P ∨ Q` | `¬ P ∧ ¬ Q` | recurse on both |
| 6 | `a = b` / arithmetic ineq | `a ≠ b` / `¬ (a ≤ b)` | decide-cascade (norm_num / omega) |
| 7 | Decidable atom `P` | `¬ P` | decide-cascade |

Mixed-quantifier prefixes (`∀ n m, …`) peel one layer at a time;
re-classify after each `intro`.

### Search-Space Estimate

```
Search-Space Estimate
  Shape         : <one of the seven above>
  Free vars     : <name : type (size)>, ...
  Candidates    : <feasible count> of <total>
  Decidable?    : <yes (instance) | no | partial>
  Known non-counterexamples (statement holds at):
    - <small values verified via decide>
    - lean_leansearch probe: "counterexample <keywords>" → <hit count>
```

The "Known non-counterexamples" line is required. Probe small values
(0, 1, 2, [], none, …) with `decide` or `norm_num` and report the ones at
which the statement holds. This tells the user the search is worth running
(if the statement fails at small values, `decide` would find it
immediately if picked as cycle 1's method).

### Cycle-Tracker init

```bash
bash "$LEAN4_SCRIPTS/cycle_tracker.sh" init \
  --max-cycles=<resolved> --max-stuck-cycles=<resolved> \
  --max-runtime=<resolved>
```

Disprove has no deep mode in v1: it never calls `can-deep` / `deep`,
so the deep counters maintained internally by the tracker are inert.
Omit the deep flags from `init` — passing `=0` would be rejected by
the tracker's `_require_positive_int` validation.

### Step 1 — Method Menu

```
Choose a search method for cycle <N>:
  1. decide-cascade  — decide / native_decide / norm_num / omega
  2. mine            — small literals + Inhabited instances
  3. enumerate       — bounded Fin / range
  4. plausible       — random property test (mathlib)
  5. tactics         — negated-goal tactic cascade
  6. lookup          — mathlib Counterexamples + repo grep
  7. external        — z3 / cvc5 (v1: stub; skipped)
  s. stop            — give up
```

One method is marked `[recommended]` and pre-selected by pressing Enter;
methods exhausted in earlier cycles are marked `[exhausted]` and cannot
be re-picked without explicit user override.

**Pre-fill order for the `[recommended]` tag** (highest priority first):

1. Explicit `--methods` CLI flag (cycle 1 only).
2. **Cycle 1 — shape-derived:** the first entry of the
   [Shape Normalization](#shape-normalization) table's "Default method"
   column for the resolved TARGET, refined by the Search-Space
   Estimate's `Decidable?` field. If `decide-cascade` is the first
   entry but `Decidable? = no`, drop to the next entry in the chain
   (e.g., shape 1 → `mine`). For shapes 4 (∧) and 5 (∨), the workflow
   may decompose into sub-targets and recurse; absent decomposition,
   the static fallback applies.
3. **Cycle ≥2 — Replan-derived:** the next-method output of the
   [Replan Rules](#replan-rules) table for the previous cycle's
   just-tried method and outcome.
4. **Static fallback:** option 1 (`decide-cascade`).

### Step 2 — Per-Method Configuration

Per-method prompts (default values shown):

```
[decide-cascade]
  Include native_decide? (adds Lean.ofReduceBool axiom)  [y/N]
  (decide / norm_num / omega run regardless; the toggle controls native_decide only)
```

```
[mine]
  Number of candidates? [10]
  Include Inhabited instances from imports? [Y/n]
```

```
[enumerate]
  Range type? [Fin / range / both] (default both)
  Range start? [5]
  Range end?   [64]
  Atom tactic per candidate? [decide / norm_num / omega] (default decide)
```

```
[plausible]
  Number of samples? [200]
  Random seed? [auto]
```

```
[tactics]
  Tactics to include? [rfl, simp, decide, native_decide, omega, norm_num, grind, linarith]
                       (toggle individually or accept all)
```

```
[lookup]
  Include 1× lean_leansearch query? [Y/n]
  Search mathlib `Counterexamples/`? [Y/n]
  Search repo for *_counterexample / *_counter / "false" comments? [Y/n]
```

```
[external]
  (v1) Solver wiring is a stub. Skip and choose another method?
```

**Pre-fill order for each field** (highest priority first):

1. **Replan's recommendation** (cycle ≥2 only) — output of the
   [Replan Rules](#replan-rules) table for the just-tried method.
2. **Derived from the Search-Space Estimate** (cycle 1, when the SSE
   provides a usable value):
   - `enumerate.range_type` ← `Fin` if the relevant binder is `Fin _`;
     `range` for `Nat`/`Int`; `both` for mixed binders.
   - `enumerate.range_end` ← `min(Fintype.size, 64)` when the type has
     a known `Fintype` instance; `64` for unbounded `Nat`/`Int`. For
     multi-variable targets (e.g., `∀ a b : Nat, P a b`), divide the
     budget per variable (e.g., 16 per var to keep the candidate grid
     ≤ 64²).
   - `enumerate.atom_tactic` ← `omega` if the residual is
     integer-linear; `norm_num` for arithmetic equalities with
     numerals; `decide` otherwise.
   - `mine.candidates` ← type-shaped literal set (`Nat`: small
     non-negatives + `Inhabited`; `Int`: small signed + `Inhabited`;
     `List`/`Option`: empties + `Inhabited`; `Bool`: both values;
     `Fin n`: all elements if `n ≤ candidates count`, else first `n`).
   - `plausible.samples` ← `min(Fintype.size × 2, 200)` for finite
     types; `200` otherwise. If the type is small and finite, prefer
     `enumerate` over `plausible` outright (no point sampling when
     exhaustive search fits the budget).
   - `tactics.cascade` ← prefix the cascade with the shape-natural
     tactic (`omega`/`norm_num` for arithmetic shapes 6/7; `decide` /
     `native_decide` for decidable atoms; `rfl`/`simp` for structural
     shapes); the full cascade still runs as fallback.
   - `decide-cascade.native_decide` ← `N` by default (axiom-introducing
     and audit-worthy; opt-in only).
   - `lookup` toggles ← all three sources on by default; Search-Space
     Estimate may turn off the `lean_leansearch` query when the TARGET
     keywords are too generic to be useful (e.g., a single-letter
     identifier).
3. **Static fallback** — the bracketed value shown in the per-method
   block above. Used only when neither (1) nor (2) supplies a value.

The Search-Space Estimate (Phase 1) is the canonical source for the
type, size, and decidability information that tier (2) consumes; an
LLM agent following this workflow MUST consult the SSE output before
falling through to the static defaults.

## Phase 2 — Work

Run the chosen method with the chosen Step 2 config. For each candidate
witness:

1. Construct a per-shape Lean snippet
   ([Per-Shape Recipes](#per-shape-recipes) below).
2. Pre-screen via `lean_multi_attempt(file, line, snippets=[snippet])`.
3. On pass, advance to Checkpoint.
4. On fail, record the residual error signature (used by Review).

Method outcomes for this cycle (consumed by Review):

| Outcome | Meaning |
|---------|---------|
| `certified` | A candidate passed pre-screen AND the file compile gate. |
| `near-miss` | A candidate passed pre-screen but `lake env lean` rejected it. The error signature is captured. |
| `exhausted-no-witness` | The method's budget was spent; no candidate was produced. |
| `no-candidate` | The method produced zero candidates (e.g., enumerate hit no `DecidablePred`). |

### Method Registry

The Step 1 menu surfaces these methods. Step 2's prompts are the
parameters each method accepts.

#### `decide-cascade`

| | |
|---|---|
| Applies to | closed decidable Props; `∀ x : α, P x` with `[Fintype α]`, `[DecidablePred P]`; arithmetic equalities/inequalities |
| Candidate | none — kernel/decision procedure decides directly |
| Step 2 toggle | `Include native_decide?` (default off; adds `Lean.ofReduceBool` axiom) |
| Budget | ~1s `decide` / `norm_num` / `omega`; ~5s `native_decide` |
| False-negative | no `Decidable` instance; nonlinear arithmetic |
| Cert snippet | `example : ¬ TARGET := by decide` (or `native_decide`, `norm_num`, `omega`) |

#### `mine` — Constructor / literal mining

| | |
|---|---|
| Applies to | shapes 1, 2 |
| Candidates | from small literals (`0`, `1`, `2`, `[]`, `none`, `some 0`), `Inhabited` instances in scope (toggle in Step 2), project-local example defs |
| Step 2 | number of candidates (default 10); include Inhabited instances (default yes) |
| Per-candidate cert | atom cascade (`decide` → `norm_num` → `omega`) |

#### `enumerate` — Bounded enumeration

| | |
|---|---|
| Applies to | shapes 1, 2 over `ℕ`, `ℤ`, `Fin n`, finite lists |
| Step 2 | range type (Fin / range / both); range start (default 5); range end (default 64); atom tactic (default `decide`) |
| Candidates | iterate `List.range n` / `Fin.elems`; Replan typically doubles `range end` cycle-over-cycle |
| Cert | per-candidate atom cascade |

#### `plausible` — Mathlib's property tester

| | |
|---|---|
| Applies to | any shape with `SampleableExt` instances |
| Step 2 | number of samples (default 200); random seed (auto) |
| Candidates | `by plausible` reports a sample |
| Cert lifting | only if residual `¬ P w` is decidable; otherwise → near-miss `WITNESS_UNCERTIFIED` |
| Requires | `import Mathlib.Tactic.Plausible` in the file's transitive closure (probe via `lean_run_code` before using) |

#### `tactics` — Negated-goal tactic cascade

| | |
|---|---|
| Applies to | any shape, as a residual finisher |
| Step 2 | which tactics to include (default: `rfl`, `simp`, `decide`, `native_decide`, `omega`, `norm_num`, `grind`, `linarith`) |
| Budget | 15s |

#### `external` — SAT/SMT (v1 stub)

| | |
|---|---|
| Applies to | bit-vectors, linear arithmetic, EUF (in principle) |
| v1 status | **not wired** — Step 2 prompt informs the user and asks to pick a different method |
| v2 plan | out-of-process z3, port literal model back as a Lean witness, run atom cascade on the residual |
| v2 dispatch | run via a subagent (analogous to prove's `sorry-filler-deep`) so the main thread stays responsive while the solver works |

#### `lookup` — Local + mathlib known-counterexamples

| | |
|---|---|
| Step 2 | toggle `lean_leansearch` query; toggle mathlib `Counterexamples/` grep; toggle repo grep |
| Source 1 | grep `Mathlib/Counterexamples/` and similar paths |
| Source 2 | repo-local grep for `*_counterexample`, `*_counter`, comments mentioning "false" near the target |
| Source 3 | one `lean_leansearch` query: `counterexample <keywords from TARGET>` |
| Budget | 10s |
| Cert | if a Counterexamples entry is a *match*, adopt its lemma name (the entry already typechecks); if only similar, list as advisory |

## Phase 3 — Checkpoint

If Work produced a `certified` outcome this cycle:

1. Construct the per-shape `T_counterexample` Lean snippet
   ([Per-Shape Recipes](#per-shape-recipes) below). Apply atom-slot
   hot-swap if the first cert tactic fails (see the cascade order
   documented with the recipes).
2. Append via
   `python3 "$LEAN4_SCRIPTS/disprove_emit_artifact.py" --scope-file=<target-file> --theorem-name=T_counterexample`
   (snippet on stdin).
3. Run `lake env lean <target-file>` from the project root.
4. Pass → record outcome `certified`, proceed to Review.
   Fail → revert the appended hunk; downgrade outcome to `near-miss`,
   capture the error signature.

Per `--commit`:
- `auto` — stage the modified file (`git add <target-file>`, never `-A`)
  and commit `disprove: T_counterexample — cycle N`.
- `ask` — show the diff and prompt the user.
- `never` — leave staging to `/lean4:checkpoint`.

If Work produced no `certified` outcome: no artifact, no rollback —
nothing was written this cycle.

### Per-Shape Recipes

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
-- escalations: native_decide → norm_num → omega
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
(`decide → native_decide → norm_num → omega → simp → rfl`).

**Shape 4 — `P ∧ Q` (disprove one conjunct):**

Pick whichever conjunct yields the smaller search; obtain `h : ¬ P` (or
`h : ¬ Q`) via the matching Shape 1/2/7 recipe, then wrap by pattern
match:

```lean
theorem T_counterexample (h : ¬ P) : ¬ (P ∧ Q) := fun ⟨hp, _⟩ => h hp
-- mirror with `fun ⟨_, hq⟩ => h hq` when disproving Q
```

**Shape 5 — `P ∨ Q` (disprove both disjuncts):**

Recurse on both — obtain `hp : ¬ P` and `hq : ¬ Q` via the matching
Shape 1/2/7 recipes, then combine:

```lean
theorem T_counterexample (hp : ¬ P) (hq : ¬ Q) : ¬ (P ∨ Q) :=
  fun h => h.elim hp hq
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
  Method            : <name>
  Config            : <method-specific key=value list>   e.g. "range=[5,64), atom=decide"
  Outcome           : certified | near-miss | exhausted-no-witness | no-candidate
  Candidates tried  : <K>
  Time              : <T>
  Near-miss signature (if any) : <error-key>  e.g. "decide: failed to reduce ¬ (n^2 + n + 41).Prime"
```

Review feeds Replan: the outcome + near-miss signature determines which
widening rule fires next.

## Phase 5 — Replan

After a cycle that didn't certify, Replan inspects the last cycle's
Review outcome and recommends the next cycle's method + Step 2 pre-fills.

### Replan Rules

| Last-cycle method | If `exhausted-no-witness` | If `near-miss` | If `no-candidate` |
|-------------------|---------------------------|----------------|-------------------|
| decide-cascade | Recommend `mine` next; if `native_decide` was off, suggest enabling it in Step 2 | — | Recommend `mine` or `enumerate` |
| mine | Recommend `enumerate` | Recommend `enumerate` with range around the near-miss | Recommend `lookup` |
| enumerate | Recommend `enumerate` again with range end × 2 | Recommend `enumerate` with range tightened around the near-miss | Recommend `plausible` |
| plausible | Recommend `enumerate` (if `SampleableExt` couldn't generate); else recommend `plausible` with 2× samples | Lift the near-miss witness into a probe and recommend `decide-cascade` for cert | Recommend `lookup` |
| tactics | Recommend `mine` | — | Recommend `lookup` |
| lookup | — | Adopt the matching mathlib Counterexample directly (skip to Checkpoint with that lemma name) | Recommend `external` (v1: stub) |

If a recommendation is generated, Replan **pre-fills** the next cycle's
Step 1 selection and Step 2 fields. The user can accept (Enter), override
in Continue/Stop's `adjust` branch, or stop.

### Stuck Definition for Disprove

A cycle is **stuck** when **both** hold:
- It produced no `certified` outcome (Review = near-miss /
  exhausted-no-witness / no-candidate), AND
- Replan has no recommendation (every method either exhausted-no-witness
  with no remaining widening, or already tried with no near-miss).

Two consecutive stuck cycles → the session bails with `INCONCLUSIVE` on
the next Continue/Stop boundary.

## Phase 6 — Continue / Stop

Always prompt the user:

```
Cycle N complete.
  Outcome: <certified | near-miss | exhausted-no-witness | no-candidate>
  Replan recommends: <method> with <key config values>

- [continue] — run cycle N+1 with Replan's recommendation
- [stop]     — accept current outcome, emit Disprove Summary
- [adjust]   — override Replan before next cycle
```

After the user decides:

```bash
# At every cycle boundary:
bash "$LEAN4_SCRIPTS/cycle_tracker.sh" tick --stuck=<yes|no>

# Just before emitting the Disprove Summary (on session stop):
bash "$LEAN4_SCRIPTS/cycle_tracker.sh" status
bash "$LEAN4_SCRIPTS/cycle_tracker.sh" stop
```

`tick` enforces `--max-cycles` and `--max-stuck-cycles` at the cycle
boundary. `--max-runtime` is checked here too (best-effort).

## Disprove Summary

The Disprove Summary is a single tri-state report: `FALSE`,
`WITNESS_UNCERTIFIED`, or `INCONCLUSIVE`. For the full template and the
per-outcome handoff bullets, see
[commands/disprove.md § Disprove Summary](../../../commands/disprove.md#disprove-summary)
— it is the canonical source.

## Safety

- **Append-only.** Never rewrite an existing
  `theorem T : P := by sorry` declaration to `: ¬ P`. The artifact
  emitter (`disprove_emit_artifact.py`) enforces this — it refuses to
  modify or duplicate existing declarations.
- **No `native_decide` without opt-in.** Each cycle's Step 2 prompt for
  `decide-cascade` asks whether to enable `native_decide`. Default off:
  `native_decide` adds the `Lean.ofReduceBool` axiom and is audit-worthy.
- **No claim of `FALSE` without compile gate.** Pre-screen via
  `lean_multi_attempt` is necessary but not sufficient; only
  `lake env lean <path>` from the project root licenses the `FALSE`
  claim.
