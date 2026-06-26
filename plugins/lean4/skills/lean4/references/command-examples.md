# Command Examples

Extended examples and session transcripts for Lean4 plugin commands.

---

## draft

### Skeleton-Only Drafting

````
User: /lean4:draft "Every continuous function on a compact set is bounded"

Claude: Parsing claim and drafting skeleton...

## Theorem Skeleton

```lean
theorem continuous_on_compact_bounded
    {X : Type*} [TopologicalSpace X] [MetricSpace X]
    {Y : Type*} [MetricSpace Y]
    {K : Set X} (hK : IsCompact K)
    {f : X → Y} (hf : ContinuousOn f K) :
    IsBounded (f '' K) := by
  sorry
```

Elaboration check (--elab-check=best-effort)... ✓ (1 sorry, no other diagnostics)

What next?
- [alternative] Different formalization (e.g., using Bornology)
- [save to scratch] Write to scratch file
````

### Attempt Mode

````
User: /lean4:draft --mode=attempt "The sum of two continuous functions is continuous"

Claude: Parsing claim and drafting skeleton...

```lean
theorem continuous_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (f + g) := by
  sorry
```

Attempting proof (--mode=attempt)...
lean_local_search("Continuous add") → found `Continuous.add`
Trying: `exact hf.add hg`
Diagnostics... ✓

Proof found! Skeleton upgraded from sorry to verified proof.

What next?
- [show source] See the mathlib proof
- [alternative] Different formalization
- [save to scratch] Write to scratch file
````

---

## formalize

### Interactive Synthesis

````
User: /lean4:formalize "Every continuous function on a compact set is bounded"

Claude: ## Phase 1: Draft

Parsing claim and drafting skeleton...

```lean
theorem continuous_on_compact_bounded
    {X : Type*} [TopologicalSpace X] [MetricSpace X]
    {Y : Type*} [MetricSpace Y]
    {K : Set X} (hK : IsCompact K)
    {f : X → Y} (hf : ContinuousOn f K) :
    IsBounded (f '' K) := by
  sorry
```

Elaboration check... ✓
Attempting proof (--draft-mode=attempt)...
lean_local_search("IsCompact ContinuousOn IsBounded image") → found it

## Phase 2: Prove

Trying: `exact hK.image_of_continuousOn hf |>.isBounded`
Diagnostics... ✓

Proof complete (--rigor=checked: no sorry, clean diagnostics, standard axioms).

What next?
- [show source] See the mathlib proof
- [alternative] Different formalization (e.g., using Bornology)
- [generalize] Weaken hypotheses
- [strengthen] Add conclusions
- [save to scratch] Write to scratch file
````

### Axiomatic Draft

````
User: /lean4:formalize --rigor=axiomatic "The p-adic numbers are complete"

Claude: Drafting formalization with explicit assumptions...

```lean
namespace Assumptions

-- Assumption Ledger
-- ┌──────────────────────────────┬────────────────────────┬───────────┬─────────────────────┐
-- │ Assumption                   │ Justification          │ Scope     │ Introduced by       │
-- ├──────────────────────────────┼────────────────────────┼───────────┼─────────────────────┤
-- │ [MetricSpace (Padic p)]     │ standard p-adic metric │ instance  │ assistant-inferred  │
-- │ hp : Fact (Nat.Prime p)     │ p must be prime        │ parameter │ user-stated         │
-- └──────────────────────────────┴────────────────────────┴───────────┴─────────────────────┘

theorem padic_complete (p : ℕ) [hp : Fact (Nat.Prime p)] :
    CompleteSpace (Padic p) := by
  sorry -- ⚠ proof blocked: needs Mathlib.NumberTheory.Padics.PadicIntegers
```

lean4-skills-check-axioms-inline <target>.lean --report-only → ✓ standard axioms only

Note: Mathlib likely has this as an instance. Searching...
lean_leanfinder("CompleteSpace Padic") → `Padic.instCompleteSpace`

This is already a registered instance in mathlib. No axioms or assumptions needed.

What next?
- [show source] See how mathlib proves completeness
- [deeper] Explore the p-adic metric construction
````

---

## prove

### Basic Usage

```
/lean4:prove                         # Start guided session
/lean4:prove File.lean               # Focus on specific file
/lean4:prove --repair-only           # Fix build errors without filling sorries
```

### Full Session Example

```
User: /lean4:prove

Claude: Discovering current state...

Using LSP:
- lean_diagnostic_messages(.) → 2 errors, 5 warnings
- lean_goal at each sorry → 8 goals to prove

## Prove Plan

**Found:** 8 sorries in 3 files
**Approach:** Balanced
**Review:** Every 5 changes

### Sorries Found
- `Helpers.lean:15` - in `trivial_lemma`
- `Helpers.lean:42` - in `helper_bound`
- `Core.lean:89` - in `main_theorem`
...

**Proceed?** (yes / adjust / cancel)

User: yes

Claude: Working on Helpers.lean:15 - `trivial_lemma`...

Goal: ⊢ 0 ≤ 1

Searching mathlib... Found: `Nat.zero_le`

Applying: `exact Nat.zero_le 1`
Building... ✓

Committing: "fill: trivial_lemma - exact Nat.zero_le"

[continues for each sorry...]
```

### Repair Mode Example

```
User: /lean4:prove --repair-only

Claude: Running repair mode...

Build errors found:
- Core.lean:42: type mismatch at application
- Core.lean:89: unknown identifier 'continuous_of_foo'

Repairing Core.lean:42...
Error: type mismatch, expected `ℕ`, got `ℤ`
Fix: Adding coercion with `↑`
Building... ✓

Repairing Core.lean:89...
Searching mathlib for 'continuous_of_foo'...
Found: `Continuous.comp` in Mathlib.Topology.Basic
Fix: Replacing with correct lemma name
Building... ✓

## Repair Complete
- Errors fixed: 2/2
- Build status: ✓ passing
```

### Review Checkpoint Example

```
## Progress

**Filled:** 5/8 sorries
**Commits:** 5 new
**Build:** passing

**Current:** Core.lean:89 - `main_theorem`
**Status:** Searching mathlib...

**Options:**
- `continue` - Keep going
- `stop` - Save progress and exit
- `skip` - Skip current sorry, try next
- `rollback N` - Undo last N commits
```

---

## autoformalize

### Basic Usage

```
/lean4:autoformalize --source ./paper.pdf --claim-select=first --out=Paper.lean
/lean4:autoformalize --source ./paper.pdf --claim-select=regex:"Theorem.*" --out=Paper.lean --rigor=checked
```

### Full Session Example

```
User: /lean4:autoformalize --source ./paper.pdf --claim-select=first --out=Paper.lean

Claude: Extracting claims from ./paper.pdf...
Found 4 claims in document order:
  1. Theorem 2.1 (Continuity bound)
  2. Lemma 2.3 (Monotone helper)
  3. Theorem 3.1 (Main convergence)
  4. Corollary 3.2 (Uniform bound)

Applying --claim-select=first → queue: [Theorem 2.1]

[Synthesis — Claim 1/1: Theorem 2.1]
Drafting "Theorem 2.1"...
  draft → temp file (declaration-only block, fully-qualified names)
  Outer loop: append to Paper.lean with boundary marker
  lean_diagnostic_messages(Paper.lean) → ✓
  Committing: "draft: Theorem 2.1 continuity bound"

Starting inner cycle on Paper.lean...
[Cycle 1] Working on Paper.lean:18 - `continuity_bound`
  Goal: ⊢ ∀ x ∈ K, ‖f x‖ ≤ C
  lean_leanfinder("IsCompact ContinuousOn norm bound") → found candidate
  Applying: `exact hK.isCompact.norm_le_of_continuousOn hf` ✓
  Committing: "fill: continuity_bound - isCompact.norm_le"

Sorry-free. Queue empty.

## Autoformalize Summary

**Reason stopped:** queue-empty (all claims attempted)

| Metric | Value |
|--------|-------|
| Claims attempted | 1/1 |
| Sorries before | 0 |
| Sorries after | 0 |
| Cycles run | 1 |
| Stuck cycles | 0 |
| Deep invocations | 0 |
| Time elapsed | 3m |
| Drafts | 1 |

**Handoff recommendations:**
- All sorries filled. Run /lean4:checkpoint to save.
```

---

## autoprove

### Basic Usage

```
/lean4:autoprove                        # Start autonomous session
/lean4:autoprove File.lean              # Focus on specific file
/lean4:autoprove --max-cycles=10        # Limit total cycles
```

### Full Session Example

```
User: /lean4:autoprove

Claude: Discovering current state...

Using LSP:
- lean_diagnostic_messages(.) → 2 errors, 5 warnings
- lean_goal at each sorry → 8 goals to prove

Starting autonomous loop (max-cycles=20, max-stuck=3)...

[Cycle 1] Working on Helpers.lean:15 - `trivial_lemma`...
Goal: ⊢ 0 ≤ 1
Applying: `exact Nat.zero_le 1` ✓
Committing: "fill: trivial_lemma - exact Nat.zero_le"

[Cycle 1] Working on Helpers.lean:42 - `helper_bound`...
Goal: ⊢ a + b ≤ b + a
Applying: `linarith` ✓
Committing: "fill: helper_bound - linarith"

Checkpoint: 2 sorries filled, build passing ✓
Review: No blockers found, continuing...

[Cycle 2] Working on Core.lean:89 - `main_theorem`...
Stuck: Same error after 2 attempts
Running stuck review...
Replanning: Search Mathlib.Topology.Order for tendsto variants
[continues autonomously...]
```

See [cycle-engine.md](cycle-engine.md#stuck-definition) for stuck detection logic and [deep mode](cycle-engine.md#deep-mode) for escalation behavior.

### Stop Condition Example

```
## Autoprove Summary

**Reason stopped:** max-stuck (3 consecutive stuck cycles)

| Metric | Value |
|--------|-------|
| Sorries before | 8 |
| Sorries after | 3 |
| Cycles run | 7 |
| Stuck cycles | 3 |
| Deep invocations | 2 |
| Time elapsed | 45m |

**Handoff recommendations:**
- Run /lean4:prove for guided work on remaining 3 sorries
- Review stuck blockers: Core.lean:89, Core.lean:156, Bounds.lean:42
```

### Deep Rollback Example

```
[Cycle 4] Working on Core.lean:89 - `main_theorem`...
Stuck after 3 attempts. Escalating to deep mode (--deep=stuck)...

Creating snapshot (--deep-snapshot=stash)...
Snapshot captured: <snapshot-id>

Deep phase 1: Extracting helper lemma to Helpers.lean
  Compile: ✓ (sorry count: 1 → 1, no new diagnostics)
Deep phase 2: Filling sorry using helper
  Compile: ✗ — sorry count increased (1 → 3)

Regression detected (--deep-regression-gate=strict):
  Sorry count: 1 → 3 (+2 regression)
  Rolling back to <snapshot-id>...
  Rollback: ✓
  Marking stuck: "deep: regression — sorry count increased from 1 to 3"

Stuck handoff:
- Deep abort reason: regression (sorry count +2)
- Strategy attempted: helper extraction to Helpers.lean
- LSP queries: lean_leanfinder("convergence bound"), lean_local_search("tendsto")
- Recommendation: try alternative approach or manual guidance

Running stuck review...

Note: if rollback itself fails, the cycle stops immediately —
no checkpoint is created, and the sorry is marked stuck with
"deep: rollback failed".
```

**Edge case — new diagnostic errors (sorry count unchanged):**

```
Deep phase 1: Refactoring Filter usage in Core.lean
  Compile: sorry count 1 → 1, but 2 new type mismatch errors

Regression detected (--deep-regression-gate=strict):
  New diagnostics: 2 errors not present in pre-deep baseline
  Rolling back to <snapshot-id>...
  Marking stuck: "deep: regression — new errors"
```

---

## disprove

### Basic Usage

```
/lean4:disprove Foo.lean:42                       # File + line (sorry/declaration site)
/lean4:disprove MyNs.SubNs.myThm                  # Qualified theorem name
/lean4:disprove Foo.lean:42 --max-cycles=5
/lean4:disprove Foo.lean:42 --commit=never
```

`/lean4:disprove` is always interactive — every cycle's Plan phase
presents Step 0 (Knowledge Search Menu), Step 1 (Method Menu), and
Step 2 (Config Menu) — three dynamic menus the cycling LLM proposes
for user review and approval.

### Cycle 1 — decide-cascade Win Example

A simple bounded universal: Step 0 runs quickly with the default Lean +
local items (no cited findings), the dynamic Step 1 menu ranks
`decide-cascade` at rank 1 (because `Target Profile.decidable=yes` and
no decide-family success has been recorded yet); the cycle's candidate
pre-screens clean in Phase 2 and is certified by the Phase 3 gate.

```
User: /lean4:disprove Bad.lean:3

Claude: Resolved Inputs
- target:                       Bad.lean:3 (kind=file-line)
- --commit:                     ask (default)
- --max-cycles:                 3
- --max-stuck-cycles:           2
- --max-runtime:                5m
- --knowledge-search-budget:    3

Resolving target...
  lean_goal(Bad.lean, 3) → ∀ n : Nat, n < 10
  Shape: 1 (∀ x, P x)

Target Profile
  shape          : 1 (∀ n : Nat, n < 10)
  free_vars      : n : Nat (∞)
  fintype_size   : ∞
  decidable      : yes
  candidate_grid : [0, 64) default window

=== Cycle 1 — Plan ===

Step 0 — Knowledge Search Menu (visit 1/3):
  [lean]   lean_leansearch: "counterexample ∀ n : Nat, n < 10"
  [local]  grep mathlib/Counterexamples/ for "bounded"
  [local]  grep repo for "*_counterexample" near Bad.lean
  [web]    websearch: known counterexample search methods
  [web]    websearch: known NON-counterexamples for "∀ n : Nat, n < 10"
  [web]    websearch: known counterexamples for "∀ n : Nat, n < 10"
  [custom] (none)
  [llm]    (none)
Approve [yes / edit / reduce] > yes

Step 0 — running 6 queries...
  0 cited findings (web/local hits had no source_url and were dropped).

Step 1 — Search method for cycle 1:
  1. (Recommended) [family: decide-cascade]  [cheap]
     decide / native_decide / norm_num / omega — Target Profile.decidable=yes
     and no decide-family success yet, so this is the obvious first move.
     Cost (~wall-clock): ~1s
  2. [family: mine]                          [cheap]
     small literals + Inhabited — useful if decide times out.
     Cost (~wall-clock): ~5s
  3. [family: enumerate]                     [medium]
     iterate Nat in [5, 64) with atom=decide — falls back if mine misses.
     Cost (~wall-clock): ~1m
  --
  knowledge search (1/3 visits used; available)
  custom method   (specify your own approach)

> [Enter — accept rank 1]

Step 2 — Configure decide-cascade:
  1. (Recommended) native_decide=off
     Pure-Lean decide — no axioms; full ∀ check within elaborator budget.
     Cost (~wall-clock): ~1s
     Coverage:           atomic (decides the ∀-statement directly)
  2. native_decide=on
     Adds Lean.ofReduceBool axiom; ~5× faster but audit-worthy.
     Cost (~wall-clock): ~0.2s
     Coverage:           atomic (decides the ∀-statement directly)
  --
  custom-config

> [Enter — accept rank 1]

=== Cycle 1 — Work ===

Running decide-cascade on ¬ (∀ n : Nat, n < 10)...
  decide ✓ candidate found (pre-screen passed) in 0.4s

=== Cycle 1 — Checkpoint ===

Constructing T_counterexample : ∃ n : Nat, ¬ (n < 10) := ⟨10, by decide⟩
Gate-only T_counterexample_negates_target : ¬ (∀ n : Nat, n < 10) :=
  not_forall.mpr T_counterexample
Appended to Bad.lean.
Compile gate (lake env lean Bad.lean): passed.
Axiom gate (T_counterexample_negates_target): ⊆ {propext, Classical.choice, Quot.sound} — passed.
Dropped gate-only wrapper; committing T_counterexample (re-checked: passed).

Commit this change? [yes / no]
> yes

Committed: "disprove: T_counterexample — cycle 1"

=== Cycle 1 — Review ===
  Method            : decide-cascade
  Config            : native_decide=off
  Outcome           : certified
  Time              : actual 0.4s  (estimated ~1s; from picked Step 2 entry's Cost)
  Step 0 visits     : 1/3

(Accumulate / Continue-Stop skipped: certified outcome ends the session.)

## Disprove Summary

**Outcome:** REFUTED

| Metric | Value |
|--------|-------|
| Target | Bad.lean:3 |
| Witness | 10 (via decide) |
| Artifact theorem | T_counterexample |
| Artifact file | Bad.lean |
| Build gate | passed |
| Axiom gate | passed (⊆ {propext, Classical.choice, Quot.sound}) |
| Cycles run | 1 |
| Stuck cycles | 0 |
| Time elapsed | 0.6s |

**Per-cycle attempts:**

| # | Method (family) | Config            | Outcome   | URL |
|---|-----------------|-------------------|-----------|-----|
| 1 | decide-cascade  | native_decide=off | certified | —   |

Counterexample certified and committed (see `git log -1`).
```

### Cycle 1 mine miss → cycle 2 enumerate widen + certify

A widening pass over an infinite ℕ-quantifier: cycle 1's `mine` exhausts
without a witness; cycle 2's dynamic Step 1 menu **promotes** `enumerate`
based on the accumulated `(mine, exhausted-no-witness)` evidence plus a
Step 0 web finding that cites `n=40`, and the cycle certifies.

```
User: /lean4:disprove Conjecture.lean:18

Claude: Resolved Inputs (defaults)

Resolving target...
  lean_goal(Conjecture.lean, 18) → ∀ n : Nat, Nat.Prime (n^2 + n + 41)
  Shape: 1 (∀ x, P x)

Target Profile
  shape          : 1 (∀ n : Nat, Nat.Prime (n^2 + n + 41))
  free_vars      : n : Nat (∞)
  fintype_size   : ∞
  decidable      : no            ← (∀ n : Nat, …) has no Decidable instance
  candidate_grid : [0, 64) default window

=== Cycle 1 — Plan ===

Step 0 — Knowledge Search Menu (visit 1/3):
  [lean]   lean_leansearch: "Euler prime polynomial counterexample"
  [local]  grep mathlib/Counterexamples/
  [local]  grep repo for "prime_polynomial_*"
  [web]    websearch: known NON-counterexamples for "n^2 + n + 41 prime"
  [web]    websearch: known counterexamples for "n^2 + n + 41 prime"
  [custom] (none)
  [llm]    (none)
Approve [yes / edit / reduce] > yes

Step 0 — running 5 queries...
  Web finding: "Euler's prime-generating polynomial fails first at n=40"
    source_url = en.wikipedia.org/wiki/Formula_for_primes#Euler_polynomial
    WebFetch on cited URL: ok (content matches).
    verified_via = webfetch:…wikipedia.org/wiki/Formula_for_primes
    confidence = high
  Lean / local: 0 hits.

Step 1 — Search method for cycle 1:
  1. (Recommended) [family: mine]   [cheap]
     Try small literals first — cheap exhaustion; the web finding hints
     at a witness around n=40, past the default literal set, so mine
     likely misses but lets cycle 2 specialize enumerate around that point.
     Cost (~wall-clock): ~5s
  2. [family: enumerate]             [medium]
     Iterate Nat in [5, 64) with atom=decide — direct route to the
     web-cited witness; cycle 1 could also start here.
     Cost (~wall-clock): ~1m
  3. [family: tactics]               [medium]
     residual cascade — useful if either mine or enumerate near-misses.
     Cost (~wall-clock): ~15s
  --
  knowledge search (1/3 visits used; available)
  custom method

> 1   (user accepts mine)

Step 2 — Configure mine:
  1. (Recommended) candidates=10, include_inhabited=true
     Standard mining; web finding's n=40 is past the literal set, so
     this likely misses — expect cycle 2 to widen.
     Cost (~wall-clock): ~5s
     Coverage:           list: 10 named candidates (literals + Inhabited)
  2. candidates=50, include_inhabited=true
     Aggressive; still misses if literals max at ~30.
     Cost (~wall-clock): ~25s
     Coverage:           list: 50 named candidates (literals + Inhabited)
  --
  custom-config

> [Enter — accept rank 1]

=== Cycle 1 — Work ===

Running mine: trying {0, 1, 2, -1, [], none, some 0, Inhabited.default …}
  All 10 candidates: residual `Nat.Prime (n^2 + n + 41)` reduces to True.
  Outcome: exhausted-no-witness.

=== Cycle 1 — Review ===
  Method            : mine
  Config            : candidates=10, include_inhabited=true
  Outcome           : exhausted-no-witness
  Time              : actual 4.8s  (estimated ~5s; from picked Step 2 entry's Cost)
  Step 0 visits     : 1/3

=== Cycle 1 — Accumulate ===
  Appended: (family=mine, config={candidates:10, include_inhabited:true},
             outcome=exhausted-no-witness)
  Session evidence size: 1 record.

Cycle 1 complete (exhausted-no-witness).
  Next cycle's Step 1 preview: [enumerate] range=[5,64), atom=decide
                               (promoted by accumulated mine evidence +
                                Step 0 web finding citing n=40)
- [continue] / [stop]
> continue

=== Cycle 2 — Plan ===

(Step 0 skipped — Step 1 did not pick `knowledge search`.)

Step 1 — Search method for cycle 2:
  1. (Recommended) [family: enumerate]  [medium]
     Iterate Nat in [5, 64) — the (mine, candidates=10) pair is in the
     failed evidence so it's excluded from the top 3; the web finding
     citing n=40 falls inside this window.
     Cost (~wall-clock): ~30s
  2. [family: plausible]                 [medium]
     200 random Nat samples — broader but probabilistic.
     Cost (~wall-clock): ~30s
  3. [family: tactics]                   [medium]
     residual cascade — last resort if enumerate near-misses.
     Cost (~wall-clock): ~15s
  --
  knowledge search (1/3 visits used; available)
  custom method

> [Enter — accept rank 1]

Step 2 — Configure enumerate:
  1. (Recommended) range_type=both, range_start=5, range_end=64, atom_tactic=decide
     Hits the web finding's n=40 within the window; decide as atom.
     Cost (~wall-clock): ~30s
     Coverage:           window: 59/∞ over Nat (covers [5, 64))
  2. range_type=range, range_start=5, range_end=128, atom_tactic=decide
     Wider window; ~2× cost.
     Cost (~wall-clock): ~1m
     Coverage:           window: 123/∞ over Nat (covers [5, 128))
  3. range_type=range, range_start=5, range_end=64, atom_tactic=norm_num
     Same window, norm_num atom for arithmetic predicates.
     Cost (~wall-clock): ~45s
     Coverage:           window: 59/∞ over Nat (covers [5, 64))
  --
  custom-config

> [Enter — accept rank 1]

=== Cycle 2 — Work ===

Running enumerate (n = 5 → 20 → 64, atom = decide)...
  n=5..39: holds (statement true at these values)
  n=40: Nat.Prime (40^2 + 40 + 41) = Nat.Prime 1681 = Nat.Prime (41 * 41) — false  ✓ candidate

=== Cycle 2 — Checkpoint ===

Constructing T_counterexample : ∃ n : Nat, ¬ Nat.Prime (n^2 + n + 41) :=
  ⟨40, by decide⟩
Gate-only T_counterexample_negates_target : ¬ (∀ n : Nat, Nat.Prime (n^2 + n + 41)) :=
  not_forall.mpr T_counterexample
Appended to Conjecture.lean.
Compile gate: passed.
Axiom gate (T_counterexample_negates_target): ⊆ {propext, Classical.choice, Quot.sound} — passed.
Dropped gate-only wrapper; committing T_counterexample (re-checked: passed).

Commit this change? [yes / no]
> yes

Committed: "disprove: T_counterexample — cycle 2"

## Disprove Summary

**Outcome:** REFUTED

| Metric | Value |
|--------|-------|
| Target | Conjecture.lean:18 |
| Witness | 40 |
| Artifact theorem | T_counterexample |
| Artifact file | Conjecture.lean |
| Build gate | passed |
| Axiom gate | passed (⊆ {propext, Classical.choice, Quot.sound}) |
| Cycles run | 2 |
| Stuck cycles | 0 |
| Time elapsed | 7.1s |

**Per-cycle attempts:**

| # | Method (family) | Config                                | Outcome              | URL |
|---|-----------------|---------------------------------------|----------------------|-----|
| 1 | mine            | candidates=10, include_inhabited=true | exhausted-no-witness | —   |
| 2 | enumerate       | range=[5,64), atom=decide             | certified            | —   |

Counterexample certified and committed (see `git log -1`).
```

### Three-cycle INCONCLUSIVE — verify-known-cex with WebFetch failure

A stubborn target: decide isn't applicable; enumerate's window misses;
plausible's sample budget exhausts. Cycle 2's Step 0 surfaces a web
finding that LOOKS like a known counterexample, but `WebFetch` fails to
verify the cited URL, so the candidate is **dropped rather than elevated**
to `[verify-known-cex]` — the cycle falls back through the regular method
ranking.

```
User: /lean4:disprove HardConjecture.lean:7 --max-cycles=3 --max-runtime=2m

Claude: Resolved Inputs (defaults; --max-cycles=3, --max-runtime=2m,
                          --knowledge-search-budget=3 default)

Resolving target... lean_goal → ∀ n : Nat, p n
  Target Profile
    shape          : 1
    decidable      : no            ← `p` lacks DecidablePred instance
    candidate_grid : [0, 64) default window

=== Cycle 1 — Plan ===
  Step 0 — visit 1/3: ran default Lean + local items; 0 cited findings.
  Step 1 — LLM proposes: [decide-cascade] rank 1 (~1s, atomic — but
           must-appear-in-top-3 invariant is OFF because decidable=no;
           the user picks it anyway to confirm), [mine] rank 2
           (~5s, list:10), [enumerate] rank 3 (~30s, window:59/∞).
  Step 2 — decide-cascade with native_decide=off (Cost ~1s, atomic).

=== Cycle 1 — Work ===  decide / native_decide / norm_num / omega — all
                        report no DecidablePred instance. Outcome:
                        no-candidate.
=== Cycle 1 — Review ===  no-candidate; Time: actual ~0.5s (estimated ~1s); Step 0 visits 1/3
=== Cycle 1 — Accumulate ===
  Appended: (decide-cascade, {native_decide:false}, no-candidate)

Cycle 1 complete (no-candidate).
  Next cycle's Step 1 preview: [enumerate] range=[5,64), atom=decide
- [continue] / [stop]
> continue (at Step 1, pick `knowledge search` to override preview)

=== Cycle 2 — Plan ===
  Step 0 — visit 2/3 (entered via Step 1 `knowledge search`):
    Items: all 8 selected (web items included). Approve > yes.
    Web finding: "p fails at n=128" — source_url=example.com/preprint.pdf
    WebFetch on example.com/preprint.pdf: 404 (cited URL is dead).
    Finding dropped (verification failed; not elevated to [verify-known-cex]).
    Lean / local hits: 0.
  Step 1 — LLM proposes: no [verify-known-cex] entry (verification failed).
           [enumerate] rank 1 (~30s, window:59/∞ — widening from default);
           [plausible] rank 2 (~30s, sampled:200); [tactics] rank 3 (~15s).
  Step 2 — enumerate with range=[5,200), atom=decide (Cost ~2m,
           window:195/∞ — user widened past the LLM's range_end=64
           seed via custom-config).

=== Cycle 2 — Work ===  No counterexample in [0, 200);
                        outcome = exhausted-no-witness.
=== Cycle 2 — Review ===  exhausted-no-witness; Time: actual ~2m (estimated ~2m); Step 0 visits 2/3
=== Cycle 2 — Accumulate ===
  Appended: (enumerate, {range_type:range, range_start:5, range_end:200,
             atom_tactic:decide}, exhausted-no-witness)

> continue

=== Cycle 3 — Plan ===
  Step 0 — skipped (Step 1 did not pick `knowledge search`).
  Step 1 — LLM proposes: [plausible] rank 1 (~75s, sampled:500) — last
           remaining family with a widening lever; (enumerate,
           range_end:200) is in failed evidence so any (enumerate,
           ≤200) variant is excluded from top 3.
  Step 2 — plausible with samples=500, seed=auto (Cost ~75s, sampled:500).

=== Cycle 3 — Work ===  No counterexample after 500 samples;
                        outcome = exhausted-no-witness.
=== Cycle 3 — Review ===  exhausted-no-witness; Time: actual ~70s (estimated ~75s)
=== Cycle 3 — Accumulate ===
  Appended: (plausible, {samples:500, seed:auto}, exhausted-no-witness).
  Stuck check: no non-failed (family, config) pair remains for top 3 —
                cycle marked STUCK.

(--max-cycles=3 reached; budget exhausted before the second stuck cycle.)

## Disprove Summary

**Outcome:** INCONCLUSIVE

| Metric | Value |
|--------|-------|
| Target | HardConjecture.lean:7 |
| Witness | — |
| Artifact theorem | — |
| Artifact file | — |
| Build gate | skipped |
| Axiom gate | skipped |
| Cycles run | 3 |
| Stuck cycles | 1 |
| Time elapsed | 1m48s |

**Per-cycle attempts:**

| # | Method (family) | Config                                                                  | Outcome              | URL |
|---|-----------------|--------------------------------------------------------------------------|----------------------|-----|
| 1 | decide-cascade  | native_decide=off                                                        | no-candidate         | —   |
| 2 | enumerate       | range=[5,200), atom=decide                                               | exhausted-no-witness | —   |
| 3 | plausible       | samples=500, seed=auto                                                   | exhausted-no-witness | —   |

Coverage: enumerate covered [0, 200); plausible sampled 500.
Stop reason: max-cycles
Recommended: rerun with --max-cycles=<higher> and pick `knowledge search`
             in Step 1 (widens with fresh evidence), or hand off to
             /lean4:prove for a positive proof attempt.
```

See [disprove-engine.md](disprove-engine.md) for the per-phase mechanics,
Step 0 / Step 1 / Step 2 menus, the Accumulate state update, and
per-shape certification recipes.

---

## checkpoint

### Basic Usage

```
/lean4:checkpoint
/lean4:checkpoint "optional custom message"
```

### Full Session Example

```
User: /lean4:checkpoint

Claude: Creating checkpoint...

Compiling touched files...
✓ MyProject/Basic.lean compiled
✓ MyProject/Lemmas.lean compiled

Building project...
✓ lake build passed

Checking axioms...
✓ Standard axioms only (propext, Classical.choice)

Counting sorries...
→ 3 sorries remaining in 2 files

Staging changes...
→ 5 files modified

Creating commit...
✓ Commit a1b2c3d: checkpoint(lean4): 3 sorries remaining, build passing

## Checkpoint Created

Commit: a1b2c3d - checkpoint(lean4): 3 sorries remaining, build passing
Build: ✓ passing
Sorries: 3 remaining
Axioms: standard only

Next steps:
- Continue with /lean4:prove
- Push manually when ready: git push
```

### Rollback Examples

```bash
# Undo last commit, keep changes staged
git reset --soft HEAD~1

# Undo last commit, keep changes unstaged
git reset HEAD~1

# Undo last N commits
git reset HEAD~N
```

---

## review

### Basic Usage

```
/lean4:review                        # Review changed files (default)
/lean4:review File.lean              # Review specific file
/lean4:review File.lean --line=89    # Review single sorry
/lean4:review --scope=project        # Review entire project (prompts)
```

### Full Review Example

```
User: /lean4:review Core.lean

Claude: Running review on Core.lean...

## Lean4 Review Report
**Scope:** Core.lean (file — target default)

### Build Status
✓ Core.lean compiles successfully

### Sorry Audit (1 remaining)
- Core.lean:89 - `convergence_bound`
  Goal: `∀ ε > 0, ∃ N, ∀ n ≥ N, |f n - L| < ε`
  Suggestion: Search mathlib for `Metric.tendsto_atTop`

### Axiom Status
✓ Standard axioms only

### Style Notes
- Line 45: Consider `simp only [add_comm, mul_comm]` instead of `simp [*]`
- Line 78: Proof is 38 lines - consider extracting helper lemma

### Golfing Opportunities
- Line 23: `apply f; exact h` → `exact f h` (directness win)
- Line 56: `ext x; simp` - verify if `simp` alone suffices

### Complexity Summary
- Theorems in file: 8
- Average proof: 15 lines
- Longest: `convergence_bound` (38 lines)

### Recommendations
1. Fill `convergence_bound` sorry - likely in mathlib
2. Extract helper from long proof at line 78
3. Tighten `simp` calls for faster compilation
```

### External Tool Integration Example

```
User: /lean4:review Core.lean --codex

Claude: Running review with Codex integration...

## Lean4 Review Report

### Build Status
✓ Core.lean compiles

### Sorry Audit
- Line 89: `convergence_bound` - needs proof

### Codex Suggestions
- Line 89: "Search Mathlib for `tendsto_atTop` variants — goal shape matches convergence lemmas"
- Line 45: "Broad `simp` may slow compilation — consider narrowing to specific lemmas"

### Claude Analysis
[standard review sections...]
```

### Custom Hook Interface

See [review-hook-schema.md](review-hook-schema.md) for full input/output schemas and example scripts.

### Stuck Review Example

See [cycle-engine.md](cycle-engine.md#stuck-definition) for stuck detection criteria.

```
[Autoprove detects no progress on Core.lean:89]

Claude: No progress on Core.lean:89 after 3 attempts. Running stuck review...

## Stuck Review — Core.lean:89

**Top 3 blockers:**
1. Missing lemma for tendsto_atTop → search Mathlib.Topology.Order
2. Need MeasurableSpace instance → add `haveI` before apply
3. Goal has implicit coercion issue → try `convert` instead of `exact`

**Recommended:** Search tendsto variants first.

Review complete. Proposed plan:
1. Search Mathlib.Topology.Order for tendsto_atTop variants
2. Add `haveI : MeasurableSpace β := inferInstance` before apply
3. If exact fails, try `convert` with explicit type annotation

Proceed with this plan? [yes / no / skip]

User: yes

Claude: Continuing with plan...
```

### End-of-Session Golf Example

```
## Session Complete

Filled: 5/8 sorries
Commits: 5 new

Create checkpoint? (per-file + project build, axiom check, commit)
- [yes] — run /lean4:checkpoint
- [no] — keep commits as-is

User: yes

Claude: Running checkpoint... ✓

Run /lean4:golf on touched files?
Files modified: Core.lean, Helpers.lean
- [yes] — golf each file
- [no] — skip

User: yes

Claude: Golfing Core.lean...
[golf output]
```

### Counterexample Discovery Example

> **Legacy / prove-engine flow.** This illustrates the shared prove-engine
> falsification-artifact path, which may also emit a `T_salvaged` sibling. The
> dedicated `/lean4:disprove` command does **not** do this in v1: salvage is
> locked off (`--negation-policy=counterexample-only`), so disprove emits only
> `T_counterexample`, never `T_salvaged`. Salvage modes are future work — see the
> [disprove section](#disprove) for the current contract.

See [cycle-engine.md](cycle-engine.md#falsification-artifacts) for artifact templates.

```
Claude: Working on Core.lean:42 - `naive_bound`...

Goal: ⊢ ∀ n : Fin 5, n.val < 3

Preflight falsification (Fin 5 is decidable)...
Trying decide... Found counterexample: n = 3

## Counterexample Found

Statement `naive_bound` is false.
Witness: `⟨3, by decide⟩` with `¬ (3 < 3)`

Creating counterexample lemma...
```lean
/-- Counterexample to naive_bound -/
theorem naive_bound_counterexample : ∃ n : Fin 5, ¬ (n.val < 3) := by
  exact ⟨3, by decide⟩
```

Create salvage lemma? [yes/no]

User: yes

Claude: What correction makes it true?
- Option A: Restrict domain to `Fin 3` (all values < 3)
- Option B: Weaken bound to `n.val < 5` (trivially true for `Fin 5`)

User: A

Creating salvage:
```lean
/-- Salvaged version of naive_bound: restrict to Fin 3 -/
theorem naive_bound_salvaged : ∀ n : Fin 3, n.val < 3 := by
  intro n; exact n.isLt
```

Committing: "disprove: naive_bound - counterexample at n=3"
```

---

## File Verification

### Three-Tier Verification Ladder

Use the lightest tool that answers the question:

| Tier | Tool | When | Speed |
|------|------|------|-------|
| Per-edit | `lean_diagnostic_messages(file)` | After every edit | Sub-second |
| File compile | `lake env lean <path/to/File.lean>` | File-level gate, import checks | Seconds |
| Project gate | `lake build` | Checkpoint, final gate, `/lean4:checkpoint` | Minutes |

Run `lake env lean` from the Lean project root; pass repo-relative file paths.

### Anti-Pattern: `lake build` with File Arguments

```
# ✗ Wrong — lake build does not accept file path arguments
lake build InfinitaryLogic/Scott/Sentence.lean
→ error: unknown target 'InfinitaryLogic/Scott/Sentence.lean'

# ✓ Correct — use lake env lean for single-file compilation
lake env lean InfinitaryLogic/Scott/Sentence.lean
→ (compiles single file with lake environment)
```

### Typical Verification Flow

```
1. Edit proof
2. lean_diagnostic_messages(file)    # immediate feedback
3. Fix any issues
4. lake env lean path/to/File.lean   # file-level gate (from project root)
5. Continue editing...
6. lake build                        # project gate at checkpoint only
```


---

## refactor

### Basic Usage

```
User: /lean4:refactor ForwardEuler/Main.lean
```

```markdown
## Refactor Plan — ForwardEuler/Main.lean

### Strategy Improvements
1. `continuousOn_eulerPath` (line 104): case-splitting on endpoints
   → Use `ContinuousOn.congr` + `Set.EqOn` (saves ~20 lines)

2. `hasDerivWithinAt_eulerPath` (line 149): manual derivative via unfolding
   → Use `HasDerivAt` chain + `congr_of_eventuallyEq` (saves ~5 lines)

### Helper Extraction
1. Floor computation from Ico membership — appears 4x (lines 89, 119, 155, 198)
   → Extract `floor_eq_of_mem_Ico`

### Estimated Impact
- Lines before: 310
- Lines after: ~245
- Helpers extracted: 1
- Mathlib lemmas newly applied: 3

Apply batch 1 (3 changes)? [yes / skip / stop]
```

### Dry Run

```
User: /lean4:refactor --scope=changed --dry-run
```

Reports opportunities without editing files.

---

## golf

### Basic Usage

```
/lean4:golf                     # Golf entire project
/lean4:golf File.lean           # Golf specific file
/lean4:golf File.lean:42        # Golf proof at specific line
/lean4:golf --dry-run           # Show opportunities without applying
```

### Full Session Example

```
User: /lean4:golf Core.lean

Claude: Verifying build...
✓ Core.lean compiles

Finding golfing opportunities...

Found 7 patterns:
- 3 directness wins (ext+rfl, apply+exact, constructor+exact)
- 1 performance cleanup (simp narrowing)
- 1 safe inline (let used once)
- 1 skip (let used 5 times)
- 1 skip (rwa replacement — marginal)

Applying optimizations...

[1/6] Line 45: ext x; rfl → rfl (directness)
  Diagnostics... ✓

[2/6] Line 66: apply f; exact h → exact f h (directness)
  Diagnostics... ✓

[3/6] Line 112: constructor; exact; exact → exact ⟨_, _⟩ (directness)
  Diagnostics... ✓

[4/6] Line 34: simp [...] → simp only [...] (performance)
  Diagnostics... ✓

[5/6] Line 67: Inline let bound := ...
  Checking usage... 1 reference, safe
  Diagnostics... ✓

[6/6] Line 23: rw [h]; exact → rwa [h]
  Skipped: only 1-line win, moves up tactic complexity ladder (rw+exact → rwa)

## Golf Results

Meaningful simplifications: 3 (directness improvements)
Performance cleanups: 1 (simp narrowing)
Syntax cleanups: 1 (let inline)
Skipped: 2 (1 safety — let used 5×, 1 marginal — rwa replacement)
Build status: ✓ passing
Total savings: 6 lines (~9%)
```

### Dry Run Example

```
User: /lean4:golf --dry-run

Claude: Scanning for opportunities...

## Golf Opportunities (Dry Run)

**File:** Core.lean

| Line | Pattern | Benefit | Confidence | Savings |
|------|---------|---------|------------|---------|
| 78 | ext + rfl → rfl | Directness | High | 1 line |
| 45 | Inline let (1 use) | Clarity | High | 2 lines |
| 34 | simp → simp only | Performance | High | 0 lines |
| 56 | Inline let (4 uses) | — | Skip | - |
| 23 | rw + exact → rwa | Marginal | Skip | 1 line |

**Estimated savings:** 3 lines from 3 safe optimizations (+ 1 perf-only)
**Run without --dry-run to apply**
```

### Saturation Example

```
## Golf Results

**File:** Core.lean
**Optimizations applied:** 12
**Build status:** ✓ passing

Saturation reached after 12 optimizations.
Remaining 3 opportunities are false positives or low-value.

Success rate dropped to 15% (below 20% threshold).
Recommend stopping further golfing on this file.
```

### Taste-Driven Golfing Example

```
User: /lean4:golf Analysis.lean

Claude: Verifying build...
✓ Analysis.lean compiles

Finding golfing opportunities...

Found 8 patterns (4 actionable, 4 skipped)

[1/4] Line 23: apply f; exact h → exact f h (directness)
  Diagnostics... ✓

[2/4] Line 45: simp [h1, h2, h3] → simp only [h1, h2] (performance — linter flagged h3 unused)
  Diagnostics... ✓

[3/4] Line 67: rw [h]; exact trivial → rwa [h]
  Skipped: 1-line win but moves up tactic complexity ladder (rw+exact is explicit,
  rwa is heavier automation). Not worth surfacing.

[4/4] Line 89: 3-line proof → 1 line with <;>
  cases h with | inl => simp [ha] | inr => simp [hb]
  Candidate: cases h <;> simp [ha, hb]
  Skipped: branches use different simp arguments — <;> only for literally identical goals

[5/4] Line 102: simpa using h_bound → exact h_bound
  Diagnostics... ✓ (simpa does no actual simplification here — exact is more direct)

[6/4] Line 115: 2-line proof kept as-is
  have h_key := critical_step a b
  exact h_key.trans (by ring)
  Candidate 1-line: exact (critical_step a b).trans (by ring)
  Skipped: named intermediate `h_key` has semantic value, 1-line form is more opaque

## Golf Results

Meaningful simplifications: 2 (directness improvements)
Performance cleanups: 1 (simp narrowing)
Skipped: 3 (1 tactic complexity, 1 non-identical <;>, 1 semantic name preserved)
Build status: ✓ passing
Total savings: 3 lines (~5%)
```

### Search Mode Example

```
User: /lean4:golf Core.lean --search=quick

Claude: Verifying build...
✓ Core.lean compiles

Finding golfing opportunities...
Found 4 syntactic patterns + 2 lemma replacement candidates

[1/6] Line 23: apply f; exact h → exact f h (directness)
  Diagnostics... ✓

[2/6] Line 30: custom_continuous_comp → Continuous.comp (mathlib)
  LSP search: lean_local_search("continuous comp")
  Testing replacement... ✓ (1/2 candidates passed)
  Import: Mathlib.Topology.Basic
  Diagnostics... ✓

[3/6] Line 45: Inline let (1 use)
  Diagnostics... ✓

[4/6] Line 67: custom_bound_lemma → replacement candidate
  LSP search: lean_leanfinder("bound monotone")
  Testing replacement... ✗ type mismatch (0/2 passed)
  Skipped (hand off to axiom-eliminator for deeper work)

## Golf Results

Optimizations applied: 3/6
Replacements: 1 lemma (mathlib)
Skipped: 1 (safety), 1 (needs axiom-eliminator)
Total savings: 5 lines (~8%)
Build status: ✓ passing
```

### Delegation Preflight Failure Example

```
User: /lean4:golf --max-delegates=3

Claude: Verifying build...
✓ Project compiles

Running preflight: delegating Core.lean:23 to golfer subagent...

⚠ Preflight subagent hit Edit permission prompt.
Stopping delegation immediately — switching to direct mode.

Continuing in main agent (no subagents will be launched)...

[1/6] Line 23: apply f; exact h → exact f h (directness)
  Diagnostics... ✓

[2/6] Line 45: ext x; rfl → rfl (directness)
  Diagnostics... ✓

[continues directly without delegation...]
```

### Bulk Rewrite Auto-Revert Example

```
User: /lean4:golf Core.lean

Claude: Verifying build...
✓ Core.lean compiles

Finding golfing opportunities...
Found 8 `:= by exact` candidates in declaration RHS positions (≥4 → bulk mode)

Preview (3 of 8):
  Line 23: `:= by exact h` → `:= h`
  Line 67: `:= by exact rfl` → `:= rfl`
  Line 101: `:= by exact Nat.zero_le 1` → `:= Nat.zero_le 1`

Apply as batch? [yes / individual / skip]

User: yes

Capturing baseline diagnostics...
Baseline: 0 diagnostics, 0 sorries

Applying batch (8 replacements, Core.lean)...
Running lean_diagnostic_messages(Core.lean)...

⚠ Regression detected:
  - 2 new diagnostics (type mismatch at lines 45, 89)
  - Sorry count: 0 → 0 (unchanged)

Restoring from pre-batch snapshot...
✓ Core.lean restored to pre-batch state

Falling back to individual edits...
[1/8] Line 23: `:= by exact h` → `:= h`
  Diagnostics... ✓
[2/8] Line 45: `:= by exact rfl` — skipped (calc block context)
[3/8] Line 89: `:= by exact (by ring)` — skipped (nested tactic-mode boundary)

Applied 5/8, skipped 2 (context rules), reverted 1 (regression)
```

### Context-Ambiguous Skip Example

```
User: /lean4:golf Lemmas.lean

Claude: Finding golfing opportunities...

Found 5 `:= by exact` candidates

[1/5] Line 12: `:= by exact h`
  Context: declaration RHS ✓, no nested tactic boundary ✓
  Diagnostics... ✓

[2/5] Line 34: `:= by exact (by simp)`
  Skipped: nested tactic-mode boundary in TERM

[3/5] Line 56: inside `calc` block
  Skipped: disallowed context (calc)

[4/5] Line 78: uncertain elaboration context
  Skipped: context classification uncertain — never force

Applied 3/5, skipped 2 (context rules)
```

### Exact-Collapse Example

````
User: /lean4:golf Core.lean --search=quick

Claude: Verifying build...
✓ Core.lean compiles

Finding golfing opportunities...
Running: find_golfable.py Core.lean --patterns apply-exact-chain --filter
Found 6 apply-exact-chain anchors

[1/6] Line 34: Mechanical collapse
  apply mul_lt_mul_of_pos_right; · exact h_bound; · exact h_pos
  → exact mul_lt_mul_of_pos_right h_bound h_pos
  lean_multi_attempt... ✓
  Diagnostics baseline check... ✓ (no new diagnostics, sorry count unchanged)

[2/6] Line 52: Mechanical collapse
  apply HasDerivAt.div; · exact hf; · exact hg
  → exact hf.div hg
  lean_multi_attempt... ✓
  Diagnostics baseline check... ✓

[3/6] Line 71: Readability skip
  apply f; · apply g; · apply h; · exact a; · exact b
  Collapsed form: exact f (g (h a b)) — >2 nesting depth, marginal net win
  Skipped (readability)

[4/6] Line 89: Mechanical collapse
  apply Continuous.comp; · exact continuous_neg; · exact hf
  → exact continuous_neg.comp hf
  lean_multi_attempt... ✓
  Diagnostics baseline check... ✓

[5/6] Line 103: Skipped (inside cases block)

[6/6] Line 115: Exploratory probe (--search=quick)
  apply bound_mono; · exact h_le; · exact h_pos
  Candidate 1: exact bound_mono h_le h_pos — lean_multi_attempt ✗
  Candidate 2: exact h_le.bound_mono h_pos — lean_multi_attempt ✓
  Diagnostics baseline check... ✓

## Golf Results

Exact-collapse: Mechanical 3 applied, Exploratory 1 found.
Skipped: 1 (readability), 1 (unsafe context)
Total savings: 8 lines (~15%)
Build status: ✓ passing
````

---

## learn

### Repo Mode — Exploring Project Structure

```
User: /lean4:learn --mode=repo --scope=project

Claude: Scanning project structure...

Found 12 .lean files across 3 directories.

## Project Map

├── InfinitaryLogic/
│   ├── Basic.lean          — Core definitions (Language, Term, Formula)
│   ├── Semantics.lean      — Model theory (Structure, Interpretation)
│   └── Scott/
│       ├── Sentence.lean   — Scott sentences (4 sorries)
│       └── Isomorphism.lean — Back-and-forth (2 sorries)
├── Helpers/
│   ├── Ordinal.lean        — Ordinal utilities (complete)
│   └── Cardinal.lean       — Cardinal bounds (1 sorry)
└── lakefile.lean

Key dependency flow:
  Basic → Semantics → Scott/Sentence → Scott/Isomorphism
  Helpers/Ordinal → Scott/Sentence

What would you like to explore?
- [deeper] Drill into a specific file
- [deps] Show full dependency graph
- [sorries] Focus on the 7 remaining sorries
```

### Mathlib Mode — Navigating a Topic

````
User: /lean4:learn --mode=mathlib topology compact

Claude: Searching mathlib for compactness in topology...

lean_local_search("compact topology") → 12 results
lean_leanfinder("IsCompact") → 8 results

## Compactness in Mathlib

**Core definition:** `IsCompact` in `Mathlib.Topology.Defs.Basic`
```lean
def IsCompact (s : Set α) : Prop :=
  ∀ ⦃f : Filter α⦄, NeBot f → f ≤ 𝓟 s →
    ∃ a ∈ s, ClusterPt a f
```

**Key lemmas:**
| Lemma | Location |
|-------|----------|
| `IsCompact.isClosed` | Mathlib.Topology.Separation.Basic |
| `IsCompact.isBounded` | Mathlib.Topology.MetricSpace.Bounded |
| `isCompact_iff_finite_subcover` | Mathlib.Topology.Defs.Basic |

**Hierarchy:** TopologicalSpace → CompactSpace → IsCompact (for subsets)

What next?
- [show proof] See proof of a specific lemma
- [related] Explore related concepts (sequentially compact, totally bounded)
- [alternative] See filter-free characterization
````

### Game Style — Natural Numbers Track

````
User: /lean4:learn --style=game --track=nng-like

Claude: [Intent: usage (inferred) | Presentation: formal]

Starting Natural Numbers Game — Track: nng-like (8 levels)

## Level 1: Zero + n = n

Prove that `0 + n = n` for all natural numbers `n`.

```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  sorry
```

Hint available if you need it. Type your proof:

User: induction n with
| zero => rfl
| succ n ih => simp [Nat.add_succ, ih]

Claude: Verifying via lean_goal + lean_multi_attempt...
lean_diagnostic_messages → clean
✓ Level 1 complete! [verified]

## Level 2: Succ (a + b) = a + Succ b

```lean
theorem succ_add (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  sorry
```

[continue / skip / quit]
````

### Paper as Source — Math Intent

````
User: /lean4:learn --source ./papers/stone-weierstrass.pdf

Claude: Reading PDF... extracting key results.

[Intent: math (inferred from PDF) | Presentation: informal]

## Stone–Weierstrass: Main Results [unverified]

1. **Theorem 1 (Real):** If A is a subalgebra of C(X, ℝ) that separates points and contains constants, then A is dense in C(X, ℝ).
2. **Theorem 2 (Complex):** The analogous result for self-adjoint subalgebras of C(X, ℂ).
3. **Corollary:** Every continuous function on [a,b] is a uniform limit of polynomials (Weierstrass).

Which result would you like to explore?

User: 1

Claude: **Theorem 1** says that polynomial-like function algebras are "enough" to approximate any continuous function, provided two conditions...

[explains conceptually at user's level]

Want to see this formalized in Lean to make it concrete?

[deeper / show source / formalize → /lean4:formalize]
````

---

## doctor

### Basic Usage

```
/lean4:doctor              # Full diagnostic
/lean4:doctor env          # Environment only
/lean4:doctor migrate      # Migration assistance
/lean4:doctor cleanup      # Remove obsolete files
```

### Full Diagnostic Example

```
User: /lean4:doctor

Claude: Running diagnostics...

## Lean4 Doctor Report

### Environment
✓ lean 4.15.0
✓ lake 4.15.0
✓ python3 3.11.2
✓ git 2.43.0
✓ rg 14.1.0

### MCP Tools
✓ Lean LSP MCP tools available in this session (lean_goal)

### Plugin
✓ LEAN4_PLUGIN_ROOT=/home/user/.claude/plugins/lean4
✓ LEAN4_SCRIPTS=/home/user/.claude/plugins/lean4/lib/scripts
✓ Hooks executable
✓ Scripts executable (12 files)

### Project
✓ lakefile.lean found
✓ lean-toolchain: leanprover/lean4:v4.27.0
✓ Build passes
→ 3 sorries in Core.lean

### Migration
✓ Clean installation (no v3 artifacts)

### Status: Ready

Your environment is configured correctly.
Run /lean4:prove to fill the 3 remaining sorries.
```

### Migration Example

```
User: /lean4:doctor migrate

Claude: Checking for v3 artifacts...

Found v3 installation:
- .claude/tools/lean4/ (12 files)
- .claude/docs/lean4/ (8 files)

## Migration Steps

1. Uninstall old plugins:
   /plugin uninstall lean4-theorem-proving
   /plugin uninstall lean4-memories
   /plugin uninstall lean4-subagents

2. Install unified plugin:
   /plugin marketplace add cameronfreer/lean4-skills
   /plugin install lean4

3. Optional cleanup:
   rm -rf .claude/tools/lean4 .claude/docs/lean4

Proceed with migration? (yes/no)
```

### Cleanup Example

```
User: /lean4:doctor cleanup

Claude: Scanning for obsolete files...

Found:
- .claude/tools/lean4/ (12 files, 45KB)
- .claude/docs/lean4/ (8 files, 32KB)

These are v3 artifacts that are no longer needed.
Remove them? (yes/no)

User: yes

Claude: Removing .claude/tools/lean4/... ✓
Removing .claude/docs/lean4/... ✓

Cleanup complete. 77KB freed.
```
