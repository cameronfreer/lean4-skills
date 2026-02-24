# Command Examples

Extended examples and session transcripts for Lean4 plugin commands.

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

Found 6 patterns:
- 4 instant wins (rw+exact, ext+rfl)
- 1 safe inline (let used once)
- 1 skip (let used 5 times)

Applying optimizations...

[1/5] Line 23: rw [h]; exact → rwa [h]
  Building... ✓

[2/5] Line 45: ext x; rfl → rfl
  Building... ✓

[3/5] Line 67: Inline let bound := ...
  Checking usage... 1 reference, safe
  Building... ✓

[4/5] Line 89: simp [*]; rfl → simp [*]
  Building... ✓

[5/5] Line 112: constructor; exact; exact → exact ⟨_, _⟩
  Building... ✓

## Golf Results

Optimizations applied: 5/6
Skipped: 1 (let used 5 times)
Total savings: 7 lines (~10%)
Build status: ✓ passing
```

### Dry Run Example

```
User: /lean4:golf --dry-run

Claude: Scanning for opportunities...

## Golf Opportunities (Dry Run)

**File:** Core.lean

| Line | Pattern | Confidence | Savings |
|------|---------|------------|---------|
| 23 | rw + exact → rwa | High | 1 line |
| 45 | Inline let (1 use) | High | 2 lines |
| 56 | Inline let (4 uses) | Skip | - |
| 78 | ext + rfl → rfl | High | 1 line |

**Estimated savings:** 4 lines from 3 safe optimizations
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

### Search Mode Example

```
User: /lean4:golf Core.lean --search=quick

Claude: Verifying build...
✓ Core.lean compiles

Finding golfing opportunities...
Found 4 syntactic patterns + 2 lemma replacement candidates

[1/6] Line 23: rw [h]; exact → rwa [h]
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

[1/6] Line 23: rw [h]; exact → rwa [h]
  Diagnostics... ✓

[2/6] Line 45: ext x; rfl → rfl
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
- Line 23: `rw [h]; exact trivial` → `rwa [h]`
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

Create verified checkpoint? (build + axiom check + commit)
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

## Learn

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

### Formalize Mode — Autoformalization

````
User: /lean4:learn --mode=formalize "Every continuous function on a compact set is bounded"

Claude: Parsing claim and drafting formalization...

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

Attempting proof via lean_goal + lean_multi_attempt...
lean_local_search("IsCompact ContinuousOn IsBounded image") → found it
Trying: `exact hK.image_of_continuousOn hf |>.isBounded`
Diagnostics... ✓

Proof complete (--rigor=checked: no sorry, clean diagnostics, standard axioms).

What next?
- [show source] See the mathlib proof
- [alternative] Different formalization (e.g., using Bornology)
- [generalize] Weaken hypotheses
- [save to scratch] Write to scratch file
````

### Game Style — Natural Numbers Track

````
User: /lean4:learn --style=game --track=nng-like

Claude: [Intent: usage (inferred) | Presentation: formal | Mode: formalize]

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

[Intent: math (inferred from PDF) | Presentation: informal | Mode: formalize]

## Stone–Weierstrass: Main Results [unverified]

1. **Theorem 1 (Real):** If A is a subalgebra of C(X, ℝ) that separates points and contains constants, then A is dense in C(X, ℝ).
2. **Theorem 2 (Complex):** The analogous result for self-adjoint subalgebras of C(X, ℂ).
3. **Corollary:** Every continuous function on [a,b] is a uniform limit of polynomials (Weierstrass).

Which result would you like to explore?

User: 1

Claude: **Theorem 1** says that polynomial-like function algebras are "enough" to approximate any continuous function, provided two conditions...

[explains conceptually at user's level]

Want to see this formalized in Lean to make it concrete?

[deeper / show source / formalize]
````

### Formalize Mode — Axiomatic Draft

````
User: /lean4:learn --mode=formalize --rigor=axiomatic "The p-adic numbers are complete"

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

bash "$LEAN4_SCRIPTS/check_axioms_inline.sh" <target>.lean --report-only → ✓ standard axioms only

Note: Mathlib likely has this as an instance. Searching...
lean_leanfinder("CompleteSpace Padic") → `Padic.instCompleteSpace`

This is already a registered instance in mathlib. No axioms or assumptions needed.

What next?
- [show source] See how mathlib proves completeness
- [deeper] Explore the p-adic metric construction
````
