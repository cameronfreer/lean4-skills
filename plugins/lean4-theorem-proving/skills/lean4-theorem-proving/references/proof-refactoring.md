# Refactoring Long Proofs

Guide for breaking monolithic proofs into maintainable helper lemmas.

## When to Refactor

**Sweet spot:** Proofs between 60-200 lines benefit most from refactoring. Under 60 lines, overhead exceeds benefit. Over 200 lines, multiple refactorings needed.

**Refactor when:**
- Proof exceeds 100 lines (or 60+ with repetitive structure)
- Multiple conceptually distinct steps
- Intermediate results would be useful elsewhere
- Hard to understand/maintain
- Repeated patterns (especially lhs/rhs with near-identical proofs)
- Large preliminary calculations (50+ line `have` statements)
- Property bundling opportunities (multiple properties proven separately, used together)

**Don't refactor when:**
- Proof is short and linear (< 50 lines, no repetition)
- No natural intermediate milestones
- Extraction would require too many parameters
- Proof is already well-structured with `have` statements and helpers

---

## LSP-Based Refactoring Workflow

**Strategy:** Use `lean_goal` (from Lean LSP MCP) to inspect proof state at different locations, then subdivide at natural breakpoints where intermediate goals are clean and reusable.

### Step 1: Survey the Proof

Walk through the proof checking goals at 4-5 key points:

```python
# Check goals at 4-5 key locations in the long proof
lean_goal(file, line=15)   # After initial setup
lean_goal(file, line=45)   # After first major step
lean_goal(file, line=78)   # After second major step
lean_goal(file, line=120)  # After third major step
lean_goal(file, line=155)  # Near end
```

**What to look for:**
- Clean, self-contained intermediate goals
- Natural mathematical milestones
- Points where context significantly changes
- Repetitive structure (same proof pattern for lhs/rhs)

### Step 2: Identify Extraction Points

Look for locations where:
- **Goal is clean:** Self-contained statement with clear meaning
- **Dependencies are local:** Depends only on earlier hypotheses (no forward references)
- **Useful elsewhere:** Goal would be reusable in other contexts
- **Natural meaning:** Intermediate state has clear mathematical interpretation

**Good breakpoints:**
- After establishing key inequalities or bounds
- After case splits (before/after `by_cases`)
- After measurability/integrability proofs
- Where intermediate result has a clear name
- After computing/simplifying expressions
- Before/after applying major lemmas

**Bad breakpoints:**
- Mid-calculation (no clear intermediate goal)
- Where helper would need 10+ parameters
- Where context is too tangled to separate cleanly
- In the middle of a `calc` chain
- Where goal depends on later bindings

### Step 3: Extract Helper Lemma

```lean
-- BEFORE: Monolithic proof
theorem big_result : Conclusion := by
  intro x hx
  have h1 : IntermediateGoal1 := by
    [30 lines of tactics...]
  have h2 : IntermediateGoal2 := by
    [40 lines of tactics...]
  [30 more lines...]

-- AFTER: Extracted helpers
lemma helper1 (x : α) (hx : Property x) : IntermediateGoal1 := by
  [30 lines - extracted from h1]

lemma helper2 (x : α) (h1 : IntermediateGoal1) : IntermediateGoal2 := by
  [40 lines - extracted from h2]

theorem big_result : Conclusion := by
  intro x hx
  have h1 := helper1 x hx
  have h2 := helper2 x h1
  [30 lines - much clearer now]
```

### Step 4: Verify with LSP

After each extraction:
```python
lean_diagnostic_messages(file)  # Check for errors
lean_goal(file, line)           # Confirm goals match
```

**Verify extraction is correct:**
```python
# Original line number where `have h1 : ...` was
lean_goal(file, line=old_h1_line)
# → Should match helper1's conclusion

# New line number after extraction
lean_goal(file, line=new_h1_line)
# → Should show `h1 : IntermediateGoal1` available
```

---

## Non-LSP Refactoring (Manual)

If you don't have LSP access, use this manual workflow:

### Step 1: Read and Understand

Read through the proof identifying conceptual sections:
- What is the proof trying to establish?
- What are the major steps?
- Are there repeated patterns?

### Step 2: Mark Candidates

Add comments marking potential extraction points:
```lean
theorem big_result : ... := by
  intro x hx
  -- Candidate 1: Establish boundedness
  have h1 : ... := by
    ...
  -- Candidate 2: Prove measurability
  have h2 : ... := by
    ...
```

### Step 3: Extract One at a Time

Extract one helper at a time, compile after each:
1. Copy `have` proof to new lemma
2. Identify required parameters
3. Replace original with `have h := helper args`
4. `lake build` to verify
5. Commit if successful

### Step 4: Iterate

Repeat until proof is manageable.

---

## Naming Extracted Helpers

**Good names describe what the lemma establishes:**
- `bounded_by_integral` - establishes bound
- `measurable_composition` - proves measurability
- `convergence_ae` - proves a.e. convergence

**Avoid vague names:**
- `helper1`, `aux_lemma` - meaningless
- `part_one`, `step_2` - based on structure, not content
- `temp`, `tmp` - should be permanent

**Mathlib-style conventions:**
- Use snake_case
- Include key concepts: `integral`, `measure`, `continuous`, etc.
- Add context if needed: `of_`, `_of`, `_iff`

---

## Real Refactoring Example

**Context:** 63-line monolithic proof about exchangeable measures with strict monotone functions.

**Step 1: Identify natural boundaries**

Using `lean_goal` at different points revealed:
- Line 15: After establishing `hk_bound : ∀ i, k i < n` (clean arithmetic result)
- Line 35: After constructing permutation (conceptually distinct)
- Line 50: After projection proof (measure theory manipulation)

**Step 2: Extract arithmetic helper**

Found this embedded calculation:
```lean
have hk_bound : ∀ i : Fin (m' + 1), k i < n := by
  intro i
  simp only [n]
  have : k i ≤ k ⟨m', Nat.lt_succ_self m'⟩ := by
    apply StrictMono.monotone hk_mono
    exact Fin.le_last i
  omega
```

Extracted to:
```lean
/-- Strictly monotone functions satisfy k(i) ≤ k(last) for all i -/
private lemma strictMono_all_lt_succ_last {m : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (i : Fin m) (last : Fin m)
    (h_last : ∀ j, j ≤ last) :
    k i ≤ k last := by
  apply StrictMono.monotone hk
  exact h_last i
```

**Result:** Main proof now just calls helper, much clearer.

**Step 3: Verify with LSP**

```python
lean_diagnostic_messages(file)  # No errors ✓
lean_goal(file, line=15)        # Shows helper available ✓
```

**Final structure:**
- Original: 63 lines monolithic
- Refactored: 45 lines main + 33 lines helpers = 78 lines total
- **Success:** Much clearer structure, each piece testable independently

**Key insight:** Success measured by clarity, not brevity.

---

## Critical Patterns from Real Refactoring

### 1. Use `private` for Proof-Specific Helpers

**Pattern:** Mark helper lemmas as `private` when they're only used in one theorem and have very specific signatures.

```lean
/-- Helper lemma: strictly monotone functions satisfy k(i) ≤ k(last) -/
private lemma strictMono_all_lt_succ_last {m : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (i : Fin m) (last : Fin m)
    (h_last : ∀ j, j ≤ last) :
    k i ≤ k last := by
  apply StrictMono.monotone hk
  exact h_last i
```

**Why:** This signals "internal scaffolding" - too specific to be generally useful, but clarifies the main proof.

### 2. ⚠️ CRITICAL: Let Bindings Create Definitional Inequality

**Problem:** When extracting a helper that uses `let` bindings, those bindings create new definitional contexts that don't unify with the main proof's `let` bindings, even if syntactically identical.

**What happened:**
```lean
-- In main theorem:
let ι : Fin (m' + 1) → Fin n := fun i => ⟨i.val, ...⟩
let proj : (Fin n → α) → (Fin (m' + 1) → α) := fun f i => f (ι i)

-- In helper lemma (also uses let):
private lemma helper ... :=
  let ι : Fin m → Fin n := fun i => ⟨i.val, ...⟩
  let proj : (Fin n → α) → (Fin m → α) := fun f i => f (ι i)
  Measure.map (proj ∘ ...) μ = Measure.map (proj ∘ ...) μ := by ...

-- Error when using helper:
-- "Did not find an occurrence of the pattern (proj ∘ fun ω j => ...)"
-- Main theorem's `proj` ≠ helper's `proj` definitionally!
```

**Solutions:**
- **Option A:** Inline the proof directly (what we did for measure theory manipulations)
- **Option B:** Pass `ι` and `proj` as explicit parameters instead of `let` bindings
- **Option C:** Use `show` to change the goal explicitly

**Takeaway:** Avoid `let` bindings in helper signatures when the caller also uses `let`. Use explicit parameters instead.

### 3. Omega Has Limits - Provide Intermediate Steps

**Problem:** `omega` can fail on arithmetic goals that humans find obvious.

**Original failing attempt:**
```lean
private lemma strictMono_length_le_max_succ {m : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (last : Fin m) :
    m ≤ k last + 1 := by
  have h_last_val : last.val < m := last.isLt
  have h_mono : last.val ≤ k last := strictMono_Fin_ge_id hk last
  omega  -- ERROR: "omega could not prove the goal"
```

**Successful fix:**
```lean
private lemma strictMono_length_le_max_succ {m : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (last : Fin m)
    (h_last_is_max : last.val + 1 = m) :  -- Explicit equality
    m ≤ k last + 1 := by
  have h_mono : last.val ≤ k last := strictMono_Fin_ge_id hk last
  calc m = last.val + 1 := h_last_is_max.symm
       _ ≤ k last + 1 := Nat.add_le_add_right h_mono 1
```

**Why it helps:** Making `last.val + 1 = m` an explicit assumption (proven as `rfl` at call site) gives `omega` less to figure out. Use `calc` for clarity.

### 4. Measure Theory Extraction Requires Exact Alignment

**Lesson:** When extracting lemmas involving `Measure.map` and compositions, ensure types and compositions align exactly. Measure theory lemmas are sensitive to definitional equality.

**What didn't work:**
```lean
-- Helper returned: Measure.map (proj ∘ f) μ = Measure.map (proj ∘ g) μ
-- Main theorem had different `proj` definition (via let)
-- Rewrite failed even though they looked the same
```

**What worked:**
```lean
-- Inline the projection proof directly in main theorem:
have hproj_eq : Measure.map (proj ∘ fun ω j => X (σ j).val ω) μ =
                Measure.map (proj ∘ fun ω j => X j.val ω) μ := by
  rw [← Measure.map_map hproj_meas (measurable_pi_lambda _ ...),
      ← Measure.map_map hproj_meas (measurable_pi_lambda _ ...)]
  exact congrArg (Measure.map proj) hexch
```

**Takeaway:** For measure theory manipulations with `let` bindings, prefer inlining over extraction.

### 5. Document What and Why

**Pattern:** Every helper lemma should explain:
1. What it proves (in mathematical terms)
2. Why it's true (key insight)
3. How it's used (if not obvious)

**Good example:**
```lean
/--
Helper lemma: The length of the domain is bounded by the maximum value plus one.

For a strictly monotone function `k : Fin m → ℕ`, we have `m ≤ k(m-1) + 1`.
This uses the fact that strictly monotone functions satisfy `i ≤ k(i)` for all `i`.
-/
private lemma strictMono_length_le_max_succ ...
```

### 6. Test After Every Extraction

**Workflow with LSP:**
1. Extract helper lemma
2. `lean_diagnostic_messages(file)` on helper
3. Update main theorem to use helper
4. `lean_diagnostic_messages(file)` on main theorem
5. Fix any type mismatches
6. Repeat

**Don't:** Make multiple changes then check - errors compound!

---

## Additional Lessons from Second Refactoring

### 7. Private Lemmas Use Regular Comments, Not Doc Comments

**Problem:**
```lean
/-- For an exchangeable sequence, the finite marginals... -/
private lemma exchangeable_finite_marginals_eq_reindexed ...
```

**Error:** `unexpected token '/--'; expected 'lemma'`

**Solution:**
```lean
-- For an exchangeable sequence, the finite marginals...
private lemma exchangeable_finite_marginals_eq_reindexed ...
```

**Why:** Doc comment syntax (`/-- -/`) is reserved for public API documentation. Private declarations don't appear in generated docs, so use regular `--` comments.

### 8. Unused Required Parameters Need Underscore Prefix

**Problem:**
```lean
∀ n (S : Set (Fin n → α)) (hS : MeasurableSet S), ...
-- Parameter hS required in signature but unused in proof
-- Linter warning: unused variable `hS`
```

**Solution:**
```lean
∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S), ...
```

**Why:** The parameter is needed in the type signature (to quantify over measurable sets), but the proof uses measure equality without explicitly referencing measurability. The underscore signals "intentionally unused."

### 9. Explicit Parameters with Equality Proofs Avoid Let Binding Issues

**First refactoring:** Helper with `let` bindings didn't unify with main theorem's `let` bindings (definitional inequality).

**This refactoring:** No issues! **Why?**

```lean
-- Helper: Pass as explicit parameter with equality proof
private lemma exchangeable_finite_marginals_eq_reindexed
    (μX : Measure (ℕ → α)) (hμX : μX = pathLaw μ X) ...

-- Main theorem: Pass with rfl
let μX := pathLaw μ X
have hMarg := exchangeable_finite_marginals_eq_reindexed hX hEx μX rfl π
```

**Key insight:** The helper takes `μX` as a parameter with explicit equality proof `hμX : μX = pathLaw μ X`. The main theorem passes `rfl` for this proof, which unifies perfectly because `μX` is definitionally equal to `pathLaw μ X` at the call site.

**General pattern:** When extracting helpers from proofs with `let` bindings, prefer explicit parameters with equality proofs over recreating the bindings internally.

### 10. Structural Comments Create Proof Table of Contents

**Pattern:** Add high-level comments to guide readers through proof strategy:

```lean
-- Define path law and establish probability measure properties
let μX := pathLaw (α:=α) μ X
...

-- Apply helper: finite marginals are equal
have hMarg := exchangeable_finite_marginals_eq_reindexed ...

-- Apply measure uniqueness from finite marginals
have hEq := measure_eq_of_fin_marginals_eq_prob ...

-- Relate back to original form using path law commutation
have hmap₁ := pathLaw_map_reindex_comm ...
```

**Why it matters:** These comments create a "table of contents" for the proof. Readers can quickly understand the structure without parsing every tactic.

### 11. LSP Diagnostics Work Even When Full Build Fails

**Observation:** `lake build` failed due to Batteries dependency issues (toolchain compatibility), but:
```python
lean_diagnostic_messages(file_path)
# ✅ Still worked! Returned [] (no errors)
```

**Why useful:** You can verify refactoring correctness locally using LSP tools even when the broader build system has issues. The LSP server works at the file/module level, not the full project level.

**Practical implication:** Don't wait for a full clean build to verify refactorings—use LSP diagnostics for fast feedback.

### 12. Different Proof Types Need Different Refactoring Strategies

**First refactoring (constructive proof):**
- Proof type: Build permutation → apply it → verify equality
- Helpers: Computational bounds and structural properties
- Pattern: Build pieces → Assemble → Use

**This refactoring (uniqueness theorem application):**
- Proof type: Establish conditions → apply uniqueness → transform result
- Helpers: Conceptual properties (marginals equality, commutation)
- Pattern: Establish conditions → Apply theorem → Transform result

**Lesson:** The nature of the proof suggests what kinds of helpers make sense:
- **Constructive proofs** → Extract construction steps
- **Uniqueness/existence proofs** → Extract condition-checking lemmas
- **Computational proofs** → Extract calculation helpers

### 13. Examine Goal States Every 5-10 Lines

**What we did:** Checked goal states at 5 different lines (654, 659, 666, 683, 690) rather than just boundaries.

**What this revealed:**
- Lines 654-665: Probability measure instances established
- Lines 666-682: Marginals equality proved ← Natural helper boundary
- Line 683: Uniqueness theorem applied
- Lines 686-695: Result transformed back ← Another helper boundary

**Lesson:** Don't just look at start and end of proof. Examine goal states every 5-10 lines to understand logical flow and find natural refactoring boundaries.

**LSP workflow:**
```python
# Survey proof at regular intervals
for line in [654, 659, 666, 673, 680, 683, 690]:
    lean_goal(file, line)  # See proof state evolution
```

---

## Lessons from Third Refactoring: Witness Extraction Patterns

### 14. Witness Extraction Deserves Its Own Helpers

**Pattern:** When a proof uses `choose` (Lean's axiom of choice) to extract witnesses from existentials, this is often a natural refactoring boundary.

**Before (inline):**
```lean
have : ∀ i, ∃ (T : Set β), MeasurableSet[m i] T ∧ s = f ⁻¹' T := by
  intro i
  have hi := hs_all i
  rw [MeasurableSpace.measurableSet_comap] at hi
  rcases hi with ⟨T, hT, hpre⟩
  exact ⟨T, hT, hpre.symm⟩
choose T hTmeas hspre using this
```

**After (helper):**
```lean
obtain ⟨T, hTmeas, hspre⟩ := comap_iInf_witnesses m s hs_all
```

**Why it works:** Witness extraction has clear inputs (hypotheses) and outputs (chosen witnesses), making it naturally modular.

**Key insight:** `choose` creates a natural boundary—everything before produces the existential proof, everything after uses the witnesses.

### 15. Isolate Hypothesis Usage for Reusability

**Observation:** In this refactoring, only ONE helper uses the surjectivity hypothesis:

```lean
private lemma comap_witnesses_eq_of_surjective {ι : Type*} {α β : Type*}
    {f : α → β} (hf : Function.Surjective f) ...
    -- ← Only place surjectivity appears

-- Other helpers work without surjectivity
private lemma comap_iInf_witnesses ...  -- No surjectivity needed
```

**Why this matters:** The other helpers are potentially reusable in contexts without surjectivity.

**General principle:** When refactoring, identify which helpers need which hypotheses. Minimize hypothesis dependencies to maximize reusability.

**Practice:**
- Extract helper with minimal assumptions first
- Build more specialized helpers on top
- This creates a reusability hierarchy

### 16. "Pick Canonical Representative" Is a Common Pattern

**Pattern:** "All things are equal, so pick one"

```lean
-- Pick canonical witness T₀
rcases ‹Nonempty ι› with ⟨i₀⟩
let T0 : Set β := T i₀
have T_all : ∀ i, T i = T0 := fun i => Tall i i₀
```

**After refactoring, this pattern is isolated:**
- **Mathematical content** (witnesses are equal) → helper lemma
- **Proof engineering** (choice of which to use) → main proof

**Why separate:** The equality proof has mathematical content worth reusing. The choice of `i₀` is arbitrary proof engineering that doesn't generalize.

**General pattern:**
1. Prove all candidates equal (extract to helper)
2. Pick one arbitrarily (keep in main proof)
3. Use the fact they're all equal (proven by helper)

### 17. Structure Comments Tell "Why", Not "What"

**Compare comment styles:**

**❌ Bad (describes what code does):**
```lean
-- Choose the witnesses Tᵢ along with measurability and the preimage identity
```

**✅ Good (describes proof strategy):**
```lean
-- Extract witnesses Tᵢ such that s = f ⁻¹' Tᵢ for each i
```

**After refactoring, main proof has high-level strategy comments:**
```lean
-- (≥) direction holds unconditionally (monotonicity)
-- (≤) direction uses surjectivity to unify witnesses
-- Extract witnesses Tᵢ such that s = f ⁻¹' Tᵢ for each i
-- All witnesses are equal by surjectivity
-- Pick canonical witness T₀
-- Conclude measurability
```

**These guide the reader through:**
- Mathematical strategy (why each step)
- Proof structure (how steps fit together)
- Key insights (where hypotheses are used)

**Not just tactical details** (what each line does).

**Best practice for structure comments:**
- Start each major section with a comment
- Explain the mathematical goal, not the Lean syntax
- Highlight where key hypotheses are used
- Make it possible to understand the proof by reading only the comments

---

## Lessons from Fourth Refactoring: Domain Separation

**Context:** 130-line proof mixing finite probability distribution arithmetic (combinatorics) with L² variance bounds (functional analysis).

**Extracted helper:** 56-line lemma proving L¹ distance between probability distributions is ≤ 2.

**Result:** 130 lines → 79 lines (39% reduction)

### 18. Separate Domain-Specific Concerns

**Pattern:** When a proof mixes independent mathematical domains, extract each domain's logic into separate helpers.

**This proof had two distinct parts:**
1. **Finite probability distribution combinatorics** (51 lines): Pure finite sum manipulation, no measure theory
2. **L² variance-covariance calculation** (55 lines): Integration, measure theory, inequalities

**By extracting #1:**
```lean
-- Helper: Pure combinatorics (highly reusable)
private lemma prob_dist_diff_abs_sum_le_two
    (p q : Fin n → ℝ) (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
    (hp_nn : ∀ i, 0 ≤ p i) (hq_nn : ∀ i, 0 ≤ q i) :
    ∑ i, |p i - q i| ≤ 2 := by
  -- Self-contained proof using positive/negative partition
  ...

-- Main theorem: Now shows probabilistic content clearly
theorem l2_contractability_bound ... := by
  have hL1 := prob_dist_diff_abs_sum_le_two ...
  -- L² calculation now dominates (as it should)
  ...
```

**Benefits:**
- Main theorem reads at correct abstraction level (measure theory + probability)
- Helper is reusable in any context involving probability distribution distances
- Each proof uses only the tools from its domain
- Much easier to understand and maintain

**General principle:** Different mathematical domains → different helpers. Don't mix combinatorics with analysis, algebra with topology, etc.

### 19. Large Preliminary Calculations Are Prime Refactoring Targets

**Pattern:** If a proof starts with 50+ lines proving an auxiliary fact before the main argument, extract it.

**Anti-pattern:**
```lean
theorem main_result ... := by
  -- 51 lines proving preliminary combinatorial bound
  have hAux : ∑ i, |p i - q i| ≤ 2 := by
    [massive calculation with positive/negative partitions]
    ...
    [50 more lines]

  -- Now the actual L² calculation (obscured by above clutter!)
  calc ...
```

**Better:**
```lean
private lemma prob_dist_diff_abs_sum_le_two ... := by
  [massive calculation]
  ...

theorem main_result ... := by
  have hAux := prob_dist_diff_abs_sum_le_two ...
  -- Main argument immediately visible
  calc ...
```

**Why this signals a refactoring opportunity:**
- The preliminary fact has independent mathematical interest
- It's conceptually separate from the main argument
- Readers need to wade through 50 lines before seeing the "real" proof
- Testing/debugging is harder (can't isolate the preliminary fact)

**Rule of thumb:** If a `have` statement's proof exceeds 20 lines and establishes a fact with a clear mathematical name, extract it.

### 20. Named Steps with Comments Tell the Mathematical Story

**Pattern:** After refactoring, use named intermediate results with comments to make the proof read like a textbook.

**After refactoring, the main proof shows clear structure:**
```lean
theorem l2_contractability_bound ... := by
  -- Step 1: E(∑cᵢξᵢ)² = E(∑cᵢ(ξᵢ-m))² using ∑cⱼ = 0
  have step1 : ... := by ...

  -- Step 2: = ∑ᵢⱼ cᵢcⱼ cov(ξᵢ, ξⱼ) by expanding square
  have step2 : ... := by ...

  -- Step 3: = σ²ρ(∑cᵢ)² + σ²(1-ρ)∑cᵢ² by variance/covariance
  have step3 : ... := by ...

  -- Step 4: L¹ distance bound from helper (combinatorics)
  have step4 := prob_dist_diff_abs_sum_le_two ...

  -- Final: Combine steps to get L² bound
  calc ...
```

**This reads like a proof in a mathematics paper:**
- Each step has a clear mathematical meaning
- Comments explain the technique or justification
- The overall strategy is immediately visible
- Can be understood by reading only the step comments

**Contrast with original:**
```lean
theorem l2_contractability_bound ... := by
  have h1 : ... := by [10 lines]
  have h2 : ... := by [15 lines]
  have hAux : ... := by [51 lines of combinatorics!]
  have h3 : ... := by [8 lines]
  calc ... [complex expression]
```

**Benefits of named steps:**
- Mathematical narrative is clear
- Easy to locate where things go wrong
- Can test/verify each step independently with LSP (`lean_goal` after each step)
- Reviewers can understand proof structure without parsing every tactic

**Best practice:** After extracting helpers, reorganize the main proof with:
1. Named steps (`step1`, `step2`, ...) for major milestones
2. Comments explaining what each step achieves mathematically
3. Clear progression from hypotheses to conclusion

---

## Summary: When Witness Extraction Appears

**If your proof has this pattern:**
```lean
have : ∀ x, ∃ y, P x y := ...
choose y hy using this
```

**Consider extracting to:**
```lean
obtain ⟨y, hy⟩ := witnesses_helper ...
```

**Benefits:**
- Clear input/output contract (hypotheses → witnesses)
- Helper is testable independently
- Main proof reads at higher level
- Witness construction logic is reusable

**This refactoring achieved the best reduction** because witness extraction was very self-contained, making extraction especially clean.

---

## Additional Refactoring Patterns

### 21. Repetitive Structure (lhs/rhs Patterns)

**Pattern:** When proving both sides of an equation or multiple cases with nearly identical logic, extract the common pattern.

**What to look for:**
- Proofs with `have hlhs : ... := by [proof]` and `have hrhs : ... := by [similar proof]`
- Case splits where each branch has identical structure
- Multiple applications of the same technique to different objects

**Before (repetitive):**
```lean
theorem foo : lhs = rhs := by
  -- Prove lhs has property P (20 lines)
  have hlhs : P lhs := by
    intro x
    simp [complex_lemma]
    apply measurability_tactic
    ... [15 more lines]

  -- Prove rhs has property P (20 lines, nearly identical!)
  have hrhs : P rhs := by
    intro x
    simp [complex_lemma]
    apply measurability_tactic
    ... [15 more lines]

  -- Use both
  exact property_equality_from_P hlhs hrhs
```

**After (extracted helper):**
```lean
private lemma has_property_P (expr : α → β) (h : SomeCondition expr) : P expr := by
  intro x
  simp [complex_lemma]
  apply measurability_tactic
  ... [15 lines - written once]

theorem foo : lhs = rhs := by
  have hlhs := has_property_P lhs hlhs_cond
  have hrhs := has_property_P rhs hrhs_cond
  exact property_equality_from_P hlhs hrhs
```

**Benefits:**
- Write the proof logic once, not twice
- Changes apply to both sides automatically
- Main proof shows structure clearly: "Both sides satisfy P, therefore equal"
- Helper is reusable for future lhs/rhs proofs

**Rule of thumb:** If you copy-paste proof code with only variable names changed, extract a helper.

### 22. Property Bundling with Conjunctions

**Pattern:** When multiple related properties are proven separately but always used together, bundle them with `∧` and use `obtain` to destructure.

**Before (properties scattered):**
```lean
theorem bar : FinalGoal := by
  have h1 : Property1 x := by [proof]
  have h2 : Property2 x := by [proof]
  have h3 : Property3 x := by [proof]
  -- Later: use all three together
  exact final_lemma h1 h2 h3
```

**After (bundled helper):**
```lean
private lemma bundle_properties (x : α) (hx : Condition x) :
    Property1 x ∧ Property2 x ∧ Property3 x := by
  constructor
  · [proof of Property1]
  constructor
  · [proof of Property2]
  · [proof of Property3]

theorem bar : FinalGoal := by
  obtain ⟨h1, h2, h3⟩ := bundle_properties x hx
  exact final_lemma h1 h2 h3
```

**Benefits:**
- Clear relationship: These properties belong together
- Single lemma name documents the bundling
- `obtain` destructures cleanly
- Easier to reuse the bundle elsewhere

**When to bundle:**
- Properties share same hypotheses
- Always proven together in a sequence
- Conceptually related (e.g., "measurability + integrability", "probability measure properties")
- No independent use cases for individual properties

**When NOT to bundle:**
- Properties have different hypotheses
- Sometimes used independently
- No conceptual relationship (just happen to be nearby)

### 23. Generic is Better

**Pattern:** When extracting helpers, remove proof-specific constraints to maximize reusability.

**Before (too specific):**
```lean
-- Extracted from one specific proof about our particular function f
private lemma helper_for_my_proof (n : ℕ) (hn : n = 42) : Property n := by
  rw [hn]
  exact specific_lemma_for_42
```

**After (generic):**
```lean
-- Works for any n ≥ 1, not just 42
private lemma helper_general (n : ℕ) (hn : 1 ≤ n) : Property n := by
  cases n with
  | zero => omega  -- contradicts 1 ≤ n
  | succ n' => exact general_lemma
```

**How to generalize:**
1. **Relax equality to inequality:** `n = 42` → `1 ≤ n`
2. **Remove specific values:** `f = our_function` → any `f` satisfying the condition
3. **Weaken hypotheses:** Use only what's actually needed in the proof
4. **Broaden types:** `Fin 10` → `Fin n` if the bound doesn't matter

**Example from measure theory:**
```lean
-- ❌ Too specific (only for product measures)
private lemma rectangle_measurable_product (s : Set (α × β)) : ... := by
  ...

-- ✅ Generic (works for any MeasurableSpace structure)
private lemma rectangle_as_pi_measurable (s : Set (∀ i : Fin 2, α i)) : ... := by
  ...
```

**Benefits:**
- Helper works in future proofs with similar structure
- Easier to understand (fewer arbitrary constraints)
- Forces you to identify the essential conditions
- Builds a reusable library of project-specific lemmas

**Balance:** Don't over-generalize to the point where the proof becomes much harder or the helper needs 10+ parameters.

### 24. Notation Conversion Helpers

**Pattern:** Proofs often need to convert between equivalent notations. Extract conversion helpers that are reusable.

**Common conversions:**
- Set builder ↔ pi notation: `{x | ∀ i, x i ∈ s i}` ↔ `Set.univ.pi s`
- Membership ↔ function application: `x ∈ S` ↔ `S x = true`
- Measure ↔ integral: `μ s` ↔ `∫⁻ x, s.indicator 1 ∂μ`
- Preimage ↔ set comprehension: `f ⁻¹' t` ↔ `{x | f x ∈ t}`

**Before (conversion inline):**
```lean
theorem qux : MeasurableSet s := by
  -- Want: s is measurable
  -- Have: s = Set.univ.pi (fun i => t i)

  -- Inline conversion (10 lines)
  unfold Set.pi
  simp only [Set.mem_univ, true_and]
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  ... [more conversion logic]

  -- Now apply measurability
  exact measurable_cylinder
```

**After (extracted conversion):**
```lean
private lemma pi_notation_measurable (t : ∀ i, Set (α i))
    (ht : ∀ i, MeasurableSet (t i)) :
    MeasurableSet (Set.univ.pi t) := by
  unfold Set.pi
  simp only [Set.mem_univ, true_and]
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact ht i

theorem qux : MeasurableSet s := by
  rw [hs]  -- s = Set.univ.pi (fun i => t i)
  exact pi_notation_measurable t ht
```

**Benefits:**
- Conversion logic written once, used everywhere
- Main proof focuses on mathematics, not notation
- Helper has clear purpose: "convert representation X to Y"
- Highly reusable across similar proofs

**Common helpers to extract:**
```lean
-- Rectangle notation for measure theory
private lemma rectangle_as_pi : s = Set.univ.pi t ↔ ∀ x, x ∈ s ↔ ∀ i, x i ∈ t i

-- Measurability under conversion
private lemma measurable_pi_iff : MeasurableSet (Set.univ.pi t) ↔ ∀ i, MeasurableSet (t i)

-- Measure preservation under pushforward
private lemma pushforward_preserves_prob : IsProbabilityMeasure μ → IsProbabilityMeasure (μ.map f)
```

**Rule of thumb:** If you're doing the same 5-10 line conversion in multiple places, extract it.

---

## Refactoring Decision Tree

```
Is the proof 60-200 lines? (sweet spot for refactoring)
├─ Yes: Look for natural boundaries (use lean_goal at 4-5 key points)
│   ├─ Repetitive structure (lhs/rhs with near-identical proofs)?
│   │   └─ Extract common pattern to helper (Pattern 21)
│   ├─ Multiple properties proven separately, used together?
│   │   └─ Bundle with ∧, use obtain (Pattern 22)
│   ├─ Mixes multiple mathematical domains (combinatorics + analysis)?
│   │   └─ Extract each domain's logic separately (Pattern 18)
│   ├─ Starts with 50+ line preliminary calculation?
│   │   └─ Extract preliminary fact to helper (Pattern 19)
│   ├─ Same 5-10 line notation conversion repeated?
│   │   └─ Extract conversion helper (Pattern 24)
│   ├─ Found witness extraction (choose/obtain)?
│   │   └─ Extract to helper (clear input/output contract)
│   ├─ Found arithmetic bounds?
│   │   ├─ Can extract without `let` bindings? → Extract to private helper
│   │   └─ Uses complex `let` bindings? → Consider inlining
│   ├─ Found permutation construction?
│   │   └─ Reusable pattern? → Extract (ensure parameter clarity)
│   ├─ Found "all equal, pick one" pattern?
│   │   ├─ Equality proof → Extract to helper (mathematical content)
│   │   └─ Choice of representative → Keep in main (proof engineering)
│   └─ Found measure manipulations?
│       └─ Uses `let` bindings? → Prefer inlining (definitional issues)
├─ > 200 lines? → Multiple refactorings needed (start with largest prelims)
└─ < 60 lines? → Probably fine as-is (unless heavily repetitive)

When extracting:
1. Make helper `private` if proof-specific (use regular -- comments, not /-- -/)
2. **Generic is better** (Pattern 23): Remove proof-specific constraints
   - Relax equality to inequality (n = 42 → 1 ≤ n)
   - Weaken hypotheses to minimum needed
   - Broaden types when possible
3. Avoid `let` bindings in helper signatures:
   - Option A: Use explicit parameters with equality proofs (param + hparam : param = expr)
   - Option B: Inline the proof if measure theory manipulation
4. If omega fails, add explicit intermediate steps (use calc)
5. Prefix unused but required parameters with underscore (_hS)
6. Add structural comments that explain "why", not "what"
7. Isolate hypothesis usage—extract with minimal assumptions first
8. Document what the helper proves and why
9. Test compilation after each extraction with lean_diagnostic_messages
10. Check goal states at 4-5 key points to find natural boundaries

After refactoring:
11. Use named steps (step1, step2, ...) with comments (Pattern 20)
```

---

## Benefits of Refactoring

**Maintainability:**
- Easier to understand small proofs
- Easier to modify without breaking
- Clear dependencies between lemmas

**Reusability:**
- Helper lemmas useful in other contexts
- Avoid reproving same intermediate results
- Build library of project-specific lemmas

**Testing:**
- Test helpers independently
- Isolate errors to specific lemmas
- Faster compilation (smaller units)

**Collaboration:**
- Easier to review small lemmas
- Clear boundaries for parallel work
- Better documentation opportunities

---

## Anti-Patterns

**❌ Over-refactoring:**
- Creating helpers used only once
- Extracting every `have` statement
- Too many small lemmas (harder to navigate)

**❌ Under-refactoring:**
- 500+ line proofs
- Multiple independent results in one theorem
- Repeated code instead of shared helpers

**❌ Poor parameter choices:**
- Extracting with 15+ parameters
- Including unnecessary generality
- Making helpers too specific to one use case

**✅ Good balance:**
- Extract when reusable or conceptually distinct
- Aim for 20-80 line helpers
- Parameters capture essential dependencies only

---

## See Also

- [lean-lsp-tools-api.md](lean-lsp-tools-api.md) - LSP tools for goal inspection
- [proof-golfing.md](proof-golfing.md) - Simplifying proofs after compilation
- [mathlib-style.md](mathlib-style.md) - Naming conventions
