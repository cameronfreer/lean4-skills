# Proof Golfing: Simplifying Proofs After Compilation

## TLDR

**Core principle:** First make it compile, then make it clean.

**When to use:** After `lake build` succeeds on stable files. Expected 30-40% reduction with proper safety filtering.

**When NOT to use:** Active development, already-optimized code (mathlib-quality), or missing verification tools (93% false positive rate without them).

**Critical:** MUST verify let binding usage before inlining. Bindings used ≥3 times should NOT be inlined (would increase code size).

## Quick Reference: Pattern Priority

| Pattern | Savings | Risk | Priority | Notes |
|---------|---------|------|----------|-------|
| `rw; exact` → `rwa` | 50% | Zero | ⭐⭐⭐⭐⭐ | Always safe, instant |
| `ext + rfl` → `rfl` | 67% | Low | ⭐⭐⭐⭐⭐ | Test first, revert if fails |
| **intro-dsimp-exact → lambda** | **75%** | **Low** | **⭐⭐⭐⭐⭐** | **Tactic proof → direct term** |
| **Extract repeated tactic patterns to helpers** | **40%** | **Low** | **⭐⭐⭐⭐⭐** | **Reusable term with ∀** |
| let+have+exact inline | 60-80% | HIGH | ⭐⭐⭐⭐⭐ | MUST verify usage ≤2x |
| **Single-use `have` inline (general)** | **30-50%** | **Low** | **⭐⭐⭐⭐** | **Beyond calc blocks** |
| **Remove redundant `show` wrappers** | **50-75%** | **Low** | **⭐⭐⭐⭐** | **`simp` handles it** |
| **Convert-based helper inlining** | **30-40%** | **Medium** | **⭐⭐⭐⭐** | **`convert ... using N`** |
| Redundant `ext` before `simp` | 50% | Medium | ⭐⭐⭐⭐ | Not all ext is redundant |
| `congr; ext; rw` → `simp only` | 67% | Medium | ⭐⭐⭐⭐ | simp is smarter than you think |
| **`simpa using` → `exact`** | **1 token** | **Zero** | **⭐⭐⭐** | **When `simp` does nothing** |
| **Unused lambda variables cleanup** | **0 lines** | **Zero** | **⭐⭐⭐** | **Eliminates linter warnings** |
| **calc with rfl for definitions** | **Clarity** | **Zero** | **⭐⭐⭐** | **Faster than proof search** |
| **refine with ?_ for term construction** | **Clarity** | **Low** | **⭐⭐⭐** | **Structure over separate have** |
| Smart `ext` (nested) | 50% | Low | ⭐⭐⭐ | ext handles multiple layers |
| `simp` closes goals directly | 67% | Low | ⭐⭐⭐ | Remove explicit `exact` |
| have-calc single-use inline | 50% | Low | ⭐⭐⭐ | Only if used once in calc |
| **Remove duplicate inline comments** | **Lines** | **Zero** | **⭐⭐** | **If docstring is complete** |
| ext-simp chain combination | Variable | Medium | ⭐⭐ | Only when saves ≥2 lines |
| Arithmetic with automation | 30-50% | Medium | ⭐⭐ | Direct lemmas often better |

**New patterns in bold** - discovered from real-world optimization sessions.

**ROI Strategy:** Do ⭐⭐⭐⭐⭐ first (instant wins), then ⭐⭐⭐⭐ (quick with testing), skip ⭐-⭐⭐ if time-limited.

## Critical Safety Warnings

### The 93% False Positive Problem

**Key finding:** Without proper analysis, 93% of "optimization opportunities" are false positives that make code WORSE.

**The Multiple-Use Heuristic:**
- Bindings used 1-2 times: Safe to inline
- Bindings used 3-4 times: 40% worth optimizing (check carefully)
- Bindings used 5+ times: NEVER inline (would increase size 2-4×)

**Example - DON'T optimize:**
```lean
let μ_map := Measure.map (fun ω i => X (k i) ω) μ  -- 20 tokens
-- Used 7 times in proof
-- Current: 20 + (2 × 7) = 34 tokens
-- Inlined: 20 × 7 = 140 tokens (4× WORSE!)
```

### When NOT to Optimize

**Skip if ANY of these:**
- ❌ Let binding used ≥3 times
- ❌ Complex proof with case analysis
- ❌ Semantic naming aids understanding
- ❌ Would create deeply nested lambdas (>2 levels)
- ❌ Readability Cost = (nesting depth) × (complexity) × (repetition) > 5

### Saturation Indicators

**Stop when:**
- ✋ Optimization success rate < 20%
- ✋ Time per optimization > 15 minutes
- ✋ Most patterns are false positives
- ✋ Debating whether 2-token savings is worth it

**Benchmark:** Well-maintained codebases reach saturation after ~20-25 optimizations.

## High-Priority Patterns (⭐⭐⭐⭐⭐)

### Pattern 1: `rw; exact` → `rwa`

Standard mathlib idiom. `rwa` = "rewrite and assumption".

```lean
-- Before (2 lines)
rw [hlhs_eq, hrhs_eq] at hproj_eq
exact hproj_eq

-- After (1 line)
rwa [hlhs_eq, hrhs_eq] at hproj_eq
```

**When:** Any `rw [...] at h` followed by `exact h`
**Risk:** Zero (always works)
**Savings:** 50% reduction

### Pattern 2: `ext + rfl` → `rfl`

When terms are definitionally equal, `rfl` suffices without `ext`.

```lean
-- Before (3 lines)
have h : proj ∘ (fun ω => fun i : ℕ => X i ω)
       = fun ω => fun i : Fin n => X i.val ω := by
  ext ω i; rfl

-- After (1 line)
have h : proj ∘ (fun ω => fun i : ℕ => X i ω)
       = fun ω => fun i : Fin n => X i.val ω := rfl
```

**When:** Proof is `by ext ...; rfl` and terms compute to same result
**Risk:** Low (test with build, revert if fails)
**Savings:** 67% reduction
**Warning:** Not all `ext + rfl` can be simplified!

### Pattern 2A: `intro-dsimp-exact` → Direct Lambda

**⭐⭐⭐⭐⭐ HIGH-IMPACT PATTERN** - Common and gives 75% reduction!

Convert tactic proofs that just unfold and extract a term into direct lambda expressions.

```lean
-- Before (4 lines)
have hι_mem : ∀ i : Fin m, p (ι i) := by
  intro i
  dsimp [p, ι]
  exact i.isLt

-- After (1 line)
have hι_mem : ∀ i : Fin m, p (ι i) := fun i => i.isLt
```

**When to apply:**
- Proof is `intro x; dsimp [...]; exact term`
- The `term` is just field access or coercion after unfolding
- No complex logic, just definitional simplification

**Pattern recognition:**
```lean
-- Generic pattern
have h : ∀ x, P x := by
  intro x
  dsimp [definitions]
  exact simple_term_involving_x

-- Becomes
have h : ∀ x, P x := fun x => simple_term_involving_x
```

**When:** Tactic proof is just intro + trivial unfolding + term extraction
**Risk:** Low (if proof body is just field access after unfolding)
**Savings:** 75% reduction (4 lines → 1 line)

**Real-world example:**
```lean
-- Before
have hk_inj : Function.Injective k' := by
  intro i j hij
  simp only [k'] at hij
  exact Fin.val_injective (hk_inj hij)

-- After
have hk_inj : Function.Injective k' := fun i j hij =>
  Fin.val_injective (hk_inj hij)
```

### Pattern 2B: Extract Repeated Tactic Patterns to Helpers

**⭐⭐⭐⭐⭐ HIGH-IMPACT** - Eliminates duplication when same tactic proof appears multiple times.

Convert repeated tactic proofs into single reusable helper using universal quantifier.

```lean
-- Before (8 lines, duplication)
have hf' : ∀ x ∈ Ioo a b, HasDerivAt f (deriv f x) x := by
  intro x hx
  exact ((hfd x hx).differentiableAt (IsOpen.mem_nhds isOpen_Ioo hx)).hasDerivAt
have hg' : ∀ x ∈ Ioo a b, HasDerivAt g (deriv g x) x := by
  intro x hx
  exact ((hgd x hx).differentiableAt (IsOpen.mem_nhds isOpen_Ioo hx)).hasDerivAt

-- After (5 lines, single helper)
have toHasDerivAt {h : ℝ → ℝ} (hd : DifferentiableOn ℝ h (Ioo a b)) :
    ∀ x ∈ Ioo a b, HasDerivAt h (deriv h x) x :=
  fun x hx => ((hd x hx).differentiableAt (IsOpen.mem_nhds isOpen_Ioo hx)).hasDerivAt
have hf' := toHasDerivAt hfd
have hg' := toHasDerivAt hgd
```

**Pattern recognition:**
- Same tactic proof structure repeated for different functions
- Only function/hypothesis changes between instances
- Proof body is linear (intro → exact, no case analysis)

**When to apply:**
- ✅ Pattern appears 2+ times
- ✅ Can abstract over changing parts (function, hypothesis)
- ✅ Helper makes code clearer, not more complex

**When NOT to apply:**
- ❌ Pattern appears only once
- ❌ Variations too different to unify cleanly
- ❌ Helper would be more complex than duplication

**Savings:** 40% reduction, improves maintainability
**Risk:** Low (helper is just term-mode proof)

### Pattern 3: let+have+exact Inline

**⚠️ MOST VALUABLE but HIGHEST RISK - MUST verify safety first!**

```lean
-- Before (14 lines, ~140 tokens)
lemma foo ... := by
  intro m k hk_mono
  let k' : Fin m → ℕ := fun i => (k i).val
  have hk'_mono : StrictMono k' := by
    intro i j hij
    simp only [k']
    exact hk_mono hij
  exact hX m k' hk'_mono

-- After (2 lines, ~38 tokens)
lemma foo ... := by
  intro m k hk_mono
  exact hX m (fun i => (k i).val) (fun i j hij => hk_mono hij)
```

**When to apply (ALL must be true):**
- ✅ Let binding used ≤2 times (preferably only in have and exact)
- ✅ Have proof is simple (no complex case analysis)
- ✅ Final result accepts lambda arguments
- ✅ No semantic naming value lost

**When NOT to apply (ANY = skip):**
- ❌ Let binding used ≥3 times
- ❌ Complex proof logic (cases, nested proofs)
- ❌ Let binding represents important semantic concept
- ❌ Would create deeply nested lambdas (>2 levels)

**Verification:** Use `analyze_let_usage.py` to count uses. Manual verification leads to errors.

**Savings:** 60-80% reduction when applicable
**Risk:** HIGH (93% false positive rate without verification)

### Pattern 3A: General Single-Use `have` Inlining (⭐⭐⭐⭐)

**Extension of Pattern 3** - Applies beyond `let+have+exact` to ANY single-use `have` statement.

```lean
-- Before (3 lines)
have hf_id_meas : Measurable f_id := measurable_pi_lambda _ ...
have hf_perm_meas : Measurable f_perm := measurable_pi_lambda _ ...
rw [← Measure.map_map hproj_meas hf_perm_meas,
    ← Measure.map_map hproj_meas hf_id_meas]

-- After (inline directly when used once - 2 lines)
rw [← Measure.map_map hproj_meas (measurable_pi_lambda _ ...),
    ← Measure.map_map hproj_meas (measurable_pi_lambda _ ...)]
```

**When to apply (ALL must be true):**
- ✅ `have` used exactly once anywhere in proof (not just calc)
- ✅ Proof term < 40 chars or low complexity
- ✅ No semantic naming value (name like `h_meas` vs descriptive `homotopy_preserves_paths`)
- ✅ Doesn't obscure proof flow

**When NOT to apply:**
- ❌ `have` used ≥2 times
- ❌ Long or complex proof term (would hurt readability)
- ❌ Semantic name aids understanding
- ❌ Part of structured proof narrative

**Difference from docs Pattern 8 (have-calc):**
- Docs focus on calc-specific inlining
- This pattern applies to ALL single-use haves
- Same safety principles, broader application

**Savings:** 30-50% per instance
**Risk:** Low (if truly single-use and term is simple)

## Medium-Priority Patterns (⭐⭐⭐⭐)

### Pattern 4: Redundant `ext` Before `simp`

For common types (Fin, Prod, Subtype), `simp` handles extensionality automatically.

```lean
-- Before (2 lines)
have h : (⟨i.val, ...⟩ : Fin n) = ι i := by
  apply Fin.ext
  simp [ι]

-- After (1 line)
have h : (⟨i.val, ...⟩ : Fin n) = ι i := by simp [ι]
```

**When:** `apply X.ext; simp` for Fin, Prod, Subtype
**Risk:** Medium (not all ext is redundant - test!)
**Savings:** 50% reduction

**Failed example - ext was necessary:**
```lean
ext x; simp [foo]  -- ✅ Works
simp [foo]         -- ❌ Fails - simp needs goal decomposed first
```

### Pattern 5: `congr; ext; rw` → `simp only`

`simp` automatically applies congruence and extensionality when needed.

```lean
-- Before (3 lines)
lemma foo ... :
    Measure.map (fun ω i => X (k₁ i) ω) μ =
    Measure.map (fun ω i => X (k₂ i) ω) μ := by
  congr 1; ext ω i; rw [h_range]

-- After (1 line)
lemma foo ... :
    Measure.map (fun ω i => X (k₁ i) ω) μ =
    Measure.map (fun ω i => X (k₂ i) ω) μ := by
  simp only [h_range]
```

**When:** Manual structural reasoning (`congr`, `ext`) before `rw` or `simp`
**Lesson:** simp is smarter than you think - try it first!
**Savings:** 67% reduction

### Pattern 5A: Remove Redundant `show` Wrappers

When `simp` handles the equality directly, `show X by simp` wrappers are unnecessary.

```lean
-- Before (4 lines)
rw [show (Set.univ : Set (∀ i, α i)) = Set.univ.pi (fun _ => Set.univ) by simp,
    Measure.pi_pi]
simp [measure_univ]

-- After (1 line)
simp [measure_univ]
```

**Pattern recognition:**
```lean
-- Generic
rw [show X = Y by simp, other_lemma]
simp [...]

-- Becomes (simp handles X = Y)
simp [...]
```

**When to apply:**
- `show X by simp` wrapper where simp proves the equality
- The wrapped equality is used only for this simp call
- simp can handle it directly in context

**When:** `show X by simp` wrapper is unnecessary - simp handles it in context
**Risk:** Low (test with build to confirm simp handles it)
**Savings:** 50-75% reduction

### Pattern 5B: Convert-Based Helper Inlining

Replace helper equality lemmas with inline `convert ... using N` to avoid separate `have` statements.

```lean
-- Before (8 lines with helper lemma)
have hfun : (fun f : ι → α => f ∘ σ) =
    (MeasurableEquiv.piCongrLeft ...) := by
  ext g i
  simp [...]
simpa [hfun] using main_proof

-- After (5 lines, inline with convert)
convert (MeasureTheory.measurePreserving_piCongrLeft ...).map_eq using 2
ext g i
simp [...]
```

**Pattern recognition:**
- Helper `have` proves equality `f = g`
- Used once in `simpa [hfun]` or `exact ... hfun ...`
- Can be inlined with `convert` + appropriate `using` level

**Technique:**
- `convert target using N` where `N` is the unification depth
- The `using N` tells Lean how many steps to unfold before checking equality
- Common values: `using 1` (surface level), `using 2` (one level deep)

**When to apply:**
- Helper equality used just for rewriting in simpa/exact
- Converting to direct proof is clearer
- You know the right `using` level (trial and error is OK)

**When:** Helper equality just for rewriting once
**Risk:** Medium (need right `using` level, may need trial-error)
**Savings:** 30-40% reduction

### Pattern 6: Smart `ext`

`ext` handles multiple nested extensionality layers automatically.

```lean
-- Before (4 lines)
apply Subtype.ext
apply Fin.ext
simp [ι]

-- After (2 lines)
ext; simp [ι]
```

**When:** Nested extensionality (Subtype of Fin, functions returning subtypes, etc.)
**Savings:** 50% reduction

### Pattern 7: `simp` Closes Goals Directly

When `simp` makes goal trivial, skip explicit `exact`.

```lean
-- Before (3 lines)
have hlt : j < j_succ := by
  simp only [Fin.lt_iff_val_lt_val, j, j_succ]
  exact Nat.lt_succ_self n

-- After (1 line)
have hlt : j < j_succ := by simp [Fin.lt_iff_val_lt_val, j, j_succ]
```

**When:** Goal becomes trivial after unfolding, or `exact` applies lemma simp knows
**Savings:** 67% reduction

## Medium-Priority Patterns (⭐⭐⭐)

### Pattern 7A: `simpa using` → `exact`

When `simpa` does no actual simplification work, use `exact` for clarity.

```lean
-- Before
simpa using (MeasureTheory.Measure.pi_comp_perm ...).symm

-- After
exact (MeasureTheory.Measure.pi_comp_perm ...).symm
```

**When to apply:**
- The `simp` in `simpa` does no actual simplification
- Goal matches the provided term exactly
- Clarifies that no simplification is happening

**How to detect:**
- Try replacing `simpa using h` with `exact h`
- If it works, `simpa` was doing nothing

**When:** Simplification does no actual work
**Risk:** Zero (if simp truly does nothing, exact is equivalent and clearer)
**Savings:** 1 token, but improves intent clarity

### Pattern 7B: Unused Lambda Variable Cleanup

Replace unused lambda parameters with `_` to eliminate linter warnings.

```lean
-- Before (triggers linter warnings)
fun i j hij => proof_not_using_i_or_j

-- After (clean, no warnings)
fun _ _ hij => proof_not_using_i_or_j
```

**When to apply:**
- Lambda binds parameters that are never used
- Linter warns about unused variables
- Code quality matters

**When:** Lambda parameters bound but never used
**Risk:** Zero (pure cleanup)
**Savings:** 0 lines but eliminates linter noise and improves code quality

**Note:** This is a code quality improvement, not a size optimization. However, eliminating linter warnings makes real issues more visible.

### Pattern 7C: Use calc with rfl for Definitional Equalities

Use `rfl` in calc chains for definitional unfolding steps - faster than proof search.

```lean
-- Before (multiple intermediate steps)
have h0 : deriv f x * Δg - deriv g x * Δf = 0 := hF'0
have eq' : (f b - f a) * (deriv g x) = (g b - g a) * (deriv f x) := by
  have := (sub_eq_zero.mp h0).symm
  simpa [Δf, Δg, mul_comm, mul_left_comm, mul_assoc] using this

-- After (clean calc with rfl for definitions)
calc (f b - f a) * deriv g x
    = Δf * deriv g x := rfl
  _ = Δg * deriv f x := by simpa [Δf, Δg, mul_comm] using (sub_eq_zero.mp hF'0).symm
  _ = (g b - g a) * deriv f x := rfl
```

**When to apply:**
- ✅ Step is definitional unfolding (let binding, def)
- ✅ Makes transformation steps explicit
- ✅ rfl is faster than any proof search

**Pattern recognition:**
- Intermediate variable that's just a definition
- Can write `X = def_expansion` where equality is definitional
- Using `by simp [def]` when `rfl` would work

**When:** Definitional equalities in calc chains
**Risk:** Zero (rfl fails if not definitional, caught at compile)
**Savings:** Clarity + performance (rfl is instant)

### Pattern 7D: Use refine with ?_ for Complex Term Construction

Replace separate `have` with inline `refine` when constructing terms with one remaining proof obligation.

```lean
-- Before (separate equality proof)
have eq' : (f b - f a) * deriv g x = (g b - g a) * deriv f x := by ...
exact ⟨c, hc, deriv f c, deriv g c, hf', hg', eq'⟩

-- After (refine with hole)
refine ⟨c, hc, deriv f c, deriv g c, toHasDerivAt hfd c hc, toHasDerivAt hgd c hc, ?_⟩
calc (f b - f a) * deriv g x
    = Δf * deriv g x := rfl
  _ = Δg * deriv f x := by ...
  _ = (g b - g a) * deriv f x := rfl
```

**When to apply:**
- ✅ Constructing term with multiple fields
- ✅ Most fields are ready, one needs proof
- ✅ Makes structure clearer - "building term with one piece left"

**When NOT to apply:**
- ❌ Multiple fields need proofs (too many holes)
- ❌ Proof is trivial (just inline it)
- ❌ Separate `have` with descriptive name aids understanding

**When:** Complex term construction with one remaining proof
**Risk:** Low (makes intent clearer)
**Savings:** Clarity (similar line count but better structure)

### Pattern 8: have-calc Single-Use Inline

When `have` is used exactly once in subsequent `calc`, inline directly.

```lean
-- Before (4 lines)
have hsqrt : Real.sqrt (Cf / m) < Real.sqrt (ε^2 / 4) :=
  Real.sqrt_lt_sqrt hnonneg hlt
calc Real.sqrt (Cf / m)
    < Real.sqrt (ε^2 / 4) := hsqrt

-- After (2 lines)
calc Real.sqrt (Cf / m)
    < Real.sqrt (ε^2 / 4) := Real.sqrt_lt_sqrt hnonneg hlt
```

**When to inline:**
- ✅ `have` used exactly once in calc
- ✅ Proof term < 40 chars
- ✅ No descriptive value in name

**When NOT:**
- ❌ Used multiple times in calc
- ❌ Proof term > 40 chars
- ❌ Descriptive name aids understanding (e.g., `h_measurable`)
- ❌ Binding reused outside calc

**Savings:** ~50% line reduction

### Pattern 9: Inline Constructor Branches

```lean
-- Before (7 lines)
constructor
· intro k hk
  exact hX m k hk
· intro ν' hν'
  have hid : StrictMono ... := fun i j hij => hij
  have h := hν' (fun i => i.val) hid
  exact h.symm

-- After (3 lines)
constructor
· intro k hk; exact hX m k hk
· intro ν' hν'; exact (hν' (fun i => i.val) (fun i j hij => hij)).symm
```

**When:** Simple constructor branches, saves ≥2 lines, stays readable
**Savings:** 30-57% per instance

### Pattern 10: Direct Lemma Over Automation

For simple goals, direct mathlib lemmas (≤5 tokens) are shorter AND more reliable than automation.

```lean
-- ❌ Wrong (longer AND fails!)
exact hX m (fun i => k + i.val) (fun i j hij => by omega)
-- Error: omega produces counterexample with Fin coercions!

-- ✅ Correct (shorter AND works!)
exact hX m (fun i => k + i.val) (fun i j hij => Nat.add_lt_add_left hij k)
```

**When NOT to use automation:**
- Direct mathlib lemma ≤5 tokens available
- Simple Nat arithmetic (omega struggles with coercions)
- Automation overhead > direct application

**Lesson:** omega with Fin coercions often fails

## Systematic Workflow

### Phase 1: Pattern Discovery (5 min)

Use systematic search, not sequential reading:

```bash
# 1. Find let+have+exact (HIGHEST value)
grep -A 10 "let .*:=" file.lean | grep -B 8 "exact"

# 2. Find by-exact wrappers
grep -B 1 "exact" file.lean | grep "by$"

# 3. Find ext+simp patterns
grep -n "ext.*simp" file.lean

# 4. Find rw+exact (for rwa)
grep -A 1 "rw \[" file.lean | grep "exact"
```

**Expected:** 10-15 targets per file

### Phase 2: Safety Verification (CRITICAL)

For each let+have+exact pattern:

1. Count let binding uses (or use `analyze_let_usage.py`)
2. If used ≥3 times → SKIP (false positive)
3. If used ≤2 times → Proceed with optimization

**Other patterns:** Verify compilation test will catch issues.

### Phase 3: Apply with Testing (5 min per pattern)

1. Apply optimization
2. Run `lake build`
3. If fails: revert immediately, move to next
4. If succeeds: continue

**Strategy:** Apply 3-5 optimizations, then batch test.

### Phase 4: Check Saturation

After 5-10 optimizations, check indicators:
- Success rate < 20% → Stop
- Time per optimization > 15 min → Stop
- Mostly false positives → Stop

**Recommendation:** Declare victory at saturation.

## Documentation Quality Patterns (⭐⭐)

### Pattern 11: Remove Duplicate Inline Comments

When comprehensive docstrings exist above a proof, inline comments that restate the same information are redundant.

```lean
-- Before (with comprehensive docstring above)
/-- Computes measure by factoring through permutation then identity,
    applying the product formula twice. -/
calc Measure.map ...
    -- Factor as permutation composed with identity
    = ... := by rw [...]
    _ -- Apply product formula for identity
    = ... := by rw [...]

-- After (docstring is the single source of truth)
/-- Computes measure by factoring through permutation then identity,
    applying the product formula twice. -/
calc Measure.map ...
    = ... := by rw [...]
    _ = ... := by rw [...]
```

**When to apply:**
- Comprehensive docstring already explains the proof strategy
- Inline comments duplicate information from docstring
- Comments don't add new insights beyond docstring
- Goal is single source of truth for documentation

**When NOT to apply:**
- Inline comments provide details NOT in docstring
- Comments explain non-obvious steps
- No docstring exists (then comments are valuable!)
- Comments mark TODO or highlight subtleties

**Principle:** Single source of truth for documentation. Comprehensive docstrings document strategy; code documents details only if non-obvious.

**When:** Inline comments restate comprehensive docstring
**Risk:** Zero if docstring is complete
**Savings:** Lines + visual clarity

## Anti-Patterns

### Don't Use Semicolons Just to Combine Lines

```lean
-- ❌ Bad (no savings)
intro x; exact proof  -- Semicolon is a token!

-- ✅ Good (when saves ≥2 lines AND sequential)
ext x; simp [...]; use y; simp  -- Sequential operations
```

**When semicolons ARE worth it:**
- ✅ Sequential operations (ext → simp → use)
- ✅ Saves ≥2 lines
- ✅ Simple steps

### Don't Over-Inline

If inlining creates unreadable proof, keep intermediate steps:

```lean
-- ❌ Bad - unreadable
exact combine (obscure nested lambdas spanning 100+ chars)

-- ✅ Good - clear intent
have h1 : A := ...
have h2 : B := ...
exact combine h1 h2
```

### Don't Remove Helpful Names

```lean
-- ❌ Bad
have : ... := by ...  -- 10 lines
have : ... := by ...  -- uses first anonymous have

-- ✅ Good
have h_key_property : ... := by ...
have h_conclusion : ... := by ...  -- uses h_key_property
```

## Failed Optimizations (Learning)

### Not All `ext` Calls Are Redundant

```lean
-- Original (works)
ext x; simp [prefixCylinder]

-- Attempted (FAILS!)
simp [prefixCylinder]  -- simp alone didn't make progress
```

**Lesson:** Sometimes simp needs goal decomposed first. Always test.

### omega with Fin Coercions

```lean
-- Attempted (FAILS with counterexample!)
by omega

-- Correct (works)
Nat.add_lt_add_left hij k
```

**Lesson:** omega struggles with Fin coercions. Direct lemmas more reliable.

## Appendix

### Token Counting Quick Reference

```lean
// ~1 token each
let, have, exact, intro, by, fun

// ~2 tokens each
:=, =>, (fun x => ...), StrictMono

// ~5-10 tokens
let x : Type := definition
have h : Property := by proof
```

**Rule of thumb:**
- Each line ≈ 8-12 tokens
- Each have + proof ≈ 15-20 tokens
- Each inline lambda ≈ 5-8 tokens

### Saturation Metrics

**Session-by-session data:**
- Session 1-2: 60% of patterns worth optimizing
- Session 3: 20% worth optimizing
- Session 4: 6% worth optimizing (diminishing returns)

**Time efficiency:**
- First 15 optimizations: ~2 min each
- Next 7 optimizations: ~5 min each
- Last 3 optimizations: ~18 min each

**Point of diminishing returns:** Success rate < 20% and time > 15 min per optimization.

### Real-World Benchmarks

**Cumulative across sessions:**
- 23 proofs optimized
- ~108 lines removed
- ~34% token reduction average
- ~68% reduction per optimized proof
- 100% compilation success (with multi-candidate approach)

**Technique effectiveness:**
1. let+have+exact: 50% of all savings, 60-80% per instance
2. Smart ext: 50% reduction, no clarity loss
3. ext-simp chains: Saves ≥2 lines when natural
4. rwa: Instant wins, zero risk
5. ext+rfl → rfl: High value when works

### Related References

- [tactics-reference.md](tactics-reference.md) - Tactic catalog
- [domain-patterns.md](domain-patterns.md) - Domain-specific patterns
- [mathlib-style.md](mathlib-style.md) - Style conventions
