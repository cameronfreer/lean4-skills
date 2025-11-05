# Performance Optimization in Lean 4

Advanced patterns for preventing elaboration timeouts and type-checking performance issues.

**When to use this reference:**
- Hitting WHNF (Weak Head Normal Form) timeouts
- `isDefEq` timeouts during type-checking
- Elaboration taking 500k+ heartbeats even on simple goals
- Build times exploding on proofs involving polymorphic combinators

---

## Quick Reference

| Problem | Pattern | Expected Improvement |
|---------|---------|---------------------|
| WHNF timeout on `eLpNorm`/`MemLp` goals | Irreducible wrapper | 500k+ → <10k heartbeats |
| `isDefEq` timeout on complex functions | Pin type parameters | 5-10min → <30sec |
| Repeated measurability proofs | Pre-prove with wrapper | 28 lines → 8 lines |
| Elaboration timeouts in polymorphic code | `@[irreducible]` + explicit params | Build success vs timeout |

---

## Pattern 1: Irreducible Wrappers for Complex Functions

### Problem

When polymorphic goals like `eLpNorm` or `MemLp` contain complex function expressions, Lean's type checker tries to unfold them to solve polymorphic parameters (`p : ℝ≥0∞`, measure `μ`, typeclass instances). This causes WHNF and `isDefEq` timeouts.

**Example that times out:**
```lean
-- This hits 500k heartbeat limit during elaboration:
have : eLpNorm (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) 2 μ < ⊤ := by
  -- Lean unfolds blockAvg → (n:ℝ)⁻¹ * Finset.sum ...
  -- Then chases typeclass instances through every layer
  -- WHNF TIMEOUT!
```

**Root cause:** The expansion of `blockAvg`:
```lean
def blockAvg (f : α → ℝ) (X : ℕ → Ω → α) (m n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * (Finset.range n).sum (fun k => f (X (m + k) ω))
```

becomes deeply nested when substituted into `eLpNorm`, triggering expensive typeclass synthesis.

### Solution: Irreducible Wrapper Pattern

**Step 1: Create frozen wrapper**

```lean
/-- Frozen alias for `blockAvg f X 0 n`. Marked `@[irreducible]` so it
    will *not* unfold during type-checking. -/
@[irreducible]
def blockAvgFrozen {Ω : Type*} (f : ℝ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => blockAvg f X 0 n ω
```

**Key point:** `@[irreducible]` prevents definitional unfolding but allows `rw` for manual expansion.

**Step 2: Pre-prove helper lemmas (fast to elaborate)**

These lemmas are cheap because the wrapper is frozen:

```lean
lemma blockAvgFrozen_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → ℝ) (X : ℕ → Ω → ℝ)
    (hf : Measurable f) (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (blockAvgFrozen f X n) := by
  rw [blockAvgFrozen]  -- Manual unfold when needed
  exact blockAvg_measurable f X hf hX 0 n

lemma blockAvgFrozen_abs_le_one {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → ℝ) (X : ℕ → Ω → ℝ)
    (hf_bdd : ∀ x, |f x| ≤ 1) (n : ℕ) :
    ∀ ω, |blockAvgFrozen f X n ω| ≤ 1 := by
  intro ω
  rw [blockAvgFrozen]
  exact blockAvg_abs_le_one f X hf_bdd 0 n ω

lemma blockAvgFrozen_diff_memLp_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (X : ℕ → Ω → ℝ)
    (hf : Measurable f) (hX : ∀ i, Measurable (X i))
    (hf_bdd : ∀ x, |f x| ≤ 1) (n n' : ℕ) :
    MemLp (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) (2 : ℝ≥0∞) μ := by
  apply memLp_two_of_bounded (M := 2)
  · exact (blockAvgFrozen_measurable f X hf hX n).sub
      (blockAvgFrozen_measurable f X hf hX n')
  intro ω
  have hn  : |blockAvgFrozen f X n  ω| ≤ 1 := blockAvgFrozen_abs_le_one f X hf_bdd n  ω
  have hn' : |blockAvgFrozen f X n' ω| ≤ 1 := blockAvgFrozen_abs_le_one f X hf_bdd n' ω
  calc |blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω|
      ≤ |blockAvgFrozen f X n ω| + |blockAvgFrozen f X n' ω| := by
        simpa [sub_eq_add_neg] using abs_add (blockAvgFrozen f X n ω) (- blockAvgFrozen f X n' ω)
    _ ≤ 1 + 1 := add_le_add hn hn'
    _ = 2 := by norm_num
```

**Step 3: Use in timeout-prone code**

**Before (times out):**
```lean
have hblockAvg_memLp : ∀ n, n > 0 → MemLp (blockAvg f X 0 n) 2 μ := by
  intro n hn_pos
  apply memLp_two_of_bounded
  · -- Measurable: blockAvg is a finite sum of measurable functions
    show Measurable (fun ω => (n : ℝ)⁻¹ * (Finset.range n).sum (fun k => f (X (0 + k) ω)))
    exact Measurable.const_mul (Finset.measurable_sum _ fun k _ =>
      hf_meas.comp (hX_meas (0 + k))) _
  intro ω
  -- 20+ line calc proof
  -- WHNF TIMEOUT HERE AT 500k+ HEARTBEATS
```

**After (fast):**
```lean
have hblockAvg_memLp : ∀ n, n > 0 → MemLp (blockAvg f X 0 n) 2 μ := by
  intro n hn_pos
  have h_eq : blockAvg f X 0 n = blockAvgFrozen f X n := by rw [blockAvgFrozen]
  rw [h_eq]
  apply memLp_two_of_bounded (M := 1)
  · exact blockAvgFrozen_measurable f X hf_meas hX_meas n
  exact fun ω => blockAvgFrozen_abs_le_one f X hf_bdd n ω
```

---

## Supporting Techniques

### Technique 1: Always Pin Polymorphic Parameters

**Problem:** Type inference on polymorphic parameters triggers expensive searches.

```lean
-- ❌ BAD: Lean infers p and μ (expensive)
have : eLpNorm (blockAvg f X 0 n - blockAvg f X 0 n') 2 μ < ⊤

-- ✅ GOOD: Explicit parameters (cheap)
have : eLpNorm (fun ω => BA n ω - BA n' ω) (2 : ℝ≥0∞) (μ := μ) < ⊤
```

**Why:** Explicit `(p := (2 : ℝ≥0∞))` and `(μ := μ)` prevent type class search through function body.

### Technique 2: Use `rw` Not `simp` for Irreducible Definitions

**Problem:** `simp` cannot unfold `@[irreducible]` definitions.

```lean
-- ❌ BAD: simp can't unfold @[irreducible]
have : blockAvg f X 0 n = blockAvgFrozen f X n := by
  simp [blockAvgFrozen]  -- Error: simp made no progress

-- ✅ GOOD: rw explicitly unfolds
have : blockAvg f X 0 n = blockAvgFrozen f X n := by
  rw [blockAvgFrozen]
```

**Why:** `rw` uses the defining equation directly; `simp` respects `@[irreducible]` attribute.

### Technique 3: Pre-prove Facts, Don't Recompute

**Problem:** Reproving the same fact triggers expensive elaboration each time.

```lean
-- ❌ BAD: Recompute MemLp every time (expensive)
intro n n'
have : MemLp (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) 2 μ := by
  apply memLp_two_of_bounded
  · -- 10 lines proving measurability
  intro ω
  -- 10 lines proving boundedness

-- ✅ GOOD: One precomputed lemma (cheap)
lemma blockAvgFrozen_diff_memLp_two ... : MemLp ... := by
  -- Proof once (elaborates fast due to irreducible wrapper)

-- Usage:
intro n n'
exact blockAvgFrozen_diff_memLp_two f X hf hX hf_bdd n n'
```

**Benefit:** One slow elaboration → many fast reuses.

### Technique 4: Use Let-Bindings for Complex Terms

**Problem:** Lean re-elaborates complex function expressions multiple times.

```lean
-- ❌ BAD: Lean re-elaborates the function multiple times
have hn  : eLpNorm (blockAvgFrozen f X n - blockAvgFrozen f X n') 2 μ < ⊤
have hn' : MemLp (blockAvgFrozen f X n - blockAvgFrozen f X n') 2 μ

-- ✅ GOOD: Bind once, reuse
let diff := fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω
have hn  : eLpNorm diff (2 : ℝ≥0∞) μ < ⊤
have hn' : MemLp diff (2 : ℝ≥0∞) μ
```

**Why:** `let` creates a single binding that's reused definitionally.

---

## When to Use This Pattern

Apply irreducible wrappers when you see:

1. **WHNF timeouts** in goals containing `eLpNorm`, `MemLp`, or other polymorphic combinators
2. **`isDefEq` timeouts** during type-checking of complex function expressions
3. **Repeated expensive computations** of measurability, boundedness, or integrability
4. **Elaboration heartbeat warnings** (>100k heartbeats) on seemingly simple goals
5. **Build timeouts** that disappear when you `sorry` specific proofs

**Common polymorphic culprits:**
- `eLpNorm`, `MemLp`, `snorm` (Lp spaces)
- `Integrable`, `AEStronglyMeasurable` (integration)
- `ContinuousOn`, `UniformContinuousOn` (topology)
- Complex dependent type combinators

---

## What NOT to Do

**❌ Don't mark helper lemmas as irreducible** - only the main wrapper:
```lean
-- ❌ WRONG
@[irreducible]
lemma blockAvgFrozen_measurable ... := ...

-- ✅ CORRECT
lemma blockAvgFrozen_measurable ... := ...  -- Normal lemma
```

**❌ Don't use `simp` on irreducible defs** - use `rw` instead:
```lean
-- ❌ WRONG
simp [blockAvgFrozen]  -- Makes no progress

-- ✅ CORRECT
rw [blockAvgFrozen]
```

**❌ Don't skip pinning type parameters** - always explicit:
```lean
-- ❌ WRONG
eLpNorm diff 2 μ  -- Type inference cost

-- ✅ CORRECT
eLpNorm diff (2 : ℝ≥0∞) (μ := μ)
```

**❌ Don't put irreducible wrapper in a section with `variable`** - use explicit params:
```lean
-- ❌ WRONG
section
variable {μ : Measure Ω}
@[irreducible]
def wrapper := ...  -- May cause issues
end

-- ✅ CORRECT
@[irreducible]
def wrapper {Ω : Type*} {μ : Measure Ω} := ...  -- Explicit params
```

---

## Expected Results

When this pattern is applied correctly:

| Metric | Before | After |
|--------|--------|-------|
| **Elaboration heartbeats** | 500k+ (timeout) | <10k (fast) |
| **Build time** | 5-10min (timeout) | <30sec (success) |
| **Proof lines** | 28 lines inline | 8 lines (reusing lemmas) |
| **Maintainability** | Low (repeated logic) | High (reusable lemmas) |

---

## Analogy to Other Languages

This pattern is the Lean 4 equivalent of:
- **C++:** `extern template` (preventing unwanted template instantiation)
- **Haskell:** `NOINLINE` pragma (preventing unwanted inlining)
- **Rust:** `#[inline(never)]` (controlling inlining for compile times)

The goal is the same: **control compilation cost by preventing unwanted expansion**.

---

## Related Patterns

- **[measure-theory.md](measure-theory.md)** - Measure theory specific type class patterns
- **[compilation-errors.md](compilation-errors.md)** - Fixing timeout errors (Error 2)
- **[compiler-guided-repair.md](compiler-guided-repair.md)** - Using compiler feedback to fix issues

---

## Advanced: When Irreducible Isn't Enough

If `@[irreducible]` still causes timeouts, consider:

1. **Split into smaller wrappers:** Multiple frozen pieces instead of one large one
2. **Use `abbrev` for simple aliases:** When you want transparency but controlled unfolding
3. **Provide explicit type annotations:** Help Lean avoid searches
4. **Reduce polymorphism:** Sometimes monomorphic wrappers are faster

**Example of splitting:**
```lean
-- Instead of one complex frozen function:
@[irreducible]
def complexFrozen := fun ω => f (g (h (X ω)))

-- Split into parts:
@[irreducible] def frozenH (X : Ω → α) : Ω → β := fun ω => h (X ω)
@[irreducible] def frozenG (Y : Ω → β) : Ω → γ := fun ω => g (Y ω)
@[irreducible] def frozenF (Z : Ω → γ) : Ω → ℝ := fun ω => f (Z ω)

-- Compose:
def complexFrozen := frozenF (frozenG (frozenH X))
```

---

## Debugging Elaboration Performance

**See elaboration heartbeats:**
```lean
set_option trace.profiler true in
theorem my_theorem := by
  -- Shows heartbeat count for each tactic
```

**Find expensive `isDefEq` checks:**
```lean
set_option trace.Meta.isDefEq true in
theorem my_theorem := by
  -- Shows all definitional equality checks
```

**Increase limit temporarily (debugging only):**
```lean
set_option maxHeartbeats 1000000 in  -- 10x normal
theorem my_theorem := by
  -- This is a WORKAROUND not a fix!
  -- Use irreducible wrappers instead
```

**Remember:** Increasing `maxHeartbeats` is a **band-aid**. The real fix is preventing unwanted unfolding with `@[irreducible]`.
