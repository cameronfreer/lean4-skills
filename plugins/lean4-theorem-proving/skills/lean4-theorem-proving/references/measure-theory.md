# Measure Theory Reference

Deep patterns and pitfalls for measure theory and probability in Lean 4.

**When to use this reference:**
- Working with sub-σ-algebras and conditional expectation
- Hitting type class synthesis errors with measures
- Managing measurable space structures and trimmed measures
- Debugging "failed to synthesize instance" errors in measure theory

## Type Class Instance Management for Sub-σ-Algebras

### Critical: Binder Order Matters

When working with a sub-σ-algebra `m ≤ m₀`, the parameter order in function signatures is crucial:

```lean
-- ❌ WRONG: m before instance parameters causes instance resolution issues
lemma my_lemma
    {Ω : Type*} [MeasurableSpace Ω]  -- Instance
    (m : MeasurableSpace Ω)            -- Plain parameter BEFORE instance params
    {μ : Measure Ω} [IsProbabilityMeasure μ]  -- More instances
    (hm : m ≤ ‹MeasurableSpace Ω›) :
    Result := by
  -- Lean chooses m instead of ambient instance!
  sorry

-- ✅ CORRECT: ALL instance parameters first, THEN plain parameters
lemma my_lemma
    {Ω : Type*} [inst : MeasurableSpace Ω]  -- Named instance
    {μ : Measure Ω} [IsProbabilityMeasure μ]  -- All instances first
    (m : MeasurableSpace Ω)  -- Plain parameter AFTER all instances
    (hm : m ≤ inst) :        -- Reference named instance
    Result := by
  -- Now instance resolution works correctly
  sorry
```

**Why this matters:**
- When `m` appears before instance parameters, `‹MeasurableSpace Ω›` resolves to `m` instead of the ambient instance
- This causes type class synthesis to choose the wrong structure
- Results in errors like "has type @MeasurableSet Ω m B but expected @MeasurableSet Ω inst B"

### Pitfall: Anonymous Instance Notation `‹_›` with Sub-σ-Algebras

When working with sub-σ-algebras, **never use `‹_›` for the ambient space**—it resolves incorrectly:

```lean
-- ❌ WRONG: Anonymous instance resolves to m instead of ambient space!
lemma bad_example [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ ‹_›)  -- ‹_› becomes m, so hm : m ≤ m
    : Result := by
  sorry  -- Type class errors: "failed to synthesize instance"

-- ✅ CORRECT: Make ambient space explicit
lemma good_example {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- Now hm : m ≤ m₀ is meaningful
    : Result := by
  -- Provide instances explicitly before calling mathlib
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
  sorry
```

**The bug:** `hm : m ≤ ‹_›` gave you `hm : m ≤ m` because Lean picked the most recent `MeasurableSpace Ω` in scope (which was `m` itself).

**The fix:** Explicit `m₀` parameter gives meaningful `hm : m ≤ m₀` and avoids instance resolution failures.

## The condExpWith Pattern for Conditional Expectation

### The Problem It Solves

When working with conditional expectation on sub-σ-algebras, you often have:
- An ambient measurable space structure on Ω
- A sub-σ-algebra `m` that's smaller: `m ≤ (ambient structure)`
- A measure `μ` on the ambient space
- Need to compute `μ[f|m]` (conditional expectation with respect to `m`)

**Challenge:** Lean needs to know about both measurable space structures simultaneously, and type class inference can get confused.

### The Anti-Pattern (What NOT to do)

```lean
lemma my_condexp_lemma
    {m : MeasurableSpace Ω} (hm : m ≤ ‹_›)  -- ❌ WRONG!
    {f : Ω → ℝ} ... :
    μ[f|m] = ... := by
  ...
```

**Problem:** The anonymous instance notation `‹_›` gets resolved incorrectly. Lean resolves it to `m` itself, giving you `hm : m ≤ m`, which is useless! This causes type class synthesis failures like:
```
error: typeclass instance problem is stuck
  IsFiniteMeasure ?m.104
```

### The condExpWith Pattern (Correct Approach)

The canonical solution from real codebases:

```lean
def condExpWith {Ω : Type*} {m₀ : MeasurableSpace Ω}  -- ✅ Explicit ambient space
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- ✅ Explicit sub-algebra relation
    (f : Ω → ℝ) : Ω → ℝ := by
  -- Inside the function body, provide instances explicitly:
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm

  exact condExp m μ f  -- Now type class resolution works!
```

### Key Principles

1. **Make the ambient measurable space explicit:**
   ```lean
   {m₀ : MeasurableSpace Ω}  -- Name it explicitly
   ```

2. **Use explicit inequality:**
   ```lean
   (hm : m ≤ m₀)  -- Not hm : m ≤ ‹_›
   ```

3. **Provide trimmed measure instances with `haveI`:**
   ```lean
   haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
   haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
   ```

### Why It Works

- **Explicit `m₀`:** Lean now knows there are TWO distinct measurable spaces in play
- **`hm : m ≤ m₀`:** The relationship is unambiguous
- **`haveI`:** Adds instances to the local type class context before calling mathlib lemmas
- **Trimmed measure:** Many conditional expectation lemmas need instances on `μ.trim hm`, not just `μ`

### Real Example: condExp_mul_pullout

**Before (broken):**
```lean
lemma condExp_mul_pullout
    {m : MeasurableSpace Ω} (hm : m ≤ ‹_›)  -- ❌
    ... := by
  exact condExp_stronglyMeasurable_mul_of_bound hm ...
  -- Error: IsFiniteMeasure ?m.104
```

**After (fixed):**
```lean
lemma condExp_mul_pullout {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- ✅
    ... := by
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm

  exact condExp_stronglyMeasurable_mul_of_bound hm ...
  -- ✅ Works!
```

## Explicit Instance Declarations

When Lean can't synthesize required instances automatically, provide them explicitly:

```lean
haveI : IsFiniteMeasure μ := inferInstance
haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
-- Now conditional expectation works:
μ[f | m]
```

## Measurability Lifting Between Structures

When you have a set measurable in the sub-algebra, lift to ambient space:

```lean
-- When you have s measurable in m, lift to ambient m₀
have hs_m : MeasurableSet[m] s := ...
have hs_m₀ : MeasurableSet[m₀] s := hm _ hs_m  -- hm : m ≤ m₀
```

## Quick Reference

**When working with sub-σ-algebras in Lean 4:**
- ✅ DO: Make ambient space explicit `{m₀ : MeasurableSpace Ω}`
- ✅ DO: Use `haveI` for trimmed measure instances
- ✅ DO: Put all instance parameters before plain parameters
- ❌ DON'T: Use `‹_›` for the ambient measurable space
- ❌ DON'T: Put plain measurable space parameters before instance parameters
- 📚 PATTERN: Use the condExpWith pattern as template for conditional expectation work

## Common Error Messages

**"typeclass instance problem is stuck"**
→ Provide instances explicitly with `haveI` before calling mathlib

**"has type @MeasurableSet Ω m B but expected @MeasurableSet Ω m₀ B"**
→ Check binder order: all instance parameters must come before plain parameters

**"failed to synthesize instance IsFiniteMeasure ?m.104"**
→ Make ambient space explicit and provide trimmed measure instances

## ❌ DON'T USE THIS HERE (Common Anti-Patterns)

**These patterns cause subtle bugs. Avoid them:**

1. **❌ Don't `letI` the whole goal to a sub-σ-algebra instance**
   - Problem: Instance drift makes Lean treat Ω's instance as σ(W) unexpectedly
   - Fix: Freeze ambient with `let m0 : MeasurableSpace Ω := ‹_›` and use `@` or local `haveI`

2. **❌ Don't prove idempotence of CE when you only need set-integral equality**
   - Problem: Proving `μ[g|m] = g` a.e. is harder than needed
   - Fix: Use `set_integral_condexp` for s ∈ m instead

3. **❌ Don't force measurability of products directly**
   - Problem: `AEStronglyMeasurable (fun ω => f ω * g ω)` synthesis is fragile
   - Fix: Rewrite to indicator form and use `Integrable.indicator`

---

## Advanced Patterns from Real Projects

### 1. Freeze the Ambient σ-Algebra (Stop Instance Drift)

**Problem:** `letI` or implicit inference can make Lean treat Ω's instance as σ(W) or σ(Z,W) unexpectedly, causing type mismatches.

**Solution:** Freeze the ambient measurable space once at the start:

```lean
-- Freeze the ambient measurable space once
let m0 : MeasurableSpace Ω := ‹_›

-- Build sub-σ-algebras explicitly (NO letI)
let mW  : MeasurableSpace Ω := MeasurableSpace.comap W  m0
let mZW : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (Z ω, W ω)) m0

-- Ambient measurability pinned to m0
have hZ_amb : @Measurable Ω m0 _ Z := by simpa using hZ
have hBpre_amb : @MeasurableSet Ω m0 (Z ⁻¹' B) := hB.preimage hZ_amb
```

**When a lemma must use the ambient instance,** force it with `@… Ω m0 …` or a tiny local block:

```lean
have hBpre_amb : MeasurableSet (Z ⁻¹' B) := by
  haveI : MeasurableSpace Ω := m0
  simpa using hB.preimage hZ
```

---

### 2. Always Prefer Set-Integral Projection Over CE Idempotence

**Instead of proving** `μ[g|m] = g` a.e. (hard), **do this:**

```lean
-- For s ∈ m, Integrable g:
have hset : ∫ x in s, μ[g|m] x ∂μ = ∫ x in s, g x ∂μ :=
  set_integral_condexp (μ := μ) (m := m) (hm := hm_le) (hs := hs) (hf := hg)
```

**Recommended wrapper** to avoid mathlib name/order drift:

```lean
lemma setIntegral_condExp_eq
    (μ : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ ‹_›)
    {s : Set Ω} (hs : MeasurableSet s) {g : Ω → ℝ} (hg : Integrable g μ) :
  ∫ x in s, μ[g|m] x ∂μ = ∫ x in s, g x ∂μ := by
  simpa using (set_integral_condexp (μ := μ) (m := m) (hm := hm) (hs := hs) (hf := hg))
```

---

### 3. Product vs Indicator: Rewrite, Don't Fight Measurability

**Pattern:** When you have `f * indicator`, rewrite to `indicator f` and use `Integrable.indicator` instead of proving product measurability.

**Canonical pointwise identity:**

```lean
-- gB := (Z ⁻¹' B).indicator (fun _ => (1 : ℝ))
have hMulAsInd :
  (fun ω => μ[f|mW] ω * gB ω) = (Z ⁻¹' B).indicator (μ[f|mW]) := by
  funext ω; by_cases hω : ω ∈ Z ⁻¹' B
  · simp [gB, hω, Set.indicator_of_mem, mul_one]
  · simp [gB, hω, Set.indicator_of_notMem, mul_zero]

-- Integrability of the product without touching product measurability:
have hIntProd : Integrable (fun ω => μ[f|mW] ω * gB ω) μ := by
  have hIntCE : Integrable (μ[f|mW]) μ := integrable_condexp
  have hBpre_amb : MeasurableSet (Z ⁻¹' B) := hB.preimage hZ
  simpa [hMulAsInd] using hIntCE.indicator hBpre_amb
```

**Restricted integral identity:**

```
∫_{W⁻¹ C} (μ[f|mW] * gB) = ∫_{W⁻¹ C} (Z⁻¹ B).indicator (μ[f|mW])
                          = ∫_{W⁻¹ C ∩ Z⁻¹ B} μ[f|mW]
```

---

### 4. Bounding CE Pointwise: Use the A.E. Boundedness Lemma

**Pattern:** Go from `|f| ≤ 1` to `|μ[f|m]| ≤ 1` a.e. with friction-free NNReal casting:

```lean
-- Start with a real bound
have hbdd_f : ∀ᵐ ω ∂μ, |f ω| ≤ (1 : ℝ) := …

-- Coerce inside the event to avoid LE synthesis errors
have hbdd_f' : ∀ᵐ ω ∂μ, |f ω| ≤ ((1 : ℝ≥0) : ℝ) :=
  hbdd_f.mono (by intro ω h; simpa [NNReal.coe_one] using h)

-- Then apply the lemma and switch abs↔norm
have hCE_le_one : ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ≤ (1 : ℝ) := by
  simpa [Real.norm_eq_abs, NNReal.coe_one] using
    (MeasureTheory.ae_bdd_condExp_of_ae_bdd
      (μ := μ) (m := m) (R := (1 : ℝ≥0)) (f := f) hbdd_f')
```

**Recommended wrapper** with a real bound `R : ℝ, 0 ≤ R`:

```lean
lemma ae_bdd_condExp_real
    (μ : Measure Ω) (m : MeasurableSpace Ω)
    {f : Ω → ℝ} {R : ℝ} (hR : 0 ≤ R) (hbdd : ∀ᵐ ω ∂μ, |f ω| ≤ R) :
  ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ≤ R := by
  have hR_nn : R = ((⟨R, hR⟩ : ℝ≥0) : ℝ) := by simp
  have hbdd' : ∀ᵐ ω ∂μ, |f ω| ≤ ((⟨R, hR⟩ : ℝ≥0) : ℝ) :=
    hbdd.mono (by intro ω h; simpa [hR_nn] using h)
  simpa [Real.norm_eq_abs, hR_nn] using
    (MeasureTheory.ae_bdd_condExp_of_ae_bdd
      (μ := μ) (m := m) (R := ⟨R, hR⟩) (f := f) hbdd')
```

---

### 5. σ-Algebra Relations: Ready-to-Paste Facts

**Copy these whenever you need σ-algebra relations:**

```lean
-- σ(W) ≤ ambient
have hmW_le  : mW ≤ ‹MeasurableSpace Ω› := hW.comap_le

-- σ(Z,W) ≤ ambient
have hmZW_le : mZW ≤ ‹MeasurableSpace Ω› := (hZ.prod_mk hW).comap_le

-- σ(W) ≤ σ(Z,W)
have hmW_le_mZW : mW ≤ mZW :=
  (measurable_snd.comp (hZ.prod_mk hW)).comap_le

-- Measurability transport
have hsm_ce    : StronglyMeasurable[mW] (μ[f|mW]) := stronglyMeasurable_condexp
have hsm_ceAmb : StronglyMeasurable (μ[f|mW])     := hsm_ce.mono hmW_le
have haesm_ce  : AEStronglyMeasurable (μ[f|mW]) μ := hsm_ceAmb.aestronglyMeasurable
```

---

### 6. Indicator-Integration Cookbook (Direction Matters)

**Two rewrites that always work:**

```lean
-- Unrestricted integral:
∫ (Z⁻¹ B).indicator h = ∫ h * ((Z⁻¹ B).indicator (fun _ => (1:ℝ)))

-- Restricted integral by S:
∫_{S} (Z⁻¹ B).indicator h = ∫_{S ∩ Z⁻¹ B} h
```

**Example with `by_cases` + `simp`** to avoid fragile lemma names:

```lean
have hRewrite : (fun ω => h ω * indicator (Z⁻¹' B) (fun _ => (1:ℝ)) ω)
              = indicator (Z⁻¹' B) h := by
  funext ω
  by_cases hω : ω ∈ Z⁻¹' B
  · simp [hω, Set.indicator_of_mem, mul_one]
  · simp [hω, Set.indicator_of_notMem, mul_zero]

-- Then use integral_congr_ae or rw [hRewrite]
```

**Key lemmas for indicator manipulation:**
- `integral_indicator` - convert indicator to restricted integral
- `Integrable.indicator` - integrability from measurability + integrability
- `Set.indicator_of_mem`, `Set.indicator_of_notMem` - pointwise simplification
- `Set.indicator_indicator` - nested indicators (S ∩ T pattern)

---

## TL;DR

When working with sub-σ-algebras and conditional expectation:
1. **Make ambient space explicit:** `{m₀ : MeasurableSpace Ω}`
2. **Never use `‹_›`** for ambient space (it resolves incorrectly)
3. **Use `haveI`** to provide trimmed measure instances
4. **Correct binder order:** All instances first, then plain parameters
5. **Follow condExpWith pattern** for conditional expectation work
6. **Freeze ambient instance** with `let m0 : MeasurableSpace Ω := ‹_›`
7. **Prefer set-integral projection** over CE idempotence proofs
8. **Rewrite products to indicators** instead of proving product measurability

This prevents type class inference failures and is essential for any serious work with conditional expectation in Lean 4.

---

## Mathlib Lemma Quick Reference

**Conditional expectation basics:**
- `integrable_condexp` - CE is integrable
- `stronglyMeasurable_condexp` - CE is strongly measurable in sub-σ-algebra
- `aestronglyMeasurable_condexp` - CE is a.e. strongly measurable

**Set-integral projection:**
- `set_integral_condexp` - `∫_{s} μ[f|m] = ∫_{s} f` for s ∈ m
- Wrap as `setIntegral_condExp_eq` to avoid parameter order changes

**A.E. boundedness:**
- `MeasureTheory.ae_bdd_condExp_of_ae_bdd` - bound CE from bound on f (NNReal version)
- Wrap as `ae_bdd_condExp_real` for real bounds

**Indicator helpers:**
- `integral_indicator` - `∫ s.indicator f = ∫_{s} f`
- `Integrable.indicator` - integrability of indicator functions
- `Set.indicator_of_mem` - `indicator s f x = f x` when `x ∈ s`
- `Set.indicator_of_notMem` - `indicator s f x = 0` when `x ∉ s`
- `Set.indicator_indicator` - nested indicators collapse to intersection

**Trimmed measures:**
- `isFiniteMeasure_trim` - transfer finite measure to trimmed measure
- `sigmaFinite_trim` - transfer σ-finiteness to trimmed measure
