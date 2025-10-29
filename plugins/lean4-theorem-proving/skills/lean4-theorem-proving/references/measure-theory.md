# Measure Theory Reference

Deep patterns and pitfalls for measure theory and probability in Lean 4.

**When to use this reference:**
- Working with sub-σ-algebras and conditional expectation
- Hitting type class synthesis errors with measures
- Debugging "failed to synthesize instance" errors

---

## TL;DR - Essential Rules

When working with sub-σ-algebras and conditional expectation:

1. **Make ambient space explicit:** `{m₀ : MeasurableSpace Ω}` (never `‹_›`)
2. **Correct binder order:** All instance parameters first, THEN plain parameters
3. **Use `haveI`** to provide trimmed measure instances before calling mathlib
4. **Avoid instance pollution:** Pin ambient (`let m0 := ‹...›`), use `@` for ambient facts (see [instance-pollution.md](instance-pollution.md))
5. **Prefer set-integral projection:** Use `set_integral_condexp` instead of proving `μ[g|m] = g`
6. **Rewrite products to indicators:** `f * indicator` → `indicator f` avoids measurability issues
7. **Follow condExpWith pattern** for conditional expectation (see below)
8. **Copy-paste σ-algebra relations** from ready-to-use snippets (see Advanced Patterns)

---

## ❌ Common Anti-Patterns (DON'T)

**Avoid these - they cause subtle bugs:**

1. **❌ Don't use `‹_›` for ambient space**
   - Bug: Resolves to `m` instead of ambient, giving `hm : m ≤ m`
   - Fix: Explicit `{m₀ : MeasurableSpace Ω}` and `hm : m ≤ m₀`

2. **❌ Don't define sub-σ-algebras without pinning ambient first**
   - Bug: Instance pollution makes Lean pick local `mW` over ambient (even from outer scopes!)
   - Fix: Pin ambient (`let m0 := ‹...›`), use `@` for ambient facts, THEN define `let mW := ...`

3. **❌ Don't prove CE idempotence when you need set-integral equality**
   - Hard: Proving `μ[g|m] = g` a.e.
   - Easy: `set_integral_condexp` gives `∫_{s} μ[g|m] = ∫_{s} g` for s ∈ m

4. **❌ Don't force product measurability**
   - Fragile: `AEStronglyMeasurable (fun ω => f ω * g ω)`
   - Robust: Rewrite to `indicator` and use `Integrable.indicator`

---

## Essential Pattern: condExpWith

The canonical approach for conditional expectation with sub-σ-algebras:

```lean
lemma my_condexp_lemma
    {Ω : Type*} {m₀ : MeasurableSpace Ω}  -- ✅ Explicit ambient
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- ✅ Explicit relation
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ... μ[f|m] ... := by
  -- Provide instances explicitly:
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm

  -- Now CE and mathlib lemmas work
  ...
```

**Key elements:**
- `{m₀ : MeasurableSpace Ω}` - explicit ambient space
- `(hm : m ≤ m₀)` - explicit relation (not `m ≤ ‹_›`)
- `haveI` for trimmed measure instances before using CE

---

## Critical: Binder Order Matters

```lean
-- ❌ WRONG: m before instance parameters
lemma bad {Ω : Type*} [MeasurableSpace Ω]
    (m : MeasurableSpace Ω)  -- Plain param TOO EARLY
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : m ≤ ‹MeasurableSpace Ω›) : Result := by
  sorry  -- ‹MeasurableSpace Ω› resolves to m!

-- ✅ CORRECT: ALL instances first, THEN plain parameters
lemma good {Ω : Type*} [inst : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]  -- All instances
    (m : MeasurableSpace Ω)                    -- Plain param AFTER
    (hm : m ≤ inst) : Result := by
  sorry  -- Instance resolution works correctly
```

**Why:** When `m` appears before instance params, `‹MeasurableSpace Ω›` resolves to `m` instead of the ambient instance.

---

## Common Error Messages

**"typeclass instance problem is stuck"** → Add `haveI` for trimmed measure instances

**"has type @MeasurableSet Ω m B but expected @MeasurableSet Ω m₀ B"** → Check binder order

**"failed to synthesize instance IsFiniteMeasure ?m.104"** → Make ambient space explicit

---

## Advanced Patterns (Battle-Tested from Real Projects)

### 1. Avoid Instance Pollution (Pin Ambient + Use `@`)

**Problem:** When you define `let mW : MeasurableSpace Ω := ...`, Lean picks `mW` over the ambient instance. Even outer scope definitions cause pollution.

**⭐ PREFERRED: Pin ambient instance + use `@` for ambient facts**

```lean
theorem my_theorem ... := by
  -- ✅ STEP 0: PIN the ambient instance
  let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›

  -- ✅ STEP 1: ALL ambient work using m0 explicitly
  have hZ_m0 : @Measurable Ω β m0 _ Z := by simpa [m0] using hZ
  have hBpre : @MeasurableSet Ω m0 (Z ⁻¹' B) := hB.preimage hZ_m0
  have hCpre : @MeasurableSet Ω m0 (W ⁻¹' C) := hC.preimage hW_m0
  -- ... all other ambient facts

  -- ✅ STEP 2: NOW define sub-σ-algebras
  let mW  : MeasurableSpace Ω := MeasurableSpace.comap W m0
  let mZW : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (Z ω, W ω)) m0

  -- ✅ STEP 3: Work with sub-σ-algebras
  have hmW_le : mW ≤ m0 := hW.comap_le
```

**Why `@` is required:** Even if you do ambient work "first," outer scope pollution (e.g., `mW` defined in parent scope) makes Lean pick the wrong instance unless you explicitly force `m0` with `@` notation.

**⚡ Performance optimization:** If calling mathlib lemmas causes timeout errors, use the **three-tier strategy**:
```lean
-- Tier 2: m0 versions (for @ notation)
have hBpre_m0 : @MeasurableSet Ω m0 (Z ⁻¹' B) := hB.preimage hZ_m0

-- Tier 3: Ambient versions (for mathlib lemmas that infer instances)
have hBpre : MeasurableSet (Z ⁻¹' B) := by simpa [m0] using hBpre_m0

-- Use ambient version with mathlib:
have := integral_indicator hBpre ...  -- No expensive unification!
```

This eliminates timeout errors (500k+ heartbeats → normal) by avoiding expensive type unification.

**📚 For full details:** See [instance-pollution.md](instance-pollution.md) - explains scope pollution, 4 solutions, and performance optimization

---

### 2. Set-Integral Projection (Not Idempotence)

**Instead of proving** `μ[g|m] = g` a.e., **use this:**

```lean
-- For s ∈ m, Integrable g:
have : ∫ x in s, μ[g|m] x ∂μ = ∫ x in s, g x ∂μ :=
  set_integral_condexp (μ := μ) (m := m) (hm := hm) (hs := hs) (hf := hg)
```

**Wrapper to avoid parameter drift:**
```lean
lemma setIntegral_condExp_eq (μ : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ ‹_›)
    {s : Set Ω} (hs : MeasurableSet s) {g : Ω → ℝ} (hg : Integrable g μ) :
  ∫ x in s, μ[g|m] x ∂μ = ∫ x in s, g x ∂μ := by
  simpa using set_integral_condexp (μ := μ) (m := m) (hm := hm) (hs := hs) (hf := hg)
```

---

### 3. Product → Indicator (Avoid Product Measurability)

```lean
-- Rewrite product to indicator
have hMulAsInd : (fun ω => μ[f|mW] ω * gB ω) = (Z ⁻¹' B).indicator (μ[f|mW]) := by
  funext ω; by_cases hω : ω ∈ Z ⁻¹' B
  · simp [gB, hω, Set.indicator_of_mem, mul_one]
  · simp [gB, hω, Set.indicator_of_notMem, mul_zero]

-- Integrability without product measurability
have : Integrable (fun ω => μ[f|mW] ω * gB ω) μ := by
  simpa [hMulAsInd] using (integrable_condexp).indicator (hB.preimage hZ)
```

**Restricted integral:** `∫_{S} (Z⁻¹ B).indicator h = ∫_{S ∩ Z⁻¹ B} h`

---

### 4. Bounding CE Pointwise (NNReal Friction-Free)

```lean
-- From |f| ≤ R to ‖μ[f|m]‖ ≤ R a.e.
have hbdd_f : ∀ᵐ ω ∂μ, |f ω| ≤ (1 : ℝ) := …
have hbdd_f' : ∀ᵐ ω ∂μ, |f ω| ≤ ((1 : ℝ≥0) : ℝ) :=
  hbdd_f.mono (fun ω h => by simpa [NNReal.coe_one] using h)
have : ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ≤ (1 : ℝ) := by
  simpa [Real.norm_eq_abs, NNReal.coe_one] using
    ae_bdd_condExp_of_ae_bdd (μ := μ) (m := m) (R := (1 : ℝ≥0)) (f := f) hbdd_f'
```

---

### 5. σ-Algebra Relations (Ready-to-Paste)

```lean
-- σ(W) ≤ ambient
have hmW_le : mW ≤ ‹MeasurableSpace Ω› := hW.comap_le

-- σ(Z,W) ≤ ambient
have hmZW_le : mZW ≤ ‹MeasurableSpace Ω› := (hZ.prod_mk hW).comap_le

-- σ(W) ≤ σ(Z,W)
have hmW_le_mZW : mW ≤ mZW := (measurable_snd.comp (hZ.prod_mk hW)).comap_le

-- Measurability transport
have hsm_ce : StronglyMeasurable[mW] (μ[f|mW]) := stronglyMeasurable_condexp
have hsm_ceAmb : StronglyMeasurable (μ[f|mW]) := hsm_ce.mono hmW_le
```

---

### 6. Indicator-Integration Cookbook

```lean
-- Unrestricted: ∫ (Z⁻¹ B).indicator h = ∫ h * ((Z⁻¹ B).indicator 1)
-- Restricted:  ∫_{S} (Z⁻¹ B).indicator h = ∫_{S ∩ Z⁻¹ B} h

-- Rewrite pattern (avoids fragile lemma names):
have : (fun ω => h ω * indicator (Z⁻¹' B) 1 ω) = indicator (Z⁻¹' B) h := by
  funext ω; by_cases hω : ω ∈ Z⁻¹' B
  · simp [hω, Set.indicator_of_mem, mul_one]
  · simp [hω, Set.indicator_of_notMem, mul_zero]
```

---

## Mathlib Lemma Quick Reference

**Conditional expectation:**
- `integrable_condexp`, `stronglyMeasurable_condexp`, `aestronglyMeasurable_condexp`
- `set_integral_condexp` - set-integral projection (wrap as `setIntegral_condExp_eq`)

**A.E. boundedness:**
- `ae_bdd_condExp_of_ae_bdd` - bound CE from bound on f (NNReal version)

**Indicators:**
- `integral_indicator`, `Integrable.indicator`
- `Set.indicator_of_mem`, `Set.indicator_of_notMem`, `Set.indicator_indicator`

**Trimmed measures:**
- `isFiniteMeasure_trim`, `sigmaFinite_trim`

**Measurability lifting:**
- `MeasurableSet[m] s → MeasurableSet[m₀] s` via `hm _ hs_m` where `hm : m ≤ m₀`
