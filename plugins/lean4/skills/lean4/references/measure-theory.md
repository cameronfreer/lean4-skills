# Measure Theory Reference

Deep patterns and pitfalls for measure theory and probability in Lean 4.

**When to use this reference:**
- Working with sub-σ-algebras and conditional expectation
- Hitting type class synthesis errors with measures
- Debugging "failed to synthesize instance" errors
- Choosing between scalar `μ[·|m]` and kernel `condExpKernel` forms
- Understanding Kernel vs Measure API distinctions
- Using Measure.map for pushforward operations
- Discovering measure theory lemmas with lean_leanfinder

---

## TL;DR - Essential Rules

When working with sub-σ-algebras and conditional expectation:

1. **Make ambient space explicit:** `{m₀ : MeasurableSpace Ω}` (never `‹_›`)
2. **Correct binder order:** All instance parameters first, THEN plain parameters
3. **Check whether synthesis already succeeds** before adding local instances: given `[IsFiniteMeasure μ]`, `IsFiniteMeasure (μ.trim hm)` is a Mathlib instance and `SigmaFinite (μ.trim hm)` follows from it. `[SigmaFinite μ]` alone is **not** enough (`sigmaFinite_trim_bot_iff`; synthesis fails). If you still freeze one, use plain `have` (it registers the instance; `haveI` only inlines, which is irrelevant in a proof)
4. **Avoid instance pollution:** name the ambient instance in the declaration (`[mΩ : MeasurableSpace Ω]`) and state ambient facts against it (`@`, `MeasurableSet[mΩ]`); `let m0 := ‹…›` is only the recovery when you cannot change the signature (see [instance-pollution.md](instance-pollution.md))
5. **Prefer set-integral projection:** Use `setIntegral_condExp` instead of proving `μ[g|m] = g`
6. **Rewrite products to indicators:** `f * indicator` → `indicator f` avoids measurability issues
7. **Follow condExpWith pattern** for conditional expectation (see below)
8. **Copy-paste σ-algebra relations** from ready-to-use snippets (see Advanced Patterns)

---

## Essential Lemmas (Start Here)

| Task | Lemma | Notes |
|------|-------|-------|
| CE integrability | `integrable_condExp` | Always available |
| Project CE to set integral | `setIntegral_condExp` | Use this, not a.e. equality |
| Trim measure instance | `inferInstance` (via the `isFiniteMeasure_trim` instance + `IsFiniteMeasure.toSigmaFinite`) | Needs `[IsFiniteMeasure μ]`; optional freeze: `have : SigmaFinite (μ.trim hm) := inferInstance` |
| Preimage measurability | `measurableSet_preimage hf hs` | Function syntax |
| Lift sub-σ-algebra set | `hm _ hs_m` where `hm : m ≤ m₀` | Direct application |

---

## ⚡ CRITICAL: Instance Pollution Prevention

**If you're working with sub-σ-algebras, READ THIS FIRST:**

**📚 [instance-pollution.md](instance-pollution.md)** - Complete guide to preventing instance pollution bugs

**Why critical:**
- **Subtle bugs:** Lean picks wrong `MeasurableSpace` instance (even from outer scopes!)
- **Timeout errors:** Can cause 500k+ heartbeat explosions in type unification
- **Hard to debug:** Synthesized vs inferred type mismatches are cryptic

**Quick fix:** name the ambient instance in the declaration, state the ambient facts against it, THEN define sub-σ-algebras. `MeasurableSpace.comap W m` pulls the **codomain** structure `m` back along `W`, so for `W : Ω → γ` the argument is the `MeasurableSpace γ`, never the ambient `MeasurableSpace Ω`:
```lean
lemma foo {Ω γ : Type*} [mΩ : MeasurableSpace Ω] [mγ : MeasurableSpace γ]
    (W : Ω → γ) (hW : Measurable W) ... := by
  -- ambient facts first, against the named instance
  have hpre : MeasurableSet[mΩ] (W ⁻¹' C) := hC.preimage hW
  -- now the sub-σ-algebra: σ(W) = comap of the CODOMAIN structure
  let mW : MeasurableSpace Ω := MeasurableSpace.comap W mγ
  have hmW_le : mW ≤ mΩ := hW.comap_le
```
If you cannot change the signature, `let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›` recovers a name for the ambient instance — `‹…›` picks the currently selected local instance, so it must be the first line, before any other `MeasurableSpace Ω` local exists.

---

## ❌ Common Anti-Patterns (DON'T)

**Avoid these - they cause subtle bugs:**

1. **❌ Don't use `‹_›` for ambient space**
   - Bug: Resolves to `m` instead of ambient, giving `hm : m ≤ m`
   - Fix: Explicit `{m₀ : MeasurableSpace Ω}` and `hm : m ≤ m₀`

2. **❌ Don't define sub-σ-algebras without pinning ambient first**
   - Bug: Instance pollution makes Lean pick local `mW` over ambient (even from outer scopes!)
   - Fix: name the ambient instance in the declaration (`[mΩ : MeasurableSpace Ω]`), state ambient facts against it (`@`, `MeasurableSet[mΩ]`), THEN define `let mW := MeasurableSpace.comap W mγ` (`let m0 := ‹...›` only when the signature is not yours to change)

3. **❌ Don't prove CE idempotence when you need set-integral equality**
   - Hard: Proving `μ[g|m] = g` a.e.
   - Easy: `setIntegral_condExp` gives `∫_{s} μ[g|m] = ∫_{s} g` for s ∈ m

4. **❌ Don't force product measurability**
   - Fragile: `AEStronglyMeasurable (fun ω ↦ f ω * g ω)`
   - Robust: Rewrite to `indicator` and use `Integrable.indicator`

5. **❌ Don't state ambient facts after introducing a `MeasurableSpace Ω` local without naming the instance**
   - Bug: a bare `MeasurableSet`/`StronglyMeasurable` is elaborated against whichever `MeasurableSpace Ω` local is newest at that point; facts elaborated before and after a new class-typed local then disagree (`inst✝⁶ vs mW`)
   - Fix: name the ambient instance and write ambient facts against it (`MeasurableSet[mΩ]`, `@`); or inline the comaps so no intermediate class-typed local exists
   - Details: See "The `inferInstance` Drift Trap" pattern below

---

## Essential Pattern: condExpWith

The canonical approach for conditional expectation with sub-σ-algebras:

```lean
lemma my_condExp_lemma
    {Ω : Type*} {m₀ : MeasurableSpace Ω}  -- ✅ Explicit ambient
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- ✅ Explicit relation
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ... μ[f|m] ... := by
  -- Check whether synthesis already succeeds before adding local instances:
  -- `[IsFiniteMeasure μ]` is in scope, `IsFiniteMeasure (μ.trim hm)` is a Mathlib
  -- instance (`isFiniteMeasure_trim`), and `SigmaFinite (μ.trim hm)` follows from
  -- it (`IsFiniteMeasure.toSigmaFinite`). Only the σ-finiteness freeze is worth
  -- keeping, and plain `have` registers it (`haveI` would only inline):
  have : SigmaFinite (μ.trim hm) := inferInstance

  -- Now CE and mathlib lemmas work
  ...
```

**Key elements:**
- `{m₀ : MeasurableSpace Ω}` - explicit ambient space
- `(hm : m ≤ m₀)` - explicit relation (not `m ≤ ‹_›`)
- Check synthesis first; with `[IsFiniteMeasure μ]` in scope, freeze `SigmaFinite (μ.trim hm)` with plain `have` only if it helps (`[SigmaFinite μ]` alone does not synthesize it)

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

**"typeclass instance problem is stuck"** → Not a missing instance: the class's *arguments* still contain unresolved metavariables (`IsFiniteMeasure ?μ`, `SigmaFinite (?μ.trim ?hm)`), so search cannot start. Pin them — annotate the expected type, or pass the implicits (`(μ := μ) (m := m)`, `(hm := hm)`) — and synthesis usually succeeds on its own. Freeze with plain `have : SigmaFinite (μ.trim hm) := inferInstance` only if it then still helps.

**"has type @MeasurableSet Ω m B but expected @MeasurableSet Ω m₀ B"** → Check binder order

**"failed to synthesize instance IsFiniteMeasure ?m.104"** → Make ambient space explicit

---

## API Distinctions and Conversions

**Key measure theory API patterns that cause compiler errors.**

### AEMeasurable vs AEStronglyMeasurable

**Problem:** Integral operations require `AEStronglyMeasurable`, but you have `AEMeasurable`.

**Error message:** `expected AEStronglyMeasurable f μ but got AEMeasurable f μ`

**Solution:** For real-valued functions with second-countable topology, use `.aestronglyMeasurable`:

```lean
-- You have:
theorem foo (hf : AEMeasurable f μ) : ... := by
  have : AEStronglyMeasurable f μ := hf.aestronglyMeasurable  -- ✓ Conversion
  ...
```

**When this works:**
- Function returns `ℝ`, `ℂ`, or any second-countable topological space
- Common for integration, Lp spaces, conditional expectation

**Rule of thumb:** If integral API complains about `AEStronglyMeasurable`, check if your type has second-countable topology and use `.aestronglyMeasurable` converter.

### Set Integrals vs Full Integrals

**Problem:** Set integral lemmas have different names than full integral lemmas.

**Error pattern:** Trying to use `integral_map` for `∫ x in s, f x ∂μ`

**Solution:** Search for `setIntegral_*` variants:

```lean
-- ❌ Wrong: Full integral API for set integral
have := integral_map  -- Doesn't apply to ∫ x in s, ...

-- ✅ Correct: Set integral API
have := setIntegral_map  -- ✓ Works for ∫ x in s, f x ∂μ
```

**Pattern:** When working with `∫ x in s, f x ∂μ`, use LeanFinder with:
- "setIntegral change of variables"
- "setIntegral map pushforward"
- NOT just "integral ..." (finds full integral APIs)

**Common set integral APIs:**
```lean
setIntegral_map       -- Change of variables for set integrals
setIntegral_const     -- Integral of constant over set
setIntegral_congr_ae  -- a.e. equality for set integrals
```

### Synthesized vs Inferred Type Mismatches

**Problem:** Error says "synthesized: m, inferred: inst✝⁴" with `MeasurableSpace`.

**Meaning:** Sub-σ-algebra annotation mismatch - elaborator resolves to different measurable space structures.

**Example error:**
```
type mismatch
  synthesized type:  @MeasurableSet Ω m s
  inferred type:     @MeasurableSet Ω inst✝⁴ s
```

**This indicates:** You have multiple `MeasurableSpace Ω` instances in scope and Lean picked the wrong one.

**Solutions:**
1. **Pin ambient and use `@`** (see Pattern 1 below: Avoid Instance Pollution)
2. **Check binder order** - instances before plain parameters
3. **Consider using `sorry` and moving on** - fighting the elaborator rarely wins

**When to give up:** If you've tried pinning ambient and fixing binder order but still get synthesized/inferred mismatches, this is often a deep elaboration issue. Document with `sorry` and note the issue - coming back later with fresh eyes often helps.

---

## Advanced Patterns (Battle-Tested from Real Projects)

### 1. Avoid Instance Pollution (Name the Ambient Instance + Use `@`)

**Problem:** When you define `let mW : MeasurableSpace Ω := ...`, a bare `MeasurableSet`/`StronglyMeasurable` elaborated afterwards resolves to `mW`, not the ambient instance. Even outer scope definitions cause this.

**⭐ PREFERRED: name the ambient instance in the declaration + use `@` (or `[mΩ]`) for ambient facts**

```lean
theorem my_theorem {Ω β γ : Type*} [m0 : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (Z : Ω → β) (W : Ω → γ) (hZ : Measurable Z) (hW : Measurable W)
    ... := by
  -- ✅ STEP 0: the ambient instance already has a NAME (`m0`) from the binder list.
  -- Recovery only if the signature is not yours to change:
  --   let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›

  -- ✅ STEP 1: ALL ambient work against m0 explicitly
  have hBpre : @MeasurableSet Ω m0 (Z ⁻¹' B) := hB.preimage hZ
  have hCpre : @MeasurableSet Ω m0 (W ⁻¹' C) := hC.preimage hW
  -- ... all other ambient facts

  -- ✅ STEP 2: NOW define sub-σ-algebras. `comap f m` pulls the CODOMAIN
  -- structure `m` back along `f` — the argument is mγ / mβ.prod mγ, never m0.
  let mW  : MeasurableSpace Ω := MeasurableSpace.comap W mγ
  let mZW : MeasurableSpace Ω := MeasurableSpace.comap (fun ω ↦ (Z ω, W ω)) (mβ.prod mγ)

  -- ✅ STEP 3: Work with sub-σ-algebras
  have hmW_le : mW ≤ m0 := hW.comap_le
```

**Why `@` is required:** Even if you do ambient work "first," outer scope pollution (e.g., `mW` defined in parent scope) makes Lean pick the wrong instance unless you explicitly force `m0` with `@` notation.

**⚡ Performance optimization:** If calling mathlib lemmas causes timeout errors, use the **three-tier strategy**:
```lean
-- Tier 2: m0 versions (for @ notation)
have hBpre_m0 : @MeasurableSet Ω m0 (Z ⁻¹' B) := hB.preimage hZ_m0

-- Tier 3: Ambient versions (for mathlib lemmas that infer instances). Keep the
-- structure explicit: a bare `MeasurableSet` here selects the newest local (mZW),
-- and `simpa [m0]` is rejected when `m0` is a parameter rather than a `let`.
have hBpre : MeasurableSet[m0] (Z ⁻¹' B) := hBpre_m0

-- Use ambient version with mathlib:
have := integral_indicator hBpre ...  -- No expensive unification!
```

This eliminates timeout errors (500k+ heartbeats → normal) by avoiding expensive type unification.

**📚 For full details:** See [instance-pollution.md](instance-pollution.md) - explains scope pollution, 4 solutions, and performance optimization

---

### 2. The `inferInstance` Drift Trap (Newest Class-Typed Local Wins)

**Problem:** After `set mη := MeasurableSpace.comap η mβ`, every bare `MeasurableSet` / `StronglyMeasurable` / `inferInstance` elaborated *later* resolves to `mη`, the newest `MeasurableSpace Ω` local, while facts elaborated *earlier* still mention the ambient `inst✝⁶`. The two sides then disagree:

**The Error:**
```lean
Type mismatch:
  hη ht has type @MeasurableSet Ω inst✝⁶ (η ⁻¹' t)
but expected       @MeasurableSet Ω mη (η ⁻¹' t)
```

**Root cause:** not a mutating `inferInstance` — an elaborated value is stable. Each `set`/`let` of a `MeasurableSpace Ω` adds a newer class-typed local, and *later* elaboration picks it. Name the ambient instance and state ambient facts against it and the two sides agree; `set` itself is not the problem, unnamed ambient facts after it are.

**❌ What DOESN'T work:**
```lean
set mη := MeasurableSpace.comap η mβ   -- newest `MeasurableSpace Ω` local from here on

-- Stated AFTER the `set`, with the instance left implicit: resolves to mη
have hpre : MeasurableSet (η ⁻¹' t) := hη ht   -- ❌ inst✝⁶ vs mη mismatch
```

**✅ Solution A (default): name the ambient instance, state ambient facts against it**
```lean
lemma foo {Ω β : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    (η : Ω → β) (hη : Measurable η) ... := by
  set mη := MeasurableSpace.comap η mβ
  have hpre : MeasurableSet[mΩ] (η ⁻¹' t) := hη ht        -- ✅ names mΩ
  have hmη_le : mη ≤ mΩ := hη.comap_le
```

**✅ Solution B: inline the comaps so no intermediate class-typed local exists**

```lean
lemma foo {Ω β : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    (η ζ : Ω → β) (hη : Measurable η) (hζ : Measurable ζ) ... := by
  -- no `set`: nothing new for later elaboration to pick up
  have hmη_le : MeasurableSpace.comap η mβ ≤ mΩ := hη.comap_le
  have hmζ_le : MeasurableSpace.comap ζ mβ ≤ mΩ := hζ.comap_le

  -- inlined comaps in the lemma applications
  have hCEη : μ[f | MeasurableSpace.comap η mβ] =ᵐ[μ]
              (fun ω ↦ ∫ y, f y ∂(condExpKernel μ (MeasurableSpace.comap η mβ) ω)) :=
    condExp_ae_eq_integral_condExpKernel hmη_le hint
```

**Why it works:**
- A named ambient instance (`mΩ`, from the binder list) is a stable reference; `MeasurableSet[mΩ]` / `@MeasurableSet Ω mΩ` says which structure a fact is about
- Without an intermediate name there is no newer class-typed local for later elaboration to prefer
- `MeasurableSpace.comap η mβ` takes the **codomain** structure (`mβ : MeasurableSpace β` for `η : Ω → β`), never the ambient `MeasurableSpace Ω`

**Key takeaways:**
1. Name the ambient instance in the declaration; `let m0 := ‹…›` only when the signature is not yours to change
2. Ambient facts stated after a `set`/`let` of a `MeasurableSpace Ω` must name the instance (`MeasurableSet[mΩ]`, `@`)
3. Inlining the comaps is the alternative when you would rather not name anything
4. Adding local instances (`have`/`haveI`) adds MORE class-typed locals; it does not fix drift
5. Compile-checked: `tests/fixtures/reference_snippets/measure_theory_snippets.lean` elaborates the transport line with `StronglyMeasurable[mΩ]`, and its executable `#guard_msgs` control shows the bare `StronglyMeasurable` form failing ("expected mW ≤ mZW")

**Real-world impact:** Resolved ALL instance synthesis errors in 150-line conditional expectation proofs (Kallenberg Lemma 1.3).

---

### 3. Set-Integral Projection (Not Idempotence)

**Instead of proving** `μ[g|m] = g` a.e., **use this:**

```lean
-- For s ∈ m, Integrable g:
have : ∫ x in s, μ[g|m] x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_condExp (μ := μ) (m := m) (hm := hm) (hs := hs) (hf := hg)
```

**Wrapper to avoid parameter drift** (name the ambient space — `hm : m ≤ ‹_›` resolves to `m ≤ m`, the exact trap this reference warns about; state `hs` for `m`; the finite-measure assumption supplies `SigmaFinite (μ.trim hm)`):
```lean
lemma setIntegral_condExp_eq {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {s : Set Ω} (hs : MeasurableSet[m] s) {g : Ω → ℝ} (hg : Integrable g μ) :
    ∫ x in s, (μ[g|m]) x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_condExp hm hg hs
```

---

### 4. Product → Indicator (Avoid Product Measurability)

```lean
-- Rewrite product to indicator
have hMulAsInd : (fun ω ↦ μ[f|mW] ω * gB ω) = (Z ⁻¹' B).indicator (μ[f|mW]) := by
  funext ω; by_cases hω : ω ∈ Z ⁻¹' B
  · simp [gB, hω, Set.indicator_of_mem, mul_one]
  · simp [gB, hω, Set.indicator_of_notMem, mul_zero]

-- Integrability without product measurability
have : Integrable (fun ω ↦ μ[f|mW] ω * gB ω) μ := by
  simpa [hMulAsInd] using (integrable_condExp).indicator (hB.preimage hZ)
```

**Restricted integral:** `∫_{S} (Z⁻¹ B).indicator h = ∫_{S ∩ Z⁻¹ B} h`

---

### 5. Bounding CE Pointwise (NNReal Friction-Free)

```lean
-- From |f| ≤ R to ‖μ[f|m]‖ ≤ R a.e.
have hbdd_f : ∀ᵐ ω ∂μ, |f ω| ≤ (1 : ℝ) := …
have hbdd_f' : ∀ᵐ ω ∂μ, |f ω| ≤ ((1 : ℝ≥0) : ℝ) :=
  hbdd_f.mono (fun ω h ↦ by simpa [NNReal.coe_one] using h)
have : ∀ᵐ ω ∂μ, ‖μ[f|m] ω‖ ≤ (1 : ℝ) := by
  simpa [Real.norm_eq_abs, NNReal.coe_one] using
    ae_bdd_condExp_of_ae_bdd (μ := μ) (m := m) (R := (1 : ℝ≥0)) (f := f) hbdd_f'
```

---

### 6. σ-Algebra Relations (Ready-to-Paste)

Compile-checked (`tests/fixtures/reference_snippets/measure_theory_snippets.lean`). Assumes named ambient structures in the declaration: `[mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]`, `Z : Ω → β`, `W : Ω → γ`, `hZ : Measurable Z`, `hW : Measurable W`. `comap` takes the **codomain** structure.

```lean
-- σ(W) and σ(Z,W) as comaps of the CODOMAIN structures
let mW  : MeasurableSpace Ω := MeasurableSpace.comap W mγ
let mZW : MeasurableSpace Ω := MeasurableSpace.comap (fun ω ↦ (Z ω, W ω)) (mβ.prod mγ)

-- σ(W) ≤ ambient
have hmW_le : mW ≤ mΩ := hW.comap_le

-- σ(Z,W) ≤ ambient
have hmZW_le : mZW ≤ mΩ := (hZ.prodMk hW).comap_le

-- σ(W) ≤ σ(Z,W): W = Prod.snd ∘ (Z,W)
have hmW_le_mZW : mW ≤ mZW :=
  MeasurableSpace.comap_le_comap_of_eq_comp Prod.snd measurable_snd rfl

-- Measurability transport — name the ambient instance: after the two `let`s a
-- bare `StronglyMeasurable` resolves to mZW and `.mono hmW_le` fails
have hsm_ce : StronglyMeasurable[mW] (μ[f|mW]) := stronglyMeasurable_condExp
have hsm_ceAmb : StronglyMeasurable[mΩ] (μ[f|mW]) := hsm_ce.mono hmW_le
```

---

### 7. Indicator-Integration Cookbook

```lean
-- Unrestricted: ∫ (Z⁻¹ B).indicator h = ∫ h * ((Z⁻¹ B).indicator 1)
-- Restricted:  ∫_{S} (Z⁻¹ B).indicator h = ∫_{S ∩ Z⁻¹ B} h

-- Rewrite pattern (avoids fragile lemma names):
have : (fun ω ↦ h ω * indicator (Z⁻¹' B) 1 ω) = indicator (Z⁻¹' B) h := by
  funext ω; by_cases hω : ω ∈ Z⁻¹' B
  · simp [hω, Set.indicator_of_mem, mul_one]
  · simp [hω, Set.indicator_of_notMem, mul_zero]
```

---

### 8. Kernel Form vs Scalar Conditional Expectation

**When to use `condExpKernel` instead of scalar notation `μ[·|m]`.**

#### Problem: Type Class Ambiguity with Scalar Notation

Scalar notation `μ[ψ | m]` relies on implicit instance resolution for `MeasurableSpace`, which gets confused when you have local bindings:

```lean
-- Ambiguous: Which MeasurableSpace instance?
let 𝔾 : MeasurableSpace Ω := ...  -- Local binding
have h : μ[ψ | m] = ... -- Error: Instance synthesis confused!
```

#### Solution: Kernel Form with Explicit Parameters

```lean
-- Explicit: condExpKernel takes μ and m as parameters
μ[ψ | m] =ᵐ[μ] (fun ω ↦ ∫ y, ψ y ∂(condExpKernel μ m ω))
```

**Why kernel form is better for complex cases:**
- **No instance ambiguity:** `condExpKernel μ m` takes measure and sub-σ-algebra as explicit parameters
- **Local bindings don't interfere:** No confusion with `let 𝔾 : MeasurableSpace Ω := ...`
- **Multiple σ-algebras:** Work with several sub-σ-algebras without instance pollution
- **Access to kernel lemmas:** Set integrals, measurability theorems, composition

#### Axiom Elimination Pattern

**Red flag:** Axiomatizing "a function returning measures with measurability properties"

```lean
-- ❌ DON'T: Reinvent condExpKernel
axiom directingMeasure : Ω → Measure α
axiom directingMeasure_measurable_eval : ∀ s, Measurable (fun ω ↦ directingMeasure ω s)
axiom directingMeasure_isProb : ∀ ω, IsProbabilityMeasure (directingMeasure ω)
axiom directingMeasure_marginal : ...
```

**Mathlib already provides this!** These axioms are essentially `condExpKernel μ (tailSigma X)`:
- `directingMeasure X : Ω → Measure α` ≈ `condExpKernel μ (tailSigma X)`
- `directingMeasure_measurable_eval` ≈ built-in kernel measurability
- `directingMeasure_isProb` ≈ `IsMarkovKernel` property
- `directingMeasure_marginal` ≈ `condExp_ae_eq_integral_condExpKernel`

**Lesson:** When tempted to axiomatize "function returning measures," check if mathlib's kernel API already provides it!

#### Prerequisites for condExpKernel

```lean
-- Required instances
[StandardBorelSpace Ω]  -- Ω is standard Borel
[IsFiniteMeasure μ]      -- μ is finite
```

**Note:** More restrictive than scalar CE, but most probability spaces satisfy these conditions.

#### Migration Strategy: Scalar → Kernel

**Before (scalar, instance-dependent):**
```lean
have h : ∫ ω in s, φ ω * μ[ψ | m] ω ∂μ = ∫ ω in s, φ ω * V ω ∂μ
```

**After (kernel, explicit):**
```lean
-- Step 1: Convert scalar to kernel form
have hCE : μ[ψ | m] =ᵐ[μ] (fun ω ↦ ∫ y, ψ y ∂(condExpKernel μ m ω))

-- Step 2: Work with kernel form
have h : ∫ ω in s, φ ω * (∫ y, ψ y ∂(condExpKernel μ m ω)) ∂μ = ...
```

**Trade-off:** Notational simplicity → instance clarity + axiom elimination

#### When to Use Which Form

**Use scalar form `μ[·|m]` when:**
- ✅ Only one σ-algebra in scope (no ambiguity)
- ✅ Simple algebraic manipulations (pull-out lemmas, tower property)
- ✅ No need for kernel-specific theorems
- ✅ Working in measure-theory basics

**Use kernel form `condExpKernel μ m` when:**
- ✅ Multiple σ-algebras in scope (local bindings like `let 𝔾 := ...`)
- ✅ Need explicit control over measure/σ-algebra binding
- ✅ Want to eliminate custom axioms about "measures parametrized by Ω"
- ✅ Need kernel composition or Markov kernel properties
- ✅ Hitting instance synthesis errors with scalar notation

#### Key Kernel Lemmas

```lean
-- Conversion between forms
condExp_ae_eq_integral_condExpKernel : μ[f | m] =ᵐ[μ] (fun ω ↦ ∫ y, f y ∂(condExpKernel μ m ω))

-- Kernel measurability
Measurable.eval_condExpKernel : Measurable (fun ω ↦ condExpKernel μ m ω s)

-- Markov kernel property
IsMarkovKernel.condExpKernel : IsMarkovKernel (condExpKernel μ m)
```

**Bottom line:** `condExpKernel` is the explicit, principled alternative when you need fine-grained instance control or when you're tempted to axiomatize "functions returning measures."

---

## Kernel and Measure API Patterns

**Essential distinctions and common patterns when working with mathlib's kernel and measure APIs.**

### 1. Kernel vs Measure Type Distinction

**Critical insight:** `Kernel α β` and `Measure β` are fundamentally different types with different APIs.

```lean
-- Kernel: function with measurability properties
Kernel α β = α → Measure β (with measurability)

-- condExpKernel example
condExpKernel μ (tailSigma X) : @Kernel Ω Ω (tailSigma X) inst
-- Source uses tailSigma measurable space
-- Target uses ambient space
```

**Problem:** Kernel.map requires source and target to have **the same measurable space structure**.

```lean
-- ❌ WRONG: Can't use Kernel.map when measurable spaces don't align
Kernel.map (condExpKernel μ m) f  -- Type error!

-- ✅ RIGHT: Evaluate kernel first, then map the resulting measure
fun ω ↦ (condExpKernel μ m ω).map f
```

**Lesson:** When your kernel changes measurable spaces (like `condExpKernel`), you can't use `Kernel.map`. Instead, evaluate the kernel at a point to get a `Measure`, then use `Measure.map`.

### 2. Measure.map for Pushforward

**API:** `Measure.map (f : α → β) (μ : Measure α) : Measure β`

**Key properties:**
```lean
-- Pushforward characterization
Measure.map_apply : (μ.map f) s = μ (f ⁻¹' s)
  -- When f is measurable and s is measurable

-- Automatic handling
-- Returns 0 if f not AE measurable (fail-safe)

-- Probability preservation
isProbabilityMeasure_map : IsProbabilityMeasure μ → AEMeasurable f μ →
  IsProbabilityMeasure (μ.map f)
```

**Pattern: Always use Measure.map for pushforward, not Kernel.map**

```lean
-- Given: μ_ω : Ω → Measure α, f : α → β
-- Want: Pushforward each μ_ω along f

-- Correct approach
fun ω ↦ (μ_ω ω).map f

-- Search with lean_leanfinder:
-- "Measure.map pushforward measurable function"
-- "isProbabilityMeasure preserved by Measure.map"
```

### 3. Kernel Measurability Proofs

**Pattern:** Proving `Measurable (fun ω ↦ κ ω s)` where `κ : Kernel α β`.

```lean
-- Step 1: Recognize this is kernel evaluation at a set
have : (fun ω ↦ κ ω s) = fun ω ↦ Kernel.eval κ s ω

-- Step 2: Use Kernel.measurable_coe
have : Measurable (fun a ↦ κ a s) := Kernel.measurable_coe κ hs
  -- where hs : MeasurableSet s
```

**Gotcha:** Type inference doesn't always work - you need to explicitly provide:
- The kernel `κ`
- The measurable set `s` with proof `hs : MeasurableSet s`

**API lemmas:**
```lean
Kernel.measurable_coe : MeasurableSet s → Measurable (fun a ↦ κ a s)
```

### 4. condExpKernel API Gaps

**Discovery:** The `condExpKernel` API is relatively sparse in mathlib.

**What exists:**
- `condExp_ae_eq_integral_condExpKernel` - conversion from scalar to kernel
- `Measurable.eval_condExpKernel` - kernel evaluation measurability
- `IsMarkovKernel.condExpKernel` - Markov kernel typeclass

**What's missing/hard to find:**
- No obvious `isProbability_condExpKernel` lemma
- Limited discoverability of probabilistic properties
- Need to derive from first principles

**Search strategy when stuck:**
1. Look for `condDistrib` lemmas (underlying construction)
2. Search for `IsMarkovKernel` or `IsCondKernel` instances
3. Use `lean_leanfinder` with "conditional kernel probability measure"
4. Be prepared to prove basic properties yourself

**Example searches:**
```python
lean_leanfinder(query="condExpKernel IsProbabilityMeasure")
lean_leanfinder(query="Markov kernel conditional expectation")
```

### 5. Indicator Function Integration

**Standard pattern:**
```lean
∫ x, (indicator B 1 : α → ℝ) x ∂μ = (μ B).toReal
```

**API:** `integral_indicator_one` - but requires specific form.

**Problem:** Indicators have multiple representations:
```lean
-- Different forms (not all recognized by API)
if x ∈ B then 1 else 0           -- if-then-else
Set.indicator B 1                 -- Set.indicator
Set.indicator B (fun _ ↦ 1)      -- Function form
(B.indicator 1) ∘ f               -- Composed
```

**Lesson:** Integration lemmas expect specific forms. Use `simp` or `rw` to normalize before applying lemmas.

**Pattern:**
```lean
-- Normalize to canonical form first
have : (fun x ↦ if x ∈ B then 1 else 0) = B.indicator 1 := by
  funext x; by_cases hx : x ∈ B <;> simp [hx, Set.indicator]

-- Now apply integration lemma
rw [this, integral_indicator_one]
```

### 6. Function vs Method Syntax

**Inconsistency in mathlib:** Some lemmas are functions, not methods.

```lean
-- ❌ WRONG: Trying method syntax
have := (hf : Measurable f).measurableSet_preimage hs
-- Error: unknown field 'measurableSet_preimage'

-- ✅ RIGHT: Use function syntax
have := measurableSet_preimage hf hs
```

**Pattern:** When you see "unknown field" errors:
1. Try standalone function: `lemma_name hf hs` instead of `hf.lemma_name hs`
2. Use `#check @lemma_name` to see the signature
3. Search with `lean_leanfinder` to find the right form

### 7. Type Class Synthesis Fragility

**Common issues:**
```lean
-- Error: "type class instance expected"
have := condExp_ae_eq_integral_condExpKernel
-- Missing: implicit measure, sub-σ-algebra, or typeclass instance

-- Error: "failed to synthesize IsProbabilityMeasure"
-- Even when it should be inferrable from context
```

**Solutions:**

**Explicit parameters:**
```lean
-- Pin everything explicitly
have := condExp_ae_eq_integral_condExpKernel (μ := μ) (m := tailSigma X) (hm := hm)
```

**Manual instances:**
```lean
-- Provide instance explicitly
have : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf
-- `[IsProbabilityMeasure μ]` is an instance argument, not a hypothesis to pass; for
-- `hf : Measurable f` use `hf.aemeasurable`
```

**Type annotations:**
```lean
-- Help elaborator with type
(μ.map f : Measure β)   -- a measure is a value, never `: Type`
```

### 8. API Discovery with lean_leanfinder

**What works well:**

**Natural language + Lean identifiers:**
```python
lean_leanfinder(query="Measure.map pushforward measurable function")
lean_leanfinder(query="IsProbabilityMeasure preserved map")
```

**Mathematical concepts:**
```python
lean_leanfinder(query="kernel composition measurability")
lean_leanfinder(query="conditional expectation integral representation")
```

**When stuck on names:**
```python
# Instead of grepping, use semantic search
lean_leanfinder(query="preimage measurable set is measurable")
# Finds: measurableSet_preimage
```

**Pattern:** Combine mathematical intent with suspected Lean API terms. LeanFinder is much better than grep for discovery.

### 9. Incremental Development with Sorries

**Recommended workflow:**

**Phase 1: Get architecture right**
```lean
-- Focus on types and structure
def myKernel : Kernel Ω α := by
  intro ω
  exact (condExpKernel μ m ω).map f  -- Right structure
  sorry  -- TODO: Prove measurability
```

**Phase 2: Add detailed TODOs**
```lean
-- Document proof strategy
sorry  -- TODO: Need measurableSet_preimage hf hs
       --       Then use Kernel.measurable_coe
```

**Phase 3: Fill incrementally**
- Reduce errors from 10+ to 5 (commit)
- Reduce from 5 to 2 (commit)
- Complete all proofs (commit)

**Why this works:**
- Type errors caught early (architecture bugs)
- TODOs capture proof strategy while fresh
- Incremental commits preserve working states
- Can get feedback on approach before full completion

**Don't:** Try to perfect everything at once. Get the architecture right first.

---

## Mathlib Lemma Quick Reference

**Conditional expectation (scalar form):**
- `integrable_condExp`, `stronglyMeasurable_condExp`, `stronglyMeasurable_condExp.aestronglyMeasurable` (there is no `aestronglyMeasurable_condExp`)
- `setIntegral_condExp` - set-integral projection (wrap as `setIntegral_condExp_eq`)

**Conditional expectation (kernel form):**
- `condExp_ae_eq_integral_condExpKernel` - convert scalar to kernel form
- `Measurable.eval_condExpKernel` - kernel evaluation is measurable
- `IsMarkovKernel.condExpKernel` - kernel is Markov

**Kernels and pushforward:**
- `Kernel.measurable_coe` - kernel evaluation at measurable set is measurable
- `Measure.map_apply` - pushforward characterization: `(μ.map f) s = μ (f ⁻¹' s)`
- `Measure.isProbabilityMeasure_map hf` - probability preserved by pushforward (`hf : AEMeasurable f μ`; the probability assumption is an instance argument)
- `measurableSet_preimage` - preimage of measurable set is measurable (function syntax!)

**A.E. boundedness:**
- `ae_bdd_condExp_of_ae_bdd` - bound CE from bound on f (NNReal version)

**Indicators:**
- `integral_indicator`, `Integrable.indicator`
- `Set.indicator_of_mem`, `Set.indicator_of_notMem`, `Set.indicator_indicator`

**Trimmed measures:**
- `isFiniteMeasure_trim` (instance; needs `[IsFiniteMeasure μ]`), `IsFiniteMeasure.toSigmaFinite` (instance) — plain `sigmaFinite_trim` no longer exists, and `[SigmaFinite μ]` alone does not give `SigmaFinite (μ.trim hm)` (`sigmaFinite_trim_bot_iff`); see `sigmaFiniteTrim_mono` / `SigmaFinite.of_trim`

**Measurability lifting:**
- `MeasurableSet[m] s → MeasurableSet[m₀] s` via `hm _ hs_m` where `hm : m ≤ m₀`
