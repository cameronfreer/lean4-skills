# Guide: Avoiding Instance Pollution in Lean 4

## The Problem

When you have multiple `MeasurableSpace Ω` instances in scope, Lean's elaborator preferentially selects **recently-defined local constants** over the ambient typeclass instance.

### Example of the Problem

```lean
theorem my_theorem (Ω β : Type*) [inst : MeasurableSpace Ω] [MeasurableSpace β]
    (Z : Ω → β) (hZ : Measurable Z) (B : Set β) (hB : MeasurableSet B) : ... := by

  let mSub : MeasurableSpace Ω := MeasurableSpace.comap Z inferInstance

  -- ❌ ERROR: Lean picks mSub instead of inst!
  have hBpre : MeasurableSet (Z ⁻¹' B) := hB.preimage hZ
  --           ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  -- Elaborates to: @MeasurableSet Ω mSub (Z ⁻¹' B)
  -- But hZ has type: @Measurable Ω β inst _ Z
  -- Type mismatch!
```

**Root Cause**: The `let mSub : MeasurableSpace Ω := ...` creates a NEW local constant that shadows the ambient instance for elaboration purposes.

---

## Solutions Comparison

### ❌ What DOESN'T Work

#### 1. Using `abbrev` in theorem body
```lean
theorem test : ... := by
  abbrev m0 := inferInstance  -- ❌ Syntax error: abbrev not allowed in tactic mode
```

**Why not**: `abbrev` is a top-level command only, cannot be used inside proofs.

#### 2. Using `abbrev` at top-level then `let` binding
```lean
abbrev mSub_def (Ω β : Type*) ... := MeasurableSpace.comap ...

theorem test : ... := by
  let mSub := mSub_def Ω β ...
  -- ❌ Still creates pollution! The `let` binding is the problem
```

**Why not**: Even if the RHS is an `abbrev`, the `let` binding creates a local constant that pollutes instance inference.

#### 3. Using `set` instead of `let`
```lean
theorem test : ... := by
  set mSub : MeasurableSpace Ω := ...
  -- ❌ Same problem as `let`
```

**Why not**: `set` also creates a local constant.

---

## ✅ Solutions That Work

### Solution 1: Don't Create Local Bindings (Best for Simple Cases)

**When to use**: When you only reference the sub-σ-algebra a few times.

```lean
theorem test (Ω β : Type*) [MeasurableSpace Ω] [MeasurableSpace β]
    (Z : Ω → β) (hZ : Measurable Z) (B : Set β) (hB : MeasurableSet B) : ... := by

  -- ✅ No local constant = no pollution
  have hBpre : MeasurableSet (Z ⁻¹' B) := hB.preimage hZ

  -- If you need to reference the sub-σ-algebra, write it out:
  have : (MeasurableSpace.comap Z inferInstance) ≤ (inferInstance : MeasurableSpace Ω) := by
    -- proof
```

**Pros**:
- Simple
- No pollution
- Works in all contexts

**Cons**:
- Verbose if you need to reference the sub-σ-algebra many times
- Harder to read with long expressions

---

### Solution 2: Do Ambient Work First, Then Define Local Instances

**When to use**: When you need to work with both ambient and sub-σ-algebras.

```lean
theorem test (Ω β : Type*) [MeasurableSpace Ω] [MeasurableSpace β]
    (Z : Ω → β) (hZ : Measurable Z) (B : Set β) (hB : MeasurableSet B) : ... := by

  -- ✅ STEP 1: Do ALL ambient instance work FIRST
  have hBpre : MeasurableSet (Z ⁻¹' B) := hB.preimage hZ
  have hCpre : MeasurableSet (W ⁻¹' C) := hC.preimage hW
  -- ... all other ambient facts

  -- ✅ STEP 2: THEN define local sub-σ-algebras
  let mSub : MeasurableSpace Ω := MeasurableSpace.comap Z inferInstance

  -- ✅ STEP 3: Work with mSub (will use it correctly from now on)
  have : mSub ≤ (inferInstance : MeasurableSpace Ω) := by
    intro s hs
    exact hs.preimage hZ
```

**Pros**:
- Clean separation of concerns
- Can name sub-σ-algebras for readability
- No `@` notation needed

**Cons**:
- Requires restructuring proof
- Can't interleave ambient and sub-σ-algebra work

**Key Principle**: Once you define `let mSub : MeasurableSpace Ω`, ALL subsequent `MeasurableSet`/`Measurable` etc. will preferentially use `mSub`. So do ambient work BEFORE defining it.

---

### Solution 3: Force with `@` Notation (Pattern A - Complex but Precise)

**When to use**: When you can't restructure and need both instances in scope simultaneously.

```lean
theorem test (Ω β : Type*) [inst : MeasurableSpace Ω] [MeasurableSpace β]
    (Z : Ω → β) (hZ : Measurable Z) (B : Set β) (hB : MeasurableSet B) : ... := by

  let mSub : MeasurableSpace Ω := MeasurableSpace.comap Z inferInstance

  -- ✅ Force ambient instance with @ notation
  have hBpre : @MeasurableSet Ω inst (Z ⁻¹' B) :=
    hB.preimage hZ  -- Type annotation on result is enough!

  -- For more complex cases, may need @ everywhere:
  have complex : @MeasurableSet Ω inst someset :=
    @MeasurableSet.inter Ω inst s1 s2 hs1 hs2
```

**Pros**:
- Precise control
- Works when other solutions don't

**Cons**:
- Verbose
- Error-prone (easy to forget `@` somewhere)
- May need type annotations on intermediate terms

**Helper Pattern** (from user's Pattern A):
```lean
-- Create conversion helpers
have measurable_congr {m₁ m₂ : MeasurableSpace Ω} (hm : m₁ = m₂) {f : Ω → β} :
    @Measurable Ω β m₁ _ f ↔ @Measurable Ω β m₂ _ f := by simp [hm]

-- Use .mpr/.mp to convert facts
have hZ_sub : @Measurable Ω β mSub _ Z := (measurable_congr some_eq).mpr hZ
```

---

### Solution 4: Use `abbrev` at Section Level (Best for Multiple Theorems)

**When to use**: When writing multiple related theorems that all need the same sub-σ-algebras.

```lean
section MySection
  variable (Ω β : Type*) [MeasurableSpace Ω] [MeasurableSpace β]
  variable (Z : Ω → β) (hZ : Measurable Z)

  -- ✅ Define once at section level
  abbrev mSub : MeasurableSpace Ω := MeasurableSpace.comap Z inferInstance

  theorem theorem1 (B : Set β) (hB : MeasurableSet B) : ... := by
    -- Can reference mSub, but STILL do ambient work first!
    have hBpre : MeasurableSet (Z ⁻¹' B) := hB.preimage hZ  -- ✅ Works!
    -- ... rest of proof

  theorem theorem2 : ... := by
    -- mSub available here too
end MySection
```

**Pros**:
- Share definitions across multiple theorems
- `abbrev` is definitionally transparent
- Less repetition

**Cons**:
- Only works at section/file level
- Still can't use in middle of proof
- Variables must be shared across all theorems in section

**IMPORTANT**: Even with section-level `abbrev`, you should STILL do ambient work before referencing `mSub` in each individual theorem. The `abbrev` doesn't prevent the pollution once you reference it!

---

## Recommended Approach

### For New Code:

1. **Default**: Use **Solution 2** (ambient work first, then define locals)
   - Cleanest and most maintainable
   - No `@` notation needed
   - Clear proof structure

2. **If sub-σ-algebra used rarely**: Use **Solution 1** (no local bindings)
   - Even simpler
   - Just write out the expression when needed

3. **For shared definitions**: Use **Solution 4** (section-level `abbrev`)
   - When multiple theorems need the same sub-σ-algebra
   - Still follow Solution 2 pattern within each proof

### For Fixing Existing Code:

1. **If possible, restructure**: Move ambient work before local definitions (Solution 2)

2. **If can't restructure**: Use **Solution 3** (force with `@`)
   - Add type annotations to results: `have h : @MeasurableSet Ω inst s := ...`
   - Create conversion helpers if needed
   - Be systematic - mark every ambient fact clearly

---

## Common Mistakes

### ❌ Mistake 1: Thinking `abbrev` prevents pollution
```lean
abbrev mSub := ...  -- at top level

theorem test : ... := by
  let m := mSub  -- ❌ The `let` still creates pollution!
```

**Fix**: Don't bind `abbrev` results to local `let` variables.

### ❌ Mistake 2: Mixing ambient and sub-σ-algebra work
```lean
theorem test : ... := by
  let mSub : MeasurableSpace Ω := ...

  have h1 : MeasurableSet s1 := ...  -- ❌ Uses mSub (probably wrong!)
  have h2 : something about mSub
  have h3 : MeasurableSet s2 := ...  -- ❌ Still uses mSub!
```

**Fix**: Do ALL ambient work before `let mSub`, or use `@` notation.

### ❌ Mistake 3: Using `letI` for non-instance data
```lean
letI mSub : MeasurableSpace Ω := ...  -- ❌ Installs as THE instance!
have : MeasurableSet s := ...  -- Now EVERYTHING uses mSub
```

**Fix**: Only use `letI` when you actually want to replace the instance. For data, use plain `let` (but follow Solution 2 pattern).

---

## Quick Reference

| Situation | Solution | Complexity |
|-----------|----------|------------|
| Sub-σ-algebra used 1-2 times | Solution 1: No local binding | ⭐ Simple |
| Sub-σ-algebra used many times, can restructure | Solution 2: Ambient work first | ⭐⭐ Medium |
| Multiple theorems need same sub-σ-algebra | Solution 4: Section `abbrev` | ⭐⭐ Medium |
| Can't restructure, need both instances | Solution 3: Force with `@` | ⭐⭐⭐ Complex |

---

## Summary

- **`let`/`set` always create local constants that pollute instance inference**
- **`abbrev` only works at top-level, not in proofs**
- **Best practice**: Do ambient instance work BEFORE defining sub-σ-algebras
- **If stuck**: Use `@` notation to force the ambient instance
- **Never use**: `letI` for data (only for actual instance replacement)

The key insight: **Instance pollution is about WHEN you create the binding, not HOW**. The solution is to control the order of your proof steps, not to find a magic binding syntax.
