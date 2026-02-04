# Proof Templates

Structured proof skeletons for common proof patterns.

## General Theorem Template

```lean
theorem my_theorem (n : ℕ) : conclusion := by
  -- TODO: Strategy - Describe proof approach here
  -- Step 1: [Describe what needs to be shown]
  have h1 : _ := by
    sorry
    -- TODO: Prove first key property

  -- Step 2: [Describe next step]
  have h2 : _ := by
    sorry
    -- TODO: Prove second key property

  -- Step 3: Combine results
  sorry
  -- TODO: Apply h1 and h2 to conclude
```

## Induction Template

```lean
theorem induction_example (n : ℕ) : P n := by
  induction n with
  | zero =>
    -- Base case: n = 0
    sorry
    -- TODO: Prove base case

  | succ n ih =>
    -- Inductive step: assume P(n), prove P(n+1)
    -- Inductive hypothesis: ih : P(n)
    sorry
    -- TODO: Use ih to prove P(n+1)
    -- Strategy: [Describe how to use ih]
```

## Case Analysis Template

```lean
theorem cases_example (h : a ∨ b) : c := by
  cases h with
  | inl h_left =>
    -- Case 1: Left branch
    sorry
    -- TODO: Handle left case
    -- Available: h_left

  | inr h_right =>
    -- Case 2: Right branch
    sorry
    -- TODO: Handle right case
    -- Available: h_right
```

## Calculation Chain Template

```lean
theorem calc_example : a = d := by
  calc a = b := by
      sorry
      -- TODO: Prove a = b
      -- Hint: [Which lemma applies?]
    _ = c := by
      sorry
      -- TODO: Prove b = c
      -- Hint: [Simplify or rewrite?]
    _ = d := by
      sorry
      -- TODO: Prove c = d
      -- Hint: [Final step]
```

## Existential Proof Template

```lean
theorem exists_example : ∃ x, P x ∧ Q x := by
  -- Strategy: Construct witness, then prove property
  use witness_value
  -- TODO: Provide the witness value

  constructor
  · -- Prove first property
    sorry
    -- TODO: Show witness satisfies first condition

  · -- Prove second property
    sorry
    -- TODO: Show witness satisfies second condition
```

## Strong Induction Template

```lean
theorem strong_induction (n : ℕ) : P n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- ih : ∀ m < n, P m
    sorry
    -- TODO: Use ih for all smaller values
```

## Well-Founded Induction Template

```lean
theorem wf_induction [WellFoundedRelation α] (a : α) : P a := by
  induction a using WellFounded.induction with
  | _ a ih =>
    -- ih : ∀ b < a, P b
    sorry
```

## If-Then-Else Template

```lean
theorem ite_example (h : if P then A else B) : C := by
  by_cases hP : P
  · -- Case: P is true
    simp only [hP, if_true] at h
    sorry
  · -- Case: P is false
    simp only [hP, if_false] at h
    sorry
```

## Uniqueness Proof Template

```lean
theorem unique_example : ∃! x, P x := by
  use witness
  constructor
  · -- Existence: P witness
    sorry
  · -- Uniqueness: ∀ y, P y → y = witness
    intro y hy
    sorry
```

## Equivalence Proof Template

```lean
theorem iff_example : P ↔ Q := by
  constructor
  · -- Forward: P → Q
    intro hp
    sorry
  · -- Backward: Q → P
    intro hq
    sorry
```

## Tips for Using Templates

1. **Start with the easiest sorry** - Often the base case or simple properties
2. **Fill in TODOs** - Replace placeholders with actual proof steps
3. **Build frequently** - `lake build` after each sorry filled
4. **Search before proving** - Most lemmas exist in mathlib
5. **One sorry at a time** - Commit after each successful fill

## See Also

- [tactic-patterns.md](tactic-patterns.md) - Tactics by goal type
- [calc-patterns.md](calc-patterns.md) - Calculation mode patterns
- [lean-phrasebook.md](lean-phrasebook.md) - Common proof idioms
