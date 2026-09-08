# Tactic Patterns by Goal Type

Quick reference for choosing tactics based on goal structure.

## Goal Structure Patterns

### Equality (`a = b`)

**Primary tactics:**
- `rfl` - Definitional equality
- `simp` / `simp only [...]` - Simplification
- `ring` - Polynomial/ring equalities
- `field_simp` - Field equalities with division
- `ext` / `funext` - Function equality (prove pointwise)

**Rewriting:**
- `rw [lemma]` - Rewrite left-to-right
- `rw [← lemma]` - Rewrite right-to-left

### Universal Quantifier (`∀ x, P x`)

- `intro x y` - Introduce variable(s) by name (`intros` exists in Lean 4 but yields inaccessible names; prefer `intro`)
- `intro x` - Introduce with specific name

### Existential Quantifier (`∃ x, P x`)

- `use x` - Provide witness
- `refine ⟨x, ?_⟩` - Provide witness, leave proof as goal
- `constructor` - Split into witness and proof goals

### Implication (`P → Q`)

- `intro h` - Assume hypothesis
- `intro h₁ h₂` - Introduce multiple hypotheses by name

### Conjunction (`P ∧ Q`)

- `constructor` - Split into two goals
- `refine ⟨?_, ?_⟩` - Structured proof
- `exact ⟨proof1, proof2⟩` - Direct proof (if you have both)

### Disjunction (`P ∨ Q`)

- `left` - Prove left side
- `right` - Prove right side
- `by_cases h : P` - Split on decidable proposition

### Inequality (`<`, `≤`, `>`, `≥`)

- `linarith` - Linear arithmetic solver
- `omega` - Integer linear arithmetic
- `positivity` - Prove positivity
- `gcongr` - Goal congruence (monotonicity)
- `calc` - Chain of inequalities

## Domain-Specific Patterns

### Measure Theory

Goal contains: `Measure`, `Measurable`, `μ`, `∫`, `Integrable`, `AEMeasurable`, `MeasurableSet`

- `measurability` - Solve measurability goals
- `filter_upwards` - Work with a.e. properties
- `ae_of_all` - Lift pointwise to a.e.
- `setIntegral_congr_ae` - Integral equality via a.e. equality

### Probability Theory

Goal contains: `IsProbabilityMeasure`, `probability`, `condExp`

- `have : IsProbabilityMeasure μ := ⟨measure_univ_proof⟩` - Supply the instance with its proof (plain `have` registers it; `inferInstance` only freezes one that already synthesizes)
- `ae_eq_condExp_of_forall_setIntegral_eq` - Conditional expectation uniqueness via set integrals (there is no `condExp_unique`)
- `measurability` - Check measurability

### Topology/Analysis

Goal contains: `Continuous`, `IsOpen`, `IsClosed`, `Tendsto`, `Filter`

- `continuity` - Prove continuity goals
- `fun_prop` - Function property automation
- `apply Continuous.comp` - Composition of continuous functions

### Algebra

Goal contains: `Group`, `Ring`, `Field`, `Monoid`, `comm`, `mul`, `add`

- `ring` - Ring equality
- `field_simp` - Simplify field expressions
- `group` - Group equality
- `abel` - Abelian group equality

## General Tactics (Always Worth Trying)

### Automation
- `simp` / `simp only [...]` - Simplification
- `grind` - Mixed-constraint automation (cross-domain fallback)
- `aesop` - Automated proof search
- `decide` - Decision procedure (for decidable goals)

### Structuring
- `have h : ... := ...` - Introduce intermediate result
- `suffices h : ... by ...` - Backwards reasoning
- `refine ?_` - Placeholder for goal refinement

### Hypothesis Work
- `rcases h with ⟨x, hx⟩` - Destructure ∃ or ∧
- `obtain ⟨x, hx⟩ := h` - Destructure and name
- `cases h` - Case split on h

### Application
- `apply lemma` - Apply lemma, leaving subgoals
- `exact term` - Provide exact proof term
- `assumption` - Use existing hypothesis

## Workflow Tips

1. **Try automation first:** `simp`, `ring`, `linarith`, `grind`, `aesop`
2. **Introduce/destruct:** `intro`, `rcases`, `cases`
3. **Break it down:** `have`, `suffices`, intermediate lemmas
4. **Search mathlib:** Most goals are already solved
5. **Check types:** Use `#check` to understand terms

## See Also

- [tactics-reference.md](tactics-reference.md) - Full tactic documentation
- [lean-phrasebook.md](lean-phrasebook.md) - Common proof patterns
