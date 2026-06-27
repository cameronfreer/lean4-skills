# Lean 4 Tactics Reference

This reference provides comprehensive guidance on essential Lean 4 tactics, when to use them, and common patterns.

**For natural language translations:** See [lean-phrasebook.md](lean-phrasebook.md) for "Mathematical English to Lean" patterns organized by proof situation.

## Decision Tree

```
What's my goal?
├─ Close with exact term → exact / assumption
├─ Apply lemma to reduce goal → apply / refine
├─ Prove equality
│   ├─ By definition → rfl
│   ├─ By rewriting → rw [lemma]
│   ├─ By calculation → calc / ring / field_simp
│   └─ By extensionality → ext / funext
├─ Split goal
│   ├─ And/Iff → constructor
│   ├─ Or → left / right
│   └─ Exists → use witness
├─ Split hypothesis → cases / rcases / obtain
├─ Simplify → simp / norm_num / ring
└─ Don't know → exact? / apply? / simp?
```

---

## Quick Reference

| Want to... | Use... |
|------------|--------|
| Close with exact term | `exact` |
| Apply lemma | `apply` |
| Rewrite once | `rw [lemma]` |
| Normalize expression | `simp`, `ring`, `norm_num` |
| Split cases | `by_cases`, `cases`, `rcases` |
| Prove exists | `use witness` |
| Prove and/iff | `constructor` |
| Prove function equality | `ext` / `funext` |
| Explore options | `exact?`, `apply?`, `simp?` |
| Automate domain-specific | `ring`, `linarith`, `continuity`, `measurability` |
| Cross-domain automation | `grind` (SMT-style) |

The most important tactic is the one you understand!

## Essential Tactics

### Simplification Tactics

#### `simp` - The Workhorse Simplifier

**What it does:** Recursively applies `@[simp]` lemmas to rewrite expressions to normal form.

**Basic usage:**
```lean
example : x + 0 = x := by simp           -- Uses simp lemmas
example : f (g x) = h x := by simp [f_g] -- Explicitly simp with f_g
example : P → Q := by simpa using h      -- simp then exact h
```

**Variants:**
```lean
simp                    -- Use all simp lemmas
simp only [lem1, lem2]  -- Use only specified lemmas (preferred)
simp [*]                -- Include all hypotheses
simp at h               -- Simplify hypothesis h
simp at *               -- Simplify all hypotheses and goal
simpa using h           -- simp then exact h
simp?                   -- Show which lemmas it uses (exploration)
```

**When to use `simp`:**
- Obvious algebraic simplifications (`x + 0`, `x * 1`, etc.)
- Normalizing expressions to canonical form
- Cleaning up after other tactics

**When to use `simp only`:**
- You know which lemmas you need (preferred for clarity)
- Want explicit, reviewable proof
- Avoiding surprising simp behavior

**When NOT to use `simp`:**
- Simple rewrites (use `rw` instead)
- Unclear what it's doing (use `simp?` first, then convert to `simp only`)

#### Deep Dive: The `simp` Tactic

**How simp works internally:**
1. Collects all `@[simp]` lemmas in scope
2. Tries to match lemma left-hand sides against expression
3. Rewrites using right-hand side
4. Recursively simplifies subexpressions
5. Continues until no more lemmas apply

**What makes a good @[simp] lemma:**
```lean
-- ✅ Good: Makes expression simpler
@[simp] lemma add_zero (x : ℕ) : x + 0 = x

@[simp] lemma map_nil : List.map f [] = []

@[simp] lemma indicator_apply (x : X) :
    Set.indicator s f x = if x ∈ s then f x else 0

-- ❌ Bad: Doesn't simplify (creates loop)
@[simp] lemma bad : f (g x) = g (f x)  -- Rewrites back and forth!

-- ❌ Bad: Makes more complex
@[simp] lemma worse : x = x + 0 - 0  -- Right side more complex
```

**Decision tree for adding @[simp]:**
```
Is the right side simpler than the left?
├─ Yes → Good @[simp] candidate
│  └─ Does it create loops with other simp lemmas?
│     ├─ No → Add @[simp]
│     └─ Yes → Don't add @[simp], use manually
└─ No → Don't add @[simp]
```

**Using simp effectively:**
```lean
-- 1. Exploration phase: Use simp? to see what happens
example : x + 0 + y * 1 = x + y := by simp?
-- Output: Try this: simp only [add_zero, mul_one]

-- 2. Production: Convert to explicit
example : x + 0 + y * 1 = x + y := by simp only [add_zero, mul_one]
```

**Common simp patterns:**
```lean
-- Simplify specific terms
simp only [my_def]  -- Unfold my_def

-- Simplify with additional lemmas
simp only [add_zero, mul_one, my_lemma]

-- Simplify and close
simpa [my_lemma] using h

-- Simplify at hypothesis
simp only [my_lemma] at h

-- Normalize then continue
simp only [my_def]
apply other_lemma
```

**simp with calc chains:**

When using `simp` before a `calc` chain, the calc must start with the **already simplified form**, not the original expression. This is especially important with `simp [Real.norm_eq_abs]` which automatically converts `‖x‖` to `|x|`, `|a * b|` to `|a| * |b|`, and `1/(m:ℝ)` to `(m:ℝ)⁻¹`.

```lean
-- ❌ WRONG: calc starts with unsimplified form
filter_upwards with ω; simp [Real.norm_eq_abs]
calc |(1/(m:ℝ)) * ∑...|  -- simp already transformed this!
    _ = (m:ℝ)⁻¹ * |∑...| := by rw [one_div, abs_mul]  -- redundant!

-- ✅ CORRECT: calc starts with simplified form
filter_upwards with ω; simp [Real.norm_eq_abs]
calc (m:ℝ)⁻¹ * |∑...|  -- Start with what simp produced
    _ ≤ ...            -- Focus on actual reasoning
```

**For detailed calc chain patterns, performance tips, and debugging workflows, see:** `references/calc-patterns.md`

### Case Analysis Tactics

#### `by_cases` - Boolean/Decidable Split

```lean
by_cases h : p  -- Creates two goals: one with h : p, one with h : ¬p

example (n : ℕ) : ... := by
  by_cases h : n = 0
  · -- Case h : n = 0
    sorry
  · -- Case h : n ≠ 0
    sorry
```

#### `rcases` - Destructure Hypotheses

```lean
-- Exists
rcases h with ⟨x, hx⟩        -- h : ∃ x, P x
                              -- Gives: x and hx : P x

-- And
rcases h with ⟨h1, h2⟩       -- h : P ∧ Q
                              -- Gives: h1 : P and h2 : Q

-- Or
rcases h with h1 | h2        -- h : P ∨ Q
                              -- Creates two goals

-- Nested
rcases h with ⟨x, y, ⟨hx, hy⟩⟩  -- h : ∃ x y, P x ∧ Q y
```

#### `obtain` - Rcases with Proof

```lean
-- Like rcases but shows intent
obtain ⟨C, hC⟩ := h_bound    -- h_bound : ∃ C, ∀ x, ‖f x‖ ≤ C
-- Now have: C and hC : ∀ x, ‖f x‖ ≤ C
```

#### `cases` - Inductive Type Split

```lean
cases l with                 -- l : List α
| nil => sorry              -- l = []
| cons head tail => sorry   -- l = head :: tail

cases n with                 -- n : ℕ
| zero => sorry             -- n = 0
| succ k => sorry           -- n = k + 1
```

### Rewriting Tactics

#### `rw` - Rewrite with Equality

```lean
rw [lemma]       -- Left-to-right rewrite
rw [← lemma]     -- Right-to-left rewrite (note ←)
rw [lem1, lem2]  -- Multiple rewrites in sequence
rw [lemma] at h  -- Rewrite in hypothesis
```

**Example:**
```lean
example (h : x = y) : x + 1 = y + 1 := by
  rw [h]  -- Rewrites x to y in goal
```

#### `simp_rw` - Simplifying Rewrites

**When to use:** Multiple sequential rewrites or rewrite chains

```lean
-- Sequential rewrites (less efficient)
rw [h₁]
rw [h₂]
rw [h₃]

-- Better: chain with simp_rw
simp_rw [h₁, h₂, h₃]
```

**Advantages over `rw`:**
- Applies rewrites left-to-right repeatedly
- More powerful for chains: can use intermediate results
- Single tactic call = clearer proof structure

**When to prefer `simp_rw`:**
- Multiple related rewrites in sequence
- Rewrite chains where later steps use earlier results
- Measure theory: integral/expectation identity chains

**Example:**
```lean
-- Measure theory rewrite chain
simp_rw [hf_eq, integral_indicator (hY hB), Measure.restrict_restrict (hY hB)]
```

#### `rfl` - Reflexivity of Equality

```lean
-- Proves goals of form a = a (definitionally)
example : 2 + 2 = 4 := by rfl
```

### Application Tactics

#### `exact` - Provide Exact Proof

```lean
exact proof_term  -- Closes goal if term has exactly the right type
```

#### `apply` - Apply Lemma, Leave Subgoals

```lean
apply my_lemma     -- Applies lemma, creates goals for premises
```

**Difference:**
```lean
-- exact: Type must match exactly
example : P := by
  exact h  -- h must have type P

-- apply: Unifies, creates subgoals
example : Q := by
  apply my_lemma  -- my_lemma : P → Q
  -- Creates goal: P
```

#### `refine` - Apply with Placeholders

```lean
refine { field1 := value1, field2 := ?_, field3 := value3 }
-- Creates goal for field2
```

### Construction Tactics

#### `constructor` - Build Inductive

```lean
-- For P ∧ Q
constructor
-- Creates two goals: P and Q

-- For P ↔ Q
constructor
-- Creates: P → Q and Q → P

-- For structures
constructor
-- Creates goals for each field
```

#### `use` - Provide Witness for Exists

```lean
use value   -- For ∃ x, P x, provide the x
            -- Creates goal: P value
```

**Example:**
```lean
example : ∃ n : ℕ, n > 5 := by
  use 10
  -- Goal: 10 > 5
  norm_num
```

### Extension & Congruence

#### `ext` / `funext` - Function Extensionality

```lean
ext x       -- To prove f = g, prove f x = g x for all x
funext x    -- Same, alternative syntax
```

#### `congr` - Congruence

```lean
congr  -- Breaks f a = f b into a = b (when f is the same)
```

### Specialized Tactics

#### Domain-Specific Automation

**Algebra:**
```lean
ring         -- Solve ring equations
field_simp   -- Simplify field expressions
group        -- Solve group equations
```

**Arithmetic:**
```lean
linarith     -- Linear arithmetic on ANY additive group (not just ℝ or ℚ)
             -- Works on: ℝ, ℚ, ℤ, Real.Angle, any group with +/-
             -- Given a + b = c, derives a = c - b, b = c - a, etc.
             -- Example: have : x ≤ y := by linarith
             -- Example: calc (∠ABD : Real.Angle) = 4*π/9 - π/9 := by linarith [split]
nlinarith    -- Non-linear arithmetic
norm_num     -- Normalize numerical expressions (including angle comparisons)
             -- Example: have h : angle_expr = 0 := by rw [lem]; norm_num at h
omega        -- Integer linear arithmetic
             -- Example: have : n < m := by omega
```

**When to use arithmetic tactics:**
```lean
-- ✅ DO: Use omega for integer inequalities
lemma nat_ineq (n m : ℕ) (h1 : n < m) (h2 : m < n + 5) : n + 1 < n + 5 := by
  omega

-- ✅ DO: Use linarith for real/rational linear arithmetic
lemma real_ineq (x y : ℝ) (h1 : x ≤ y) (h2 : y < x + 1) : x < x + 1 := by
  linarith

-- ⚠️ AVOID: Manual inequality chains when tactics work
-- Instead of: apply add_lt_add; exact h1; exact h2
-- Just use: omega (or linarith for reals)
```

**Analysis:**
```lean
continuity      -- Prove continuity automatically
```

**Measure Theory:**
```lean
measurability   -- Prove measurability automatically
                -- Replaces manual measurable_pi_lambda patterns
                -- Use @[measurability] attribute to make lemmas discoverable
                -- See domain-patterns.md Pattern 8 for detailed examples
positivity      -- Prove positivity of measures/integrals
```

**Compositional Function Properties (`fun_prop`):**

`fun_prop` proves function properties compositionally by decomposing functions into simpler parts.

**Basic usage:**
```lean
-- Let fun_prop handle subgoals automatically
fun_prop
```

**With discharge tactic (`disch`):**

The `disch` parameter (short for "discharge") specifies which tactic to use for solving subgoals that `fun_prop` generates.

**Common patterns:**
```lean
-- Measurability (for compositional measurable functions)
fun_prop (disch := measurability)

-- Continuity (for compositional continuous functions)
fun_prop (disch := continuity)

-- From context (when subgoals are hypotheses)
fun_prop (disch := assumption)

-- Algebraic properties
fun_prop (disch := simp)
```

**Example - Measurability:**
```lean
-- Goal: Measurable (fun ω ↦ fun j : Fin n ↦ X (k j) ω)
-- Without disch: fun_prop generates subgoals you must solve manually
-- With disch: automation solves them
have h : Measurable (fun ω ↦ fun j : Fin n ↦ X (k j) ω) := by
  fun_prop (disch := measurability)
```

**Choosing the right `disch` tactic:**
- Proving `Measurable`? → `disch := measurability`
- Proving `Continuous`? → `disch := continuity`
- Subgoals in context? → `disch := assumption`
- Needs simplification? → `disch := simp`
- Not sure? → Try `fun_prop` alone to see subgoals first

**Advanced - Tactic sequences:**
```lean
-- Try measurability, then simplify any remaining goals
fun_prop (disch := (measurability <;> simp))
```

**Making custom lemmas discoverable to `fun_prop`:**

Use the `@[fun_prop]` attribute to make your custom lemmas available to `fun_prop`:

```lean
-- Make lemma discoverable by both tactics
@[measurability, fun_prop]
lemma measurable_shiftℤ : Measurable (shiftℤ (α := α)) := by
  measurability

-- Now fun_prop can automatically use this when it encounters shiftℤ
example : Measurable (fun ω ↦ shiftℤ ω) := by
  fun_prop  -- Automatically finds and applies measurable_shiftℤ
```

**When to use both attributes:**
- `@[measurability]` - Makes lemma discoverable by `measurability` tactic
- `@[fun_prop]` - Makes lemma discoverable by `fun_prop` tactic
- `@[measurability, fun_prop]` - Makes lemma discoverable by both (recommended for custom function property lemmas)

**Real example from practice:**
```lean
-- Without @[fun_prop]: manual proof needed
have h : Measurable (fun ω ↦ f (ω (-1))) := by
  exact hf_meas.comp (measurable_pi_apply (-1))

-- With @[fun_prop] on component lemmas: automated
have h : Measurable (fun ω ↦ f (ω (-1))) := by
  fun_prop (disch := measurability)
```

#### `grind` - SMT-Style Automation

**What it does:** Combines congruence closure, E-matching, case splitting, and arithmetic/algebraic solvers to close mixed-constraint goals.

**When to reach for it:**
- `simp` normalizes but does not close
- Goal mixes equalities + inequalities + algebraic facts
- Finite-domain reasoning (`Fin`, `Bool`, small enums)

**Baseline usage:**
```lean
example (h1 : a = b) (h2 : b = c) : a = c := by grind
example [CommRing R] [NoZeroDivisors R] (h : x * y = 0) (hx : x ≠ 0) : y = 0 := by grind
example : (5 : Fin 3) = 2 := by grind

-- Typical sequence:
simp only [normalize_defs]
grind
```

**High-value controls (official docs):**
```lean
grind?                       -- suggest a grind call (lemmas/options)
grind [key_lemma1, key_lemma2]      -- add lemmas
grind only [key_lemma1, key_lemma2] -- restrict lemma set
grind [-some_lemma]                  -- exclude one lemma
grind (splits := 0)                  -- disable case splitting
grind (splits := 8)                  -- bound case splitting
grind -splitIte -splitMatch +splitImp
grind -ring                           -- disable ring solver
grind -funCC +revert -reducible       -- newer search/reduction controls
```

**When NOT to use `grind`:**
- Pure rewrites -> `simp`
- Integer-only arithmetic -> `omega`
- Nonlinear arithmetic -> `nlinarith`
- Combinatorial/bit-blasting search -> `bv_decide`

**Notes:**
- Local hypotheses are already in scope for `grind`; avoid passing them redundantly.
- If search explodes, reduce splitting (`splits := 0`) before adding more lemmas.
- For custom automation, register lemmas with `@[grind]` / `@[grind =]` / `@[grind ->]` and use `@[grind_pattern]` only when matching needs manual shaping.

**For full details:** [grind-tactic.md](grind-tactic.md)

## Tactic Combinations

### Common Patterns

**Pattern 1: Simplify then apply**
```lean
by
  simp only [my_defs]
  apply main_lemma
```

**Pattern 2: Cases then simplify each**
```lean
by
  by_cases h : p
  · simp [h]  -- Use h in simplification
  · simp [h]
```

**Pattern 3: Induction with automation**
```lean
by
  induction n with
  | zero => simp
  | succ k ih => simp [ih]; ring
```

**Pattern 4: Destructure and combine**
```lean
by
  obtain ⟨x, hx⟩ := exists_proof
  obtain ⟨y, hy⟩ := another_exists
  exact combined_lemma hx hy
```

**Pattern 5: Work with what you have (avoid rearrangement)**

When library gives `∠ B H C + ∠ H C B + ∠ C B H = π` but you want different order, don't fight commutativity - extract what you need directly:
```lean
have angle_sum : ∠ B H C + ∠ H C B + ∠ C B H = π := angle_add_angle_add_angle_eq_pi C ...
have : ∠ H C B = π - ∠ B H C - ∠ C B H := by linarith [angle_sum]
-- Then substitute known values in calc chain
```

**Pattern 6: by_contra + le_antisymm (squeeze theorem)**

Prove `s ∈ Set.Ioo 0 1` from `s ∈ Set.Icc 0 1` and contradictions at endpoints:
```lean
by_contra hs_not_pos
push_neg at hs_not_pos  -- gives s ≤ 0
have : s = 0 := le_antisymm hs_not_pos hs_ge  -- hs_ge : 0 ≤ s
-- Derive contradiction from s = 0 (e.g., H ≠ A)
```

## Interactive Exploration Commands

Not tactics but essential for development:

```lean
#check expr                    -- Show type
#check @theorem                -- Show with all implicit arguments
#print theorem                 -- Show definition/proof
#print axioms theorem          -- List axioms used
#eval expr                     -- Evaluate (computable only)

-- In tactic mode
trace "Current goal: {·}"

-- Debug instance synthesis
set_option trace.Meta.synthInstance true in
theorem my_theorem : Goal := by apply_instance
```

## Tactic Selection Decision Tree

```
What am I trying to do?

├─ Close goal with term I have
│  └─ exact term

├─ Apply lemma but need to prove premises
│  └─ apply lemma

├─ Prove equality
│  ├─ Definitionally equal? → rfl
│  ├─ Need rewrites? → rw [lemmas]
│  ├─ Need normalization? → simp / ring / norm_num
│  └─ Functions equal pointwise? → ext / funext

├─ Split into cases
│  ├─ On decidable prop? → by_cases
│  ├─ On inductive type? → cases / induction
│  └─ Destruct exists/and/or? → rcases / obtain

├─ Prove exists
│  └─ use witness

├─ Prove and
│  └─ constructor (or ⟨proof1, proof2⟩)

└─ Unsure / Complex
   └─ simp? / exact? / apply?  (exploration tactics)
```

## Advanced Patterns

### Calc Mode (Transitive Reasoning)

```lean
calc
  a = b := by proof1
  _ = c := by proof2
  _ = d := by proof3
-- Chains equalities/inequalities
```

### Conv Mode (Rewrite Specific Subterms)

```lean
conv => {
  lhs           -- Focus on left-hand side
  arg 2         -- Focus on 2nd argument
  rw [lemma]    -- Rewrite there
}
```

### Tactic Sequences

```lean
-- Sequential (each line is one tactic)
by
  line1
  line2
  line3

-- Chained with semicolon (all get same tactic)
by constructor <;> simp  -- Apply simp to both goals

-- Focused with bullets
by
  constructor
  · -- First goal
    sorry
  · -- Second goal
    sorry
```
