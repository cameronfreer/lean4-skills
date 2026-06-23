# Common Compilation Errors in Lean 4

This reference provides detailed explanations and fixes for the most common compilation errors encountered in Lean 4 theorem proving.

## Quick Reference Table

| Error | Cause | Fix |
|-------|-------|-----|
| **"failed to synthesize instance"** | Missing type class | Add `haveI : IsProbabilityMeasure μ := ⟨proof⟩` |
| **"maximum recursion depth"** | Type class loop/complex search | Provide manually: `letI := instance` or increase: `set_option synthInstance.maxHeartbeats 40000` |
| **WHNF/isDefEq timeout** (500k+ heartbeats) | Complex function in polymorphic goal | **[performance-optimization.md](performance-optimization.md)** - use `@[irreducible]` wrapper |
| **"type mismatch"** (has type ℕ but expected ℝ) | Wrong type | Use coercion: `(x : ℝ)` or `↑x` |
| **"expected Filter got Measure"** | Dot notation namespace confusion | Use standalone: `EventuallyEq.lemma h` not `h.EventuallyEq.lemma` |
| **"numerals are data but expected Prop"** | Value where proof expected | Use proof term: `tendsto_const_nhds` not `1` |
| **"tactic 'exact' failed"** | Goal/term type mismatch | Use `apply` for unification or restructure: `⟨h.2, h.1⟩` |
| **"unknown identifier"** | Missing import OR namespace not opened | Import tactic OR `open Filter Topology` |
| **"unexpected token/identifier"** | Section comment in proof | Replace `/-! -/` with `--` in tactic mode |
| **"no goals to be solved"** | Tactic already finished | Remove redundant tactics after `simp` |
| **"equation compiler failed"** | Can't prove termination | Add `termination_by my_rec n => n` clause |
| **"synthesized: m, inferred: inst✝"** | Instance pollution (sub-σ-algebras) | ⚡ **READ [instance-pollution.md](instance-pollution.md)** - pin ambient first! |
| **"binder x doesn't match goal's binder ω"** | Alpha/beta-equivalence issue | Use `set F := <expr> with hF`, apply to `F`, unfold with `simpa [hF]` |
| **Error at line N** | Actual error before line N | Check 5-10 lines before reported location |

---

## ⚡ WORKING WITH SUB-σ-ALGEBRAS?

**If you're defining multiple `MeasurableSpace` instances (sub-σ-algebras), STOP and read this first:**

**📚 [instance-pollution.md](instance-pollution.md)** - Essential guide to prevent:
- **Subtle bugs:** Lean picks wrong instance (even from outer scopes!)
- **Timeout errors:** 500k+ heartbeat explosions
- **Cryptic errors:** "synthesized: m, inferred: inst✝⁴"

**Quick fix:** Pin ambient instance BEFORE defining sub-σ-algebras (see [instance-pollution.md](instance-pollution.md) for details).

---

## Detailed Error Explanations

### 1. Failed to Synthesize Instance

**Full error message:**
```
failed to synthesize instance
  IsProbabilityMeasure μ
```

**What it means:** Lean cannot automatically infer the required type class instance.

**Common scenarios:**
- Working with sub-σ-algebras: `m ≤ m₀` but Lean can't infer instances on `m`
- Trimmed measures: `μ.trim hm` needs explicit `SigmaFinite` instance
- Conditional expectations requiring multiple measure properties

**Solutions:**

**Pattern 1: Explicit instance declaration**
```lean
haveI : IsProbabilityMeasure μ := ⟨measure_univ⟩
haveI : IsFiniteMeasure μ := inferInstance
haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
```

**Pattern 2: Using Fact for inequalities**
```lean
have h_le : m ≤ m₀ := ...
haveI : Fact (m ≤ m₀) := ⟨h_le⟩
```

**Pattern 3: Explicit instance passing**
```lean
@condExp Ω ℝ m₀ m (by exact inst) μ (by exact hm) f
```

**Pattern 4: Exclude unwanted section variables**
```lean
-- When section has `variable [MeasurableSpace Ω]` but lemma doesn't need it
omit [MeasurableSpace Ω] in
/-- Docstring for the lemma -/
lemma my_lemma : Statement := by
  proof
```
- **Must appear before the docstring** (not after)
- Common when section variables cause unwanted instance requirements
- Can omit multiple: `omit [inst1] [inst2] in`

**⚡ CRITICAL for sub-σ-algebras:** If working with multiple `MeasurableSpace` instances, **read [instance-pollution.md](instance-pollution.md) FIRST** to avoid subtle bugs and timeout errors!

**For deep patterns with sub-σ-algebras, conditional expectation, and measure theory type class issues, see:** [measure-theory.md](measure-theory.md)

**Debug with:**
```lean
set_option trace.Meta.synthInstance true in
theorem my_theorem : Goal := by
  apply_instance
```

### 2. Maximum Recursion Depth

**Full error message:**
```
(deterministic) timeout at 'typeclass', maximum number of heartbeats (20000) has been reached
```

**What it means:** Type class synthesis is stuck in a loop or the search is too complex.

**Common causes:**
- Circular instance dependencies
- Very deep instance search trees
- Ambiguous instances competing

**Solutions:**

**Solution 1: Provide instance manually**
```lean
letI : MeasurableSpace Ω := m₀  -- Freeze the instance
-- Now Lean won't search
```

**Solution 2: Increase search limit**
```lean
set_option synthInstance.maxHeartbeats 40000 in
theorem my_theorem : Goal := ...
```

**Solution 3: Check for instance loops**
```lean
-- ❌ WRONG: Creates loop
instance [Foo A] : Bar A := ...
instance [Bar A] : Foo A := ...

-- ✅ CORRECT: One-directional
instance [Foo A] : Bar A := ...
```

### 3. Type Mismatch

**Full error message:**
```
type mismatch
  x
has type
  ℕ
but is expected to have type
  ℝ
```

**What it means:** The term's type doesn't match what's expected.

**Common scenarios:**
- Natural number used where real number expected
- Integer used where rational expected
- General coercion needed

**Solutions:**

**Pattern 1: Explicit coercion**
```lean
-- Natural to real
(n : ℝ)  -- Preferred
↑n       -- Alternative

-- Integer to real
(z : ℝ)

-- Custom coercion
⟨x, hx⟩ : {x : ℝ // x > 0}
```

**Pattern 2: Check actual types**
```lean
#check x        -- See current type
#check (x : ℝ)  -- Verify coercion works
```

**Pattern 3: Function application**
```lean
-- If f : ℝ → ℝ and n : ℕ
f ↑n    -- Apply after coercion
f (n : ℝ)  -- Explicit
```

**Pattern 4: Bypass coercion unification with calc**

When automatic coercion `(π/6 : Real.Angle)` won't unify with explicit `((π/6 : ℝ) : Real.Angle)`, use calc chain with coercion-free middle steps:
```lean
calc ((Real.pi / 6 : ℝ) : Real.Angle)
    = ∠ A C H := by rw [← h_angle]  -- Explicit coercion matches helper signature
  _ = ∠ A C B := by simp [h_eq]      -- Pure angle equality (no coercion!)
  _ = ((4 * Real.pi / 9 : ℝ) : Real.Angle) := by rw [angle_ACB]
```

### 4. Tactic 'exact' Failed

**Full error message:**
```
tactic 'exact' failed, type mismatch
  term
has type
  A → B
but is expected to have type
  ∀ x, A x → B x
```

**What it means:** The term's type is close but not exactly the goal type.

**Solutions:**

**Solution 1: Use apply instead**
```lean
-- exact doesn't work but apply might
apply my_lemma
-- Leaves subgoals to fill
```

**Solution 2: Restructure term**
```lean
-- Wrong order
exact ⟨h.1, h.2⟩  -- Type mismatch

-- Correct order
exact ⟨h.2, h.1⟩  -- Works
```

**Solution 3: Add intermediate steps**
```lean
-- Instead of: exact complex_term
have h1 := part1
have h2 := part2
exact ⟨h1, h2⟩
```

### 5. Unknown Identifier (Missing Tactic or Namespace Open)

**Full error message:**
```
unknown identifier 'ring'
unknown identifier 'Tendsto'
```

**What it means:** Tactic not imported OR namespace not opened.

**Cause 1: Missing tactic import**

**Common missing imports:**
```lean
import Mathlib.Tactic.Ring          -- ring, ring_nf
import Mathlib.Tactic.Linarith      -- linarith, nlinarith
import Mathlib.Tactic.FieldSimp     -- field_simp
import Mathlib.Tactic.Continuity    -- continuity
import Mathlib.Tactic.Measurability -- measurability
import Mathlib.Tactic.Positivity    -- positivity
```

**Quick fix:**
1. See error for tactic name
2. Add `import Mathlib.Tactic.TacticName`
3. Rebuild

**Cause 2: Missing `open` declarations**

Names like `Tendsto` and `atTop` live in the `Filter` namespace. Without opening it, Lean cannot resolve them:

```lean
-- ❌ WRONG: bare identifiers without open
have h : Tendsto f atTop (𝓝 x) := ...

-- ✅ CORRECT: open the relevant namespaces
open Filter Topology in
have h : Tendsto f atTop (𝓝 x) := ...
```

Alternatively, you can fully qualify the names (`Filter.Tendsto`, `Filter.atTop`), but `open Filter Topology` is the standard mathlib practice.

### 6. Equation Compiler Failed (Termination)

**Full error message:**
```
fail to show termination for
  my_recursive_function
with errors
  ...
```

**What it means:** Lean can't automatically prove the function terminates.

**Solutions:**

**Pattern 1: Add termination_by clause**
```lean
def my_rec (n : ℕ) : ℕ :=
  if n = 0 then 0
  else my_rec (n - 1)
termination_by n  -- Decreasing argument
```

**Pattern 2: Well-founded recursion**
```lean
def my_rec (l : List α) : Result :=
  match l with
  | [] => base_case
  | h :: t => combine h (my_rec t)
termination_by l.length
```

**Pattern 3: Use sorry for termination proof**
```lean
def my_rec (x : X) : Y := ...
termination_by measure_func x
decreasing_by sorry  -- TODO: Prove later
```

### 7. Unsolved Goals (Nat.pos_of_ne_zero and Arithmetic)

**Full error message:**
```
unsolved goals
h : m ≠ 0
h2 : (4 : ℝ) / ε ≤ ↑m
⊢ False
```

**What it means:** After introducing a contradiction hypothesis, the goal is `False` but the tactic can't derive the contradiction.

**Common scenario:** Proving `m > 0` from `m ≠ 0` and some bound, but `norm_num` fails because the expressions are symbolic (not concrete numbers).

**Why norm_num fails:**
- `norm_num` works on **concrete numerical expressions** (like `2 + 2 = 4`)
- When you have symbolic variables like `4/ε`, `norm_num` can't evaluate them
- After `rw [h]` where `h : m = 0`, you get `4/ε ≤ 0`, but `norm_num` can't derive `False` from this

**Solution: Use simp to eliminate variables, then linarith**

```lean
-- ❌ WRONG: norm_num can't solve symbolic arithmetic
have hm_pos' : m > 0 := Nat.pos_of_ne_zero (by
  intro h
  rw [h] at h2  -- Now h2 : 4/ε ≤ 0
  norm_num at h2  -- FAILS: can't derive False because 4/ε is symbolic
  )
-- Error: unsolved goals ⊢ False

-- ✅ CORRECT: simp eliminates the variable, then linarith
have hm_pos' : m > 0 := Nat.pos_of_ne_zero (by
  intro h
  simp [h] at h2  -- Now h2 : 4/ε ≤ 0 AND we eliminated m entirely
  have : (4 : ℝ) / ε > 0 := by positivity  -- Explicit positivity proof
  linarith)  -- Can now derive contradiction: 0 < 4/ε ≤ 0
```

**Key insight:**
- `norm_num` = numerical normalization (concrete numbers)
- `simp` = simplification (eliminates variables, unfolds definitions)
- `linarith` = linear arithmetic solver (works with inequalities and symbolic expressions)

**General pattern for contradiction proofs:**
1. `simp [hypothesis]` to eliminate the contradictory assumption
2. Establish any needed positivity facts with `positivity`
3. `linarith` to derive the contradiction from inequalities

**When to use each tactic:**
- `norm_num`: Concrete arithmetic (`2 + 2 = 4`, `7 < 10`)
- `simp`: Simplify using hypotheses and definitions
- `linarith`: Linear inequalities with variables (`a + b ≤ c`, `x > 0 → x + 1 > 0`)
- `omega`: Integer linear arithmetic (works on `ℕ` and `ℤ`)

### 8. Unexpected Token/Identifier in Proof (Section Doc Comments)

**Full error message:**
```
unexpected identifier; expected command
unexpected token 'have'; expected command
```

**What it means:** Section doc comments `/-! ... -/` in tactic mode can terminate proof parsing.

**CRITICAL:** Section doc comments terminate proof context, causing everything after to be interpreted as top-level declarations.

```lean
-- ❌ WRONG: Section comments break proof
lemma my_proof := by
  classical
  set mW := ... with hmW

  /-! ### Step 0: documentation -/

  set φp := ... with hφp  -- ERROR: unexpected identifier
  have h := ...           -- ERROR: unexpected token 'have'

-- ✅ CORRECT: Use regular comments
lemma my_proof := by
  classical
  set mW := ... with hmW
  -- Step 0: documentation
  set φp := ... with hφp  -- ✓ Works
  have h := ...           -- ✓ Works
```

**Best practice:** Use `--` for in-proof comments, reserve `/-! -/` for top-level documentation only.

### 9. Variable Shadowing in Lambda

**Full error message:**
```
type mismatch
  a
has type
  Set ℝ≥0∞
but is expected to have type
  α
```

**What it means:** Lambda variable shadows outer variable, causing type confusion.

```lean
-- ❌ WRONG: 'a' in lambda shadows outer 'a'
have h_sp_le : ∀ n a, (sp n a) ≤ φp a := by
  intro n a
  have := SimpleFunc.iSup_eapprox_apply
    (fun a => ENNReal.ofReal (max (φ a) 0))  -- 'a' shadows!
    ... a  -- ERROR: which 'a'?

-- ✅ CORRECT: Rename lambda variable or add type annotation
have h_sp_le : ∀ n a, (sp n a) ≤ φp a := by
  intro n a
  have := SimpleFunc.iSup_eapprox_apply
    (fun (x : α) => ENNReal.ofReal (max (φ x) 0))
    ... a  -- ✓ Clear: outer 'a'
```

**Prevention:** Use different variable names in nested lambdas or add explicit type annotations.

### 10. No Goals After Tactic

**Full error message:**
```
no goals to be solved
```

**What it means:** Previous tactic already completed the proof, but another tactic remains.

```lean
-- ❌ WRONG: simp already solved goal
have hφp_nn : ∀ a, 0 ≤ φp a := by
  intro a
  simp [φp]
  exact le_max_right _ _  -- ERROR: no goals left

-- ✅ CORRECT: Remove redundant tactic
have hφp_nn : ∀ a, 0 ≤ φp a := by
  intro a
  simp [φp]  -- ✓ simp completes proof
```

**Debug:** Check goal state after each tactic. If "no goals" appears, proof is done.

## Quick Debug Workflow

When encountering any error:

1. **Read error location carefully** - Often points to exact issue
2. **Use #check** - Verify types of all terms involved
3. **Simplify** - Try to create minimal example that fails
4. **Search mathlib** - Error might be documented in lemma comments
5. **Ask Zulip** - Lean community is very helpful

### Quick Checklist for "Unexpected" Errors in Proofs

When facing "unexpected identifier/token" in long proofs:

1. ☐ Search for `/-! ... -/` section comments → replace with `--`
2. ☐ Check for bare identifiers (`Tendsto`, `atTop`) → `open Filter Topology`
3. ☐ Look for lambda shadowing → rename variables or add type annotations
4. ☐ Check for "no goals" after `simp` → remove redundant tactics
5. ☐ For section variables + explicit params → rely on section, use `(by infer_instance)`
6. ☐ For sub-σ-algebra work → ensure `hmW_le : mW ≤ _` proof exists

---

## Additional Common Errors

### 9. Dot Notation Namespace Confusion

**Error message:**
```
type mismatch
  expected Filter
  got Measure
```

**What it means:** You're using dot notation for a lemma name that conflicts with a type constructor.

**Example:**
```lean
-- ❌ WRONG: Interpreted as EventuallyEq constructor call
have := h.EventuallyEq.comp_measurePreserving
--        ^ EventuallyEq constructor called with μ as first argument
--          Expected Filter but got Measure
```

**Solution:** Use snake_case standalone names instead of dot notation:

```lean
-- ✅ CORRECT: Call the lemma function
have := EventuallyEq.comp_measurePreserving h ...
```

**Pattern:** If you see type errors where:
- A `Measure` is expected to be a `Filter`
- A `Set` is expected to be a different type
- "Expected X but got Y" for completely unrelated types

Check if you're using dot notation for a lemma that shares a name with a type constructor.

**Rule:** For private helper lemmas extending common type names (`EventuallyEq`, `Tendsto`, `Continuous`, etc.), use standalone function call syntax, not dot notation.

### 10. Numerals in Propositional Contexts

**Error message:**
```
numerals are data but expected type is Prop
```

**What it means:** You're passing a value (numeral) where a proof term is expected.

**Example:**
```lean
-- ❌ WRONG: 1 is a numeral (data), not a proof
have := h1.atTop_add 1
--                    ^ Expected: Tendsto proof
--                      Got: numeral 1
```

**Solution:** For constant function limits, use `tendsto_const_nhds`:

```lean
-- ✅ CORRECT: Pass a proof term
have := h1.atTop_add (tendsto_const_nhds : Tendsto (fun _ => (1 : ℝ)) atTop (nhds 1))
```

**Pattern:** Functions like `atTop_add` work on limits and need proof terms:
- `Tendsto f atTop (nhds a)` ← This is a Prop (needs proof)
- `1` ← This is data (ℕ or ℝ)

**Common fixes:**
```lean
-- For constant functions
tendsto_const_nhds : Tendsto (fun _ => c) filter (nhds c)

-- For simple expressions
use lemmas like Filter.tendsto_id, Filter.tendsto_const_pure
```

### 11. Error Location Can Be Misleading

**Problem:** Lean reports errors where elaboration fails, not always where the mistake is.

**Example:**
```
error: type mismatch at line 4238
```
But the actual mistake is at line 4231.

**Why:** Elaborator processes code sequentially and reports failure at the point where it can't continue, which may be several lines after the actual error.

**Strategy:**

**When investigating an error:**
1. Read 5-10 lines **before** the reported location
2. Look for recent changes (especially new `let` bindings, `have` statements, or tactic calls)
3. Check for missing hypotheses or incorrect variable names
4. Verify that all previous lines actually compile in isolation

**Example workflow:**
```lean
-- Error reported at line 4238
-- Start reading from line 4228-4230

-- Line 4231: Ah! Wrong variable name here
let μX := pathLaw μ X  -- Should be Y not X

-- Lines 4232-4237: These all assumed μX was correct
-- Line 4238: Where elaboration finally failed
```

**Pattern:** The mistake is often in:
- Most recent `let` or `have` before error (wrong RHS)
- Most recent tactic (applied wrong lemma)
- Missing hypothesis from 2-5 lines before

**Don't:** Assume the error line is where you need to fix.
**Do:** Trace backwards from error to find the root cause.

### 12. Alpha/Beta-Equivalence Issues (Binder Mismatches)

**Problem:** Lean fails to match expressions because binder names differ (α-equivalence) or beta-redexes aren't reduced.

**Error message:**
```
tactic 'simp' failed
  binder x doesn't match goal's binder ω
```

**Example failure:**
```lean
have h := integral_condExp (f := fun ω => μ[g|m] ω * ξ ω)
-- h : ∫ (x : Ω), F x ∂μ = ∫ (x : Ω), μ[F|m] x ∂μ
-- Goal: ∫ (ω : Ω), μ[g|m] ω * ξ ω ∂μ = ...

simpa using h.symm  -- Error: binder x ≠ binder ω
```

**Why it fails:** Lean doesn't automatically recognize that `fun x => F x` and `fun ω => F ω` are the same when comparing goal to hypothesis.

**Solution: Use `set ... with` pattern to name expression once**

```lean
-- Name the integrand once and for all
set F : Ω → ℝ := fun ω => μ[g | m] ω * ξ ω with hF

-- Apply lemma to named function F
have h_goal :
    ∫ (ω : Ω), μ[g | m] ω * ξ ω ∂μ
  = ∫ (ω : Ω), μ[(fun ω => μ[g | m] ω * ξ ω) | m] ω ∂μ := by
  simpa [hF] using
    (MeasureTheory.integral_condExp (μ := μ) (m := m) (hm := hm) (f := F)).symm

exact h_goal.symm
```

**Why this works:**
- `set F := ...` gives the expression an explicit name
- Lean never compares different lambda expressions
- `simpa [hF]` unfolds `F` uniformly in both places
- No binder name mismatches because we use the same name throughout

**Pattern:**
1. `set F := <complex expr> with hF`
2. Apply lemma to the named `F`
3. Unfold with `simpa [hF]` or `rw [hF]`

**See also:** [lean-phrasebook.md](lean-phrasebook.md) - "Name complex expression to avoid alpha/beta-equivalence issues"

---

## Type Class Debugging Commands

```lean
-- See synthesis trace
set_option trace.Meta.synthInstance true in
theorem test : Goal := by apply_instance

-- See which instance was chosen
#check (inferInstance : IsProbabilityMeasure μ)

-- Check all implicit arguments
#check @my_lemma
```

## Common Patterns to Avoid

### ❌ Fighting the Type Checker

```lean
-- Repeatedly trying variations until something compiles
exact h
exact h.1
exact ⟨h⟩
exact (h : _)  -- Guessing
```

### ✅ Understanding Then Fixing

```lean
#check h  -- See what h actually is
#check goal  -- See what's needed
-- Now fix systematically
```

### ❌ Ignoring Error Messages

```lean
-- "It says type mismatch, let me try random things"
```

### ✅ Reading Carefully

```lean
-- Error says "has type A but expected B"
-- Solution: Convert A to B or restructure
```

---

## Build Log Capture

For debugging persistent build errors, capture the full log for inspection:

### Basic Capture

```bash
LOG=$(mktemp -t lean4_build_XXXXXX.log)
lake build 2>&1 | tee "$LOG"

# Quick scans
tail -n 120 "$LOG"
rg -n "error|warning|failed" "$LOG"
```

### With Git Hash (Conflict-Safe)

```bash
HASH=$(git rev-parse --short HEAD 2>/dev/null || date +%s)
LOG="/tmp/lean4_build_${HASH}_$RANDOM.log"
lake build 2>&1 | tee "$LOG"
```

**Benefits:**
- Preserves logs across rebuilds for comparison
- Avoids filename clashes between runs
- Enables grep without rebuilding
- Links log to specific commit state

**See also:** [Repair Mode](../../../commands/prove.md#repair-mode) for escalation-only repair policy.
