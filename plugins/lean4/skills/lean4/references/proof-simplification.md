# Proof Simplification

Guide for simplifying Lean 4 proofs by finding better proof strategies, leveraging mathlib, and extracting domain-specific helpers. Complements [proof-refactoring.md](proof-refactoring.md) (which covers structural extraction) and [proof-golfing.md](proof-golfing.md) (which covers tactic-level optimization).

## Overview

Proof simplification operates at the *strategy* level:
- **Refactoring** asks: "How do I break this proof into pieces?"
- **Golfing** asks: "How do I write these tactics more concisely?"
- **Simplification** asks: "Is there a fundamentally better way to prove this?"

## Quick Decision Tree

```
Proof seems too long or complex
├─ Is it doing something "basic" in 20+ lines?
│   ├─ Search mathlib — the lemma probably exists
│   │   ├─ Found it → Apply directly (Strategy 1)
│   │   └─ Not found → State in mathlib-ready generality (Strategy 3)
│   └─ Still hard → Definition might be fighting you (Strategy 5)
├─ Same pattern appears 2+ times?
│   └─ Extract helper in maximum generality (Strategy 2)
├─ Proof has a complex case split?
│   └─ Search for a `congr`/`EqOn`/`EventuallyEq` approach (Strategy 4)
├─ Proof manually threads through a definition?
│   └─ Search for a lemma about the definition (Strategy 1)
└─ Proof is inherently complex, just long?
    └─ Use [proof-refactoring.md](proof-refactoring.md) instead
```

---

## Strategy 1: Replace with Mathlib Lemmas

The single highest-impact simplification: finding that mathlib already has what you need.

### Search Protocol

For a proof block establishing `P`, search in this order:

1. **Exact name search** — if you suspect a name:
   ```
   lean_local_search("ContinuousOn.congr")
   ```

2. **Natural language search** — describe what the proof establishes:
   ```
   lean_leansearch("piecewise function continuous on locally finite closed cover")
   lean_leansearch("floor equals n when value is in Ico n n+1")
   ```

3. **Type-pattern search** — when you know the type signature:
   ```
   lean_loogle("LocallyFinite ?f → (∀ i, IsClosed (?f i)) → ContinuousOn ?g _")
   lean_loogle("?a ∈ Set.Ico ?n (?n + 1) → Nat.floor ?a = ?n")
   ```

4. **Goal-conditioned search** — when you have an open goal:
   ```
   lean_leanfinder("the goal state or its informal description")
   lean_state_search(file, line, col)
   ```

5. **Module exploration** — check what's near a related lemma:
   ```
   lean_local_search("Nat.floor_eq")  -- find all floor_eq variants
   ```

### What to Search For

| Proof Pattern | Search For |
|---------------|-----------|
| Continuity of piecewise function | `LocallyFinite.continuousOn_iUnion`, `ContinuousOn.union_of_isClosed`, `ContinuousOn.if` |
| Derivative of a function that equals another | `HasDerivWithinAt.congr_of_eventuallyEq`, `HasDerivAt.congr` |
| Continuity of a function that equals another | `ContinuousOn.congr`, `ContinuousWithinAt.congr_of_eventuallyEq` |
| Floor/ceil equals specific value | `Nat.floor_eq_on_Ico`, `Int.floor_eq_iff` |
| Interval membership from floor | `Nat.floor_le`, `Nat.lt_floor_add_one` |
| Lipschitz/bound transfer | `LipschitzWith.dist_le_mul`, `LipschitzOnWith` |
| Gronwall-style bounds | `dist_le_of_approx_trajectories_ODE`, `gronwallBound` |
| Affine map properties | `hasDerivAt_id`, `HasDerivAt.smul_const`, `HasDerivAt.const_add` |
| Filter membership | `Ioo_mem_nhdsGT`, `Ico_mem_nhdsGE`, `filter_upwards` |
| Set equality on interval | `Set.EqOn`, `Set.EqOn.eventuallyEq_nhdsWithin` |

### Example: Continuity via `ContinuousOn.congr`

**Before (35 lines):** Prove continuity of `eulerPath` on `[tn, t_{n+1}]` by case-splitting on interior points, left endpoint, and right endpoint, proving each case separately.

**After (8 lines):** Show `eulerPath` equals an affine function on the interval (`Set.EqOn`), then transfer continuity via `ContinuousOn.congr`:
```lean
suffices h_eq : Set.EqOn (eulerPath v h t0 y0) f (Set.Icc tn t_{n+1}) from
  (by fun_prop : ContinuousOn f _).congr h_eq
```

**Key insight:** `ContinuousOn.congr` takes `ContinuousOn f s` and `EqOn g f s` to give `ContinuousOn g s`. Direction matters: `EqOn` goes from the *new* function to the *known-continuous* function.

### Example: Derivative via `congr_of_eventuallyEq`

**Before (15 lines):** Manually compute derivative by unfolding `eulerPath`, simplifying floor, and assembling pieces.

**After (10 lines):** Show `eulerPath` agrees with an affine map eventually, take the affine map's derivative (a single `HasDerivAt` chain), and transfer:
```lean
have h_affine : HasDerivAt (fun t' => yn + (t' - tn) • c) ((1 : ℝ) • c) t :=
  hasDerivAt_id t |>.sub_const tn |>.smul_const c |>.const_add yn
-- ... show eventuallyEq ...
exact h_affine.hasDerivWithinAt.congr_of_eventuallyEq h_eq h_val.symm
```

---

## Strategy 2: Extract Repeated Patterns as Helpers

When the same proof pattern appears 2+ times with different arguments, extract it.

### Identification

Look for:
- Same `rw`/`simp` lemma sequence with different arguments
- Same `nlinarith`/`linarith` argument structure
- Same definitional unfolding followed by the same simplification
- Same combination of `Nat.floor_eq_iff` + `div_le_iff` + `nlinarith`

### Extraction Protocol

1. **Find the common core** — what mathematical fact is being proved each time?
2. **State it as a standalone lemma** with the most general hypotheses
3. **Name it after what it proves**, not where it's used
4. **Place it before first use**

### Example: `floor_eq_of_mem_Ico`

**Pattern found in 4 places:**
```lean
-- Each time, manually proving ⌊(t-t0)/h⌋₊ = n from t ∈ Ico
have : ⌊(t - t0) / h⌋₊ = n := by
  apply Nat.floor_eq_iff (by positivity) |>.mpr
  constructor
  · rw [le_div_iff₀ h_pos]; linarith [ht.1]
  · rw [div_lt_iff₀ h_pos]; linarith [ht.2]
```

**Extracted helper:**
```lean
private theorem floor_eq_of_mem_Ico (h_pos : 0 < h) (t0 : ℝ) (n : ℕ) (t : ℝ)
  (ht : t ∈ Set.Ico (t0 + n * h) (t0 + (n + 1) * h)) :
  ⌊(t - t0) / h⌋₊ = n :=
  Nat.floor_eq_on_Ico n _ ⟨by rw [le_div_iff₀ h_pos]; linarith [ht.1],
    by rw [div_lt_iff₀ h_pos]; linarith [ht.2]⟩
```

**Impact:** 4 proof sites reduced to single-line applications.

### Generalization Checklist

When extracting, ask:
- **Weaker hypotheses?** Can `=` become `≤`? Can `Fin n` become `ℕ`?
- **Fewer assumptions?** Does the proof actually use all hypotheses?
- **More general types?** Can `ℝ` become `[LinearOrderedField α]`?
- **Mathlib-ready?** Would this be useful in mathlib? If so, state it in mathlib conventions.

---

## Strategy 3: Identify Missing Mathlib Lemmas

Sometimes the right lemma doesn't exist in mathlib. Recognizing this is valuable — it means you should state the lemma in proper generality and potentially contribute it.

### Signs of a Missing Lemma

1. **20+ lines to prove something "obvious"** — e.g., floor computation from interval membership
2. **Same proof repeated across multiple projects** — community need
3. **Proof requires only basic library infrastructure** — doesn't depend on advanced theory
4. **Natural place in the library** — fits cleanly in an existing module

### What to Do

1. **State it in maximum generality** — use the most general typeclasses
2. **Follow mathlib naming conventions** — `Nat.floor_eq_of_mem_Ico`, not `my_floor_helper`
3. **Add a docstring** explaining what it does
4. **Note it for a PR** — record in the refactoring report
5. **Use it locally** with a `private` version for now

### Example

**Observation:** Proving `⌊(t-t0)/h⌋₊ = n` from `t ∈ Ico (t0 + n*h) (t0 + (n+1)*h)` requires ~5 lines every time. Mathlib has `Nat.floor_eq_on_Ico` for the simple case `a ∈ [n, n+1)`, but not for the shifted/scaled case.

**Local helper (project-specific):**
```lean
private theorem floor_eq_of_mem_Ico (h_pos : 0 < h) ...
```

**Potential mathlib lemma (general):**
```lean
theorem Nat.floor_eq_of_mem_Ico_smul [LinearOrderedField α] [FloorSemiring α]
  {h : α} (h_pos : 0 < h) {a : α} {n : ℕ}
  (ha : a ∈ Set.Ico (n * h) ((n + 1) * h)) : ⌊a / h⌋₊ = n
```

---

## Strategy 4: Replace Case Splits with Congr Lemmas

Many proofs case-split where a `congr`-style lemma would be cleaner.

### Pattern: Case Split on Function Equality

**Before:**
```lean
-- Prove f is continuous by showing it equals g at every point via cases
intro t ht
rcases eq_or_lt_of_le ht.2 with rfl | h_lt
· -- Right endpoint case
  [10 lines]
· rcases eq_or_lt_of_le ht.1 with rfl | h_gt
  · -- Left endpoint case
    [8 lines]
  · -- Interior case
    [5 lines]
```

**After:**
```lean
-- Show f = g on the whole set, transfer continuity
suffices h_eq : Set.EqOn f g s from (hg_cont.congr h_eq)
intro t ht
-- Unified proof (often much shorter)
```

### Pattern: Derivative via EventuallyEq

**Before:** Manually differentiate a piecewise function by unfolding, simplifying floor, assembling.

**After:** Show the function agrees with a known-differentiable function eventually, transfer:
```lean
have h_eq : f =ᶠ[nhdsWithin t s] g := by
  filter_upwards [some_neighborhood_lemma] with x hx
  exact function_agrees_on_interval x hx
exact (h_deriv_g.congr_of_eventuallyEq h_eq h_val).congr_deriv (one_smul _ _)
```

### When Congr Lemmas Help

- Function is defined piecewise but equals something simpler on each piece
- You need continuity/differentiability/measurability of a complex function
- The complex function agrees with a simple one on the relevant set
- Case splits are about matching definitions, not about mathematical content

---

## Strategy 5: Reconsider Definitions

Sometimes the proof is hard because the definition is fighting you.

### Signs

1. **Every proof about `foo` starts with `unfold foo; simp`** — the definition is too opaque
2. **Floor/ceil computations dominate** — the definition uses discretization that makes continuity hard
3. **Same definitional unfolding in every lemma** — the API is too thin

### What to Do

1. **Build the API** — prove the key properties as standalone lemmas (e.g., `eulerPath_eq_on_Ico`)
2. **Consider alternative definitions** — would a different but equivalent definition be easier to work with?
3. **Use `simp` lemmas** — make key equalities available to `simp` so proofs don't need manual unfolding

### Example

The `eulerPath` definition uses `Nat.floor`, making every proof fight with floor arithmetic. Solution: prove `eulerPath_eq_on_Ico` (explicit formula on each interval) and `eulerPath_grid_point` (values at grid points) as the primary API, then never unfold `eulerPath` directly.

---

## Cross-Cutting Analysis

When analyzing a whole file, look for patterns that span multiple proofs.

### File-Level Audit Checklist

1. **Grep for repeated tactic sequences:**
   - Same `rw [lemma1, lemma2]; simp` appearing 3+ times
   - Same `nlinarith` with similar auxiliary hypotheses
   - Same `unfold foo; simp [bar]` pattern

2. **Check proof lengths:**
   - Any proof > 30 lines → candidate for simplification
   - Any proof > 60 lines → strong candidate
   - Multiple 15-line proofs with same structure → extract helper

3. **Check for hand-rolled basics:**
   - Continuity proofs that don't use `fun_prop`
   - Derivative proofs that don't use `HasDerivAt` chains
   - Arithmetic proofs that don't use `omega`/`positivity`/`norm_num`

4. **Check for overly specific hypotheses:**
   - Can `h : a = b` become `h : a ≤ b`?
   - Can `[NormedSpace ℝ E]` become `[Module ℝ E]`?
   - Can `(n : ℕ)` become `(n : ℤ)` or be removed?

5. **Check API coverage:**
   - Is every proof unfolding a definition directly?
   - Should there be intermediate API lemmas?

### Reporting Format

After analysis, report:

```
## File Analysis: ForwardEuler/main.lean

### Repeated Patterns (extract as helpers)
1. ⌊(t-t0)/h⌋₊ = n from Ico membership — appears 4x (lines 89, 119, 155, 198)
   → Extract `floor_eq_of_mem_Ico`

2. t ∈ Ico tn t_{n+1} from t ≥ t0 — appears 2x (lines 128, 222)
   → Extract `mem_Ico_floor`

### Strategy Improvements (use better mathlib lemmas)
1. eulerPath_continuousOn_Icc (line 104): case-splitting on endpoints
   → Use ContinuousOn.congr + EqOn (saves ~20 lines)

2. eulerPath_continuous (line 124): manual cover + finiteness
   → Use LocallyFinite.continuousOn_iUnion (cleaner structure)

3. eulerPath_hasDerivWithinAt (line 149): manual derivative calculation
   → Use HasDerivAt chain + congr_of_eventuallyEq (saves ~5 lines)

### Potential Mathlib Contributions
1. `floor_eq_of_mem_Ico` — general enough for Mathlib.Order.FloorSemiring

### Estimated Impact
- Lines before: 310
- Lines after: ~245
- Helpers extracted: 2
- Mathlib lemmas newly applied: 4
```

---

## See Also

- [proof-refactoring.md](proof-refactoring.md) — Structural refactoring (breaking proofs into helpers)
- [proof-golfing.md](proof-golfing.md) — Tactic-level optimization
- [mathlib-guide.md](mathlib-guide.md) — How to search mathlib
- [mathlib-style.md](mathlib-style.md) — Naming conventions for potential mathlib contributions
- [lean-phrasebook.md](lean-phrasebook.md) — Math-to-Lean translations for search queries
