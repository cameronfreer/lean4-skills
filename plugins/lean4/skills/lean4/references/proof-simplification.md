# Proof Simplification

Guide for simplifying Lean 4 proofs at the *strategy* level: finding fundamentally better proof approaches, leveraging mathlib, and extracting reusable helpers. Complements [proof-refactoring.md](proof-refactoring.md) (structural extraction) and [proof-golfing.md](proof-golfing.md) (tactic-level optimization).

## Quick Decision Tree

```
Proof seems too long or complex
├─ Is it doing something "basic" in 20+ lines?
│   ├─ Search mathlib — the lemma probably exists (→ Replace with Mathlib)
│   │   └─ Not found → State in mathlib-ready generality (→ Missing Lemmas)
│   └─ Still hard → Definition might be fighting you (→ Reconsider Definitions)
├─ Same pattern appears 2+ times?
│   └─ Extract helper in maximum generality (→ Extract Helpers)
├─ Proof has a complex case split?
│   └─ Search for a congr/EqOn/EventuallyEq approach (→ Congr Lemmas)
├─ Proof manually threads through a definition?
│   └─ Search for a lemma about the definition (→ Replace with Mathlib)
└─ Proof is inherently complex, just long?
    └─ Use [proof-refactoring.md](proof-refactoring.md) instead
```

---

## Replace with Mathlib Lemmas

The single highest-impact simplification. For search protocol details, see [mathlib-guide.md](mathlib-guide.md) and [lean-lsp-tools-api.md](lean-lsp-tools-api.md).

### Common Patterns Worth Searching

| Proof Pattern | Mathlib Lemmas to Search |
|---------------|-----------|
| Continuity of piecewise function | `ContinuousOn.if`, `ContinuousOn.union_of_isClosed`, `LocallyFinite.continuousOn_iUnion` |
| Property of a function that equals another on a set | `ContinuousOn.congr`, `HasDerivWithinAt.congr_of_eventuallyEq`, `Measurable.congr` |
| Floor/ceil equals specific value | `Nat.floor_eq_on_Ico`, `Int.floor_eq_iff` |
| Lipschitz/bound transfer | `LipschitzWith.dist_le_mul`, `LipschitzOnWith` |
| Filter membership | `Ioo_mem_nhdsGT`, `Ico_mem_nhdsGE`, `filter_upwards` |
| Set equality on interval | `Set.EqOn`, `Set.EqOn.eventuallyEq_nhdsWithin` |

---

## Replace Case Splits with Congr Lemmas

Many proofs case-split where a `congr`-style lemma would be cleaner.

### Pattern: Transfer via `Set.EqOn`

**Before:** Prove continuity by case-splitting on endpoints and interior:
```lean
intro t ht
rcases eq_or_lt_of_le ht.2 with rfl | h_lt
· -- Right endpoint: [10 lines]
· rcases eq_or_lt_of_le ht.1 with rfl | h_gt
  · -- Left endpoint: [8 lines]
  · -- Interior: [5 lines]
```

**After:** Show function equals a known-continuous function on the set, transfer:
```lean
suffices h_eq : Set.EqOn f g s from (hg_cont.congr h_eq)
intro t ht
-- Unified proof (often much shorter)
```

**Key insight:** `ContinuousOn.congr` takes `ContinuousOn f s` and `EqOn g f s` to give `ContinuousOn g s`. Direction matters: `EqOn` goes from the *new* function to the *known-continuous* function.

### Pattern: Transfer via `EventuallyEq`

**Before:** Manually differentiate a complex function by unfolding and assembling.

**After:** Show the function agrees with a known-differentiable function eventually:
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

## Extract Repeated Patterns as Helpers

When the same proof pattern appears 2+ times with different arguments, extract it.

### Identification

Look for:
- Same `rw`/`simp` lemma sequence with different arguments
- Same `nlinarith`/`linarith` argument structure
- Same definitional unfolding followed by the same simplification

### Extraction Protocol

1. **Find the common core** — what mathematical fact is being proved each time?
2. **State it as a standalone lemma** with the most general hypotheses
3. **Name it after what it proves**, not where it's used
4. **Place it before first use**

### Generalization Checklist

When extracting, ask:
- **Weaker hypotheses?** Can `=` become `≤`? Can `Fin n` become `ℕ`?
- **Fewer assumptions?** Does the proof actually use all hypotheses?
- **More general types?** Can `ℝ` become `[LinearOrderedField α]`?
- **Mathlib-ready?** Would this be useful in mathlib? If so, state it in mathlib conventions (see [mathlib-style.md](mathlib-style.md)).

---

## Identify Missing Mathlib Lemmas

Sometimes the right lemma doesn't exist in mathlib. Recognizing this is valuable.

### Signs

- 20+ lines to prove something "obvious"
- Same proof repeated across multiple projects
- Proof requires only basic library infrastructure
- Natural place in the library (fits cleanly in an existing module)

### What to Do

1. State it in maximum generality (most general typeclasses)
2. Follow mathlib naming conventions (see [mathlib-style.md](mathlib-style.md))
3. Use a `private` version locally for now
4. Note it in the refactoring report for potential contribution

---

## Reconsider Definitions

Sometimes the proof is hard because the definition is fighting you.

### Signs

- Every proof starts with `unfold foo; simp` — definition is too opaque
- Same definitional unfolding in every lemma — API is too thin
- Arithmetic computations dominate — definition uses discretization that makes analysis hard

### What to Do

1. **Build the API** — prove key properties as standalone lemmas
2. **Consider alternative definitions** — would an equivalent definition be easier to work with?
3. **Use `simp` lemmas** — make key equalities available to `simp` so proofs don't need manual unfolding

---

## File-Level Audit Checklist

When analyzing a whole file:

1. **Repeated tactic sequences** — same `rw`/`simp` chain 2+ times → extract helper
2. **Proof lengths** — >30 lines for "basic" facts → search mathlib; >60 lines → strong candidate
3. **Hand-rolled basics** — continuity proofs not using `fun_prop`, derivatives not using `HasDerivAt` chains, arithmetic not using `omega`/`positivity`/`norm_num`
4. **Overly specific hypotheses** — can `=` become `≤`? Can `[NormedSpace ℝ E]` become `[Module ℝ E]`?
5. **API coverage** — is every proof unfolding a definition directly? Should there be intermediate API lemmas?

---

## See Also

- [proof-refactoring.md](proof-refactoring.md) — Structural refactoring (breaking proofs into helpers)
- [proof-golfing.md](proof-golfing.md) — Tactic-level optimization
- [mathlib-guide.md](mathlib-guide.md) — How to search mathlib
- [mathlib-style.md](mathlib-style.md) — Naming conventions for potential mathlib contributions
