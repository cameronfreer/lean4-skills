# Agent Workflow Examples

**Internal reference:** These workflows are orchestrated by commands. You typically don't invoke them directly.

Extended workflow examples for Lean4 plugin internal workflows.

---

## lean4-sorry-filler-deep

### Structural Refactoring Example

```
## Sorry Filling Plan

**Target:** Core.lean:156 - `filter_convergence`

**Why it's hard:**
- Statement uses Set but should use Filter
- Need intermediate lemma about Filter.Eventually
- Type class instance ordering issue

**Strategy:**
1. Generalize statement from Set to Filter
2. Add helper lemma `filter_eventually_of_set`
3. Prove main theorem using helper
4. Verify dependent theorems still work

**Estimated difficulty:** medium
**Estimated phases:** 3

---

## Phase 1 Complete

**Actions taken:**
- Generalized `filter_convergence` type signature
- Added import for `Mathlib.Order.Filter.Basic`

**Compile status:** ✓ Success

**Next phase:** Add helper lemma

---

## Phase 2 Complete

**Actions taken:**
- Added `filter_eventually_of_set` helper (8 lines)
- Placed in Helpers.lean for reuse

**Compile status:** ✓ Success

**Next phase:** Fill original sorry

---

## Phase 3 Complete

**Actions taken:**
- Filled sorry using helper lemma
- Proof: 4 lines using `filter_eventually_of_set` + `Filter.Eventually.mono`

**Compile status:** ✓ Success

---

## Sorry Filled Successfully

**Target:** Core.lean:156
**Strategy used:** structural refactoring
**Phases completed:** 3
**Total edits:** 2 files changed

**Summary:**
- Sorry eliminated: ✓
- Proof type: helper-lemmas
- Complexity: 4 lines of proof
- New helpers introduced: 1 (`filter_eventually_of_set`)
- Axioms introduced: 0

**Verification:**
- File compiles: ✓
- Dependent theorems work: ✓
- No unexpected axioms: ✓
```

---

## lean4-proof-repair

### Type Mismatch Repair

```json
{
  "errorHash": "type_mismatch_a3f2",
  "errorType": "type_mismatch",
  "message": "type mismatch\n  h1\nhas type\n  Measurable f\nbut is expected to have type\n  Continuous f",
  "file": "Core.lean",
  "line": 42,
  "goal": "⊢ Continuous f",
  "localContext": ["h1 : Measurable f", "h2 : Integrable f μ"]
}
```

Stage 1 output:
```diff
--- Core.lean
+++ Core.lean
@@ -42,1 +42,1 @@
-  exact h1
+  exact Continuous.of_discrete h1
```

Build fails, error persists. Stage 1 retry:
```diff
--- Core.lean
+++ Core.lean
@@ -42,1 +42,2 @@
-  exact h1
+  haveI : DiscreteTopology α := inferInstance
+  exact continuous_of_discreteTopology
```

Build succeeds. ✓

### Instance Synthesis Repair

```json
{
  "errorType": "synth_instance",
  "message": "failed to synthesize instance\n  MeasurableSpace β",
  "file": "Core.lean",
  "line": 89
}
```

Stage 1 outputs (after 3 failures, escalates to Stage 2):
```diff
--- Core.lean
+++ Core.lean
@@ -87,0 +87,1 @@
+variable [MeasurableSpace β] in
@@ -89,1 +90,1 @@
-theorem foo : Measurable (f ∘ g) := by
+theorem foo [MeasurableSpace β] : Measurable (f ∘ g) := by
```

### Unknown Identifier Repair

```json
{
  "errorType": "unknown_ident",
  "message": "unknown identifier 'continuous_real'",
  "file": "Core.lean",
  "line": 15
}
```

Search: `bash $LEAN4_SCRIPTS/search_mathlib.sh "continuous.*real" name`
Found: `Real.continuous_ofReal`

```diff
--- Core.lean
+++ Core.lean
@@ -1,0 +1,1 @@
+import Mathlib.Topology.Instances.Real
@@ -15,1 +16,1 @@
-  exact continuous_real
+  exact Real.continuous_ofReal
```

---

## lean4-proof-golfer

### Verified Inlining Example

```
File: Core.lean
Finding patterns...

Pattern found at line 45:
  let x := complex_expr
  have h := property x
  exact h

Running: analyze_let_usage.py Core.lean --line 45
Result: x used 1 time, h used 1 time

Safety: ✓ Safe to inline (both used ≤2 times)

Before (3 lines):
  let x := complex_expr
  have h := property x
  exact h

After (1 line):
  exact property complex_expr

Building... ✓

Savings: 2 lines, ~30 tokens
```

### False Positive Detection

```
Pattern found at line 78:
  let bound := expensive_computation
  ...uses bound 6 times...

Running: analyze_let_usage.py Core.lean --line 78
Result: bound used 6 times

Safety: ✗ SKIP - would expand code 6× (from 1 expr to 6)

Skipping this optimization.
```

### Saturation Report

```
Proof Golfing Results:

File: Core.lean
Patterns attempted: 15
Successful: 8
Failed/Reverted: 2
Skipped (safety): 5

Total savings:
- Lines: 145 → 127 (12% reduction)
- Tokens: estimated 2100 → 1850 tokens

Saturation indicators:
- Success rate: 8/15 = 53%
- Last 3 attempts: 1 success, 2 skips

Status: Good progress, some room remains.
Continue? (yes/no)
```

---

## lean4-axiom-eliminator

### Migration Plan Example

```
## Axiom Elimination Plan

**Total custom axioms:** 4
**Target:** 0 custom axioms

### Axiom Inventory

1. **helper_continuous** (Core.lean:23)
   - Type: mathlib_search
   - Used by: 3 theorems
   - Strategy: Search mathlib for equivalent
   - Priority: high

2. **measure_finite** (Measure.lean:45)
   - Type: compositional
   - Used by: 5 theorems
   - Strategy: Compose from mathlib lemmas
   - Priority: high

3. **set_countable** (Core.lean:89)
   - Type: structural_refactor
   - Used by: 2 theorems
   - Strategy: Generalize to Countable typeclass
   - Priority: medium

4. **magic_bound** (Bounds.lean:12)
   - Type: needs_deep_expertise
   - Used by: 1 theorem
   - Strategy: Convert to sorry for later filling
   - Priority: low

### Elimination Order

**Phase 1: Low-hanging fruit**
- helper_continuous (mathlib_search)
- measure_finite (compositional)

**Phase 2: Medium difficulty**
- set_countable (structural_refactor)

**Phase 3: Hard cases**
- magic_bound (convert to sorry)
```

### Per-Axiom Progress Report

```
## Axiom Eliminated: helper_continuous

**Location:** Core.lean:23
**Strategy:** mathlib_import

**Search results:**
bash $LEAN4_SCRIPTS/search_mathlib.sh "continuous.*comp" name
→ Found: Continuous.comp in Mathlib.Topology.Basic

**Changes made:**
- Removed `axiom helper_continuous`
- Added `import Mathlib.Topology.Basic`
- Replaced with `theorem helper_continuous := Continuous.comp`

**Verification:**
- Compile: ✓
- Axiom count: 4 → 3 ✓
- Dependents work: ✓

**Next target:** measure_finite
```

### Final Summary

```
## Axiom Elimination Complete

**Starting axioms:** 4
**Ending axioms:** 0
**Eliminated:** 4

**By strategy:**
- Mathlib import: 2
- Compositional proof: 1
- Structural refactor: 1
- Converted to sorry: 0

**Files changed:** 3
**Helper lemmas added:** 2

**Quality checks:**
- All files compile: ✓
- No new axioms introduced: ✓
- Dependent theorems work: ✓
- Sorry count unchanged: ✓
```
