# Refactoring Long Proofs

Guide for breaking monolithic proofs into maintainable helper lemmas.

## When to Refactor

**Refactor when:**
- Proof exceeds 100 lines
- Multiple conceptually distinct steps
- Intermediate results would be useful elsewhere
- Hard to understand/maintain
- Repeated patterns

**Don't refactor when:**
- Proof is short and linear
- No natural intermediate milestones
- Extraction would require too many parameters
- Proof is already well-structured with `have` statements

---

## LSP-Based Refactoring Workflow

**Strategy:** Use `lean_goal` (from Lean LSP MCP) to inspect proof state at different locations, then subdivide at natural breakpoints where intermediate goals are clean and reusable.

### Step 1: Survey the Proof

Walk through the proof checking goals at different points:

```python
# Check goals at various locations in the long proof
lean_goal(file, line=15)   # After initial setup
lean_goal(file, line=45)   # After first major step
lean_goal(file, line=78)   # After second major step
lean_goal(file, line=120)  # Near end
```

**What to look for:**
- Clean, self-contained intermediate goals
- Natural mathematical milestones
- Points where context is manageable

### Step 2: Identify Extraction Points

Look for locations where:
- **Goal is clean:** Self-contained statement with clear meaning
- **Dependencies are local:** Depends only on earlier hypotheses (no forward references)
- **Useful elsewhere:** Goal would be reusable in other contexts
- **Natural meaning:** Intermediate state has clear mathematical interpretation

**Good breakpoints:**
- After establishing key inequalities or bounds
- After case splits (before/after `by_cases`)
- After measurability/integrability proofs
- Where intermediate result has a clear name
- After computing/simplifying expressions
- Before/after applying major lemmas

**Bad breakpoints:**
- Mid-calculation (no clear intermediate goal)
- Where helper would need 10+ parameters
- Where context is too tangled to separate cleanly
- In the middle of a `calc` chain
- Where goal depends on later bindings

### Step 3: Extract Helper Lemma

```lean
-- BEFORE: Monolithic proof
theorem big_result : Conclusion := by
  intro x hx
  have h1 : IntermediateGoal1 := by
    [30 lines of tactics...]
  have h2 : IntermediateGoal2 := by
    [40 lines of tactics...]
  [30 more lines...]

-- AFTER: Extracted helpers
lemma helper1 (x : α) (hx : Property x) : IntermediateGoal1 := by
  [30 lines - extracted from h1]

lemma helper2 (x : α) (h1 : IntermediateGoal1) : IntermediateGoal2 := by
  [40 lines - extracted from h2]

theorem big_result : Conclusion := by
  intro x hx
  have h1 := helper1 x hx
  have h2 := helper2 x h1
  [30 lines - much clearer now]
```

### Step 4: Verify with LSP

After each extraction:
```python
lean_diagnostic_messages(file)  # Check for errors
lean_goal(file, line)           # Confirm goals match
```

**Verify extraction is correct:**
```python
# Original line number where `have h1 : ...` was
lean_goal(file, line=old_h1_line)
# → Should match helper1's conclusion

# New line number after extraction
lean_goal(file, line=new_h1_line)
# → Should show `h1 : IntermediateGoal1` available
```

---

## Non-LSP Refactoring (Manual)

If you don't have LSP access, use this manual workflow:

### Step 1: Read and Understand

Read through the proof identifying conceptual sections:
- What is the proof trying to establish?
- What are the major steps?
- Are there repeated patterns?

### Step 2: Mark Candidates

Add comments marking potential extraction points:
```lean
theorem big_result : ... := by
  intro x hx
  -- Candidate 1: Establish boundedness
  have h1 : ... := by
    ...
  -- Candidate 2: Prove measurability
  have h2 : ... := by
    ...
```

### Step 3: Extract One at a Time

Extract one helper at a time, compile after each:
1. Copy `have` proof to new lemma
2. Identify required parameters
3. Replace original with `have h := helper args`
4. `lake build` to verify
5. Commit if successful

### Step 4: Iterate

Repeat until proof is manageable.

---

## Naming Extracted Helpers

**Good names describe what the lemma establishes:**
- `bounded_by_integral` - establishes bound
- `measurable_composition` - proves measurability
- `convergence_ae` - proves a.e. convergence

**Avoid vague names:**
- `helper1`, `aux_lemma` - meaningless
- `part_one`, `step_2` - based on structure, not content
- `temp`, `tmp` - should be permanent

**Mathlib-style conventions:**
- Use snake_case
- Include key concepts: `integral`, `measure`, `continuous`, etc.
- Add context if needed: `of_`, `_of`, `_iff`

---

## Real Refactoring Example

**Context:** 63-line monolithic proof about exchangeable measures with strict monotone functions.

**Step 1: Identify natural boundaries**

Using `lean_goal` at different points revealed:
- Line 15: After establishing `hk_bound : ∀ i, k i < n` (clean arithmetic result)
- Line 35: After constructing permutation (conceptually distinct)
- Line 50: After projection proof (measure theory manipulation)

**Step 2: Extract arithmetic helper**

Found this embedded calculation:
```lean
have hk_bound : ∀ i : Fin (m' + 1), k i < n := by
  intro i
  simp only [n]
  have : k i ≤ k ⟨m', Nat.lt_succ_self m'⟩ := by
    apply StrictMono.monotone hk_mono
    exact Fin.le_last i
  omega
```

Extracted to:
```lean
/-- Strictly monotone functions satisfy k(i) ≤ k(last) for all i -/
private lemma strictMono_all_lt_succ_last {m : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (i : Fin m) (last : Fin m)
    (h_last : ∀ j, j ≤ last) :
    k i ≤ k last := by
  apply StrictMono.monotone hk
  exact h_last i
```

**Result:** Main proof now just calls helper, much clearer.

**Step 3: Verify with LSP**

```python
lean_diagnostic_messages(file)  # No errors ✓
lean_goal(file, line=15)        # Shows helper available ✓
```

**Final structure:**
- Original: 63 lines monolithic
- Refactored: 45 lines main + 33 lines helpers = 78 lines total
- **Success:** Much clearer structure, each piece testable independently

**Key insight:** Success measured by clarity, not brevity.

---

## Critical Patterns from Real Refactoring

### 1. Use `private` for Proof-Specific Helpers

**Pattern:** Mark helper lemmas as `private` when they're only used in one theorem and have very specific signatures.

```lean
/-- Helper lemma: strictly monotone functions satisfy k(i) ≤ k(last) -/
private lemma strictMono_all_lt_succ_last {m : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (i : Fin m) (last : Fin m)
    (h_last : ∀ j, j ≤ last) :
    k i ≤ k last := by
  apply StrictMono.monotone hk
  exact h_last i
```

**Why:** This signals "internal scaffolding" - too specific to be generally useful, but clarifies the main proof.

### 2. ⚠️ CRITICAL: Let Bindings Create Definitional Inequality

**Problem:** When extracting a helper that uses `let` bindings, those bindings create new definitional contexts that don't unify with the main proof's `let` bindings, even if syntactically identical.

**What happened:**
```lean
-- In main theorem:
let ι : Fin (m' + 1) → Fin n := fun i => ⟨i.val, ...⟩
let proj : (Fin n → α) → (Fin (m' + 1) → α) := fun f i => f (ι i)

-- In helper lemma (also uses let):
private lemma helper ... :=
  let ι : Fin m → Fin n := fun i => ⟨i.val, ...⟩
  let proj : (Fin n → α) → (Fin m → α) := fun f i => f (ι i)
  Measure.map (proj ∘ ...) μ = Measure.map (proj ∘ ...) μ := by ...

-- Error when using helper:
-- "Did not find an occurrence of the pattern (proj ∘ fun ω j => ...)"
-- Main theorem's `proj` ≠ helper's `proj` definitionally!
```

**Solutions:**
- **Option A:** Inline the proof directly (what we did for measure theory manipulations)
- **Option B:** Pass `ι` and `proj` as explicit parameters instead of `let` bindings
- **Option C:** Use `show` to change the goal explicitly

**Takeaway:** Avoid `let` bindings in helper signatures when the caller also uses `let`. Use explicit parameters instead.

### 3. Omega Has Limits - Provide Intermediate Steps

**Problem:** `omega` can fail on arithmetic goals that humans find obvious.

**Original failing attempt:**
```lean
private lemma strictMono_length_le_max_succ {m : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (last : Fin m) :
    m ≤ k last + 1 := by
  have h_last_val : last.val < m := last.isLt
  have h_mono : last.val ≤ k last := strictMono_Fin_ge_id hk last
  omega  -- ERROR: "omega could not prove the goal"
```

**Successful fix:**
```lean
private lemma strictMono_length_le_max_succ {m : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (last : Fin m)
    (h_last_is_max : last.val + 1 = m) :  -- Explicit equality
    m ≤ k last + 1 := by
  have h_mono : last.val ≤ k last := strictMono_Fin_ge_id hk last
  calc m = last.val + 1 := h_last_is_max.symm
       _ ≤ k last + 1 := Nat.add_le_add_right h_mono 1
```

**Why it helps:** Making `last.val + 1 = m` an explicit assumption (proven as `rfl` at call site) gives `omega` less to figure out. Use `calc` for clarity.

### 4. Measure Theory Extraction Requires Exact Alignment

**Lesson:** When extracting lemmas involving `Measure.map` and compositions, ensure types and compositions align exactly. Measure theory lemmas are sensitive to definitional equality.

**What didn't work:**
```lean
-- Helper returned: Measure.map (proj ∘ f) μ = Measure.map (proj ∘ g) μ
-- Main theorem had different `proj` definition (via let)
-- Rewrite failed even though they looked the same
```

**What worked:**
```lean
-- Inline the projection proof directly in main theorem:
have hproj_eq : Measure.map (proj ∘ fun ω j => X (σ j).val ω) μ =
                Measure.map (proj ∘ fun ω j => X j.val ω) μ := by
  rw [← Measure.map_map hproj_meas (measurable_pi_lambda _ ...),
      ← Measure.map_map hproj_meas (measurable_pi_lambda _ ...)]
  exact congrArg (Measure.map proj) hexch
```

**Takeaway:** For measure theory manipulations with `let` bindings, prefer inlining over extraction.

### 5. Document What and Why

**Pattern:** Every helper lemma should explain:
1. What it proves (in mathematical terms)
2. Why it's true (key insight)
3. How it's used (if not obvious)

**Good example:**
```lean
/--
Helper lemma: The length of the domain is bounded by the maximum value plus one.

For a strictly monotone function `k : Fin m → ℕ`, we have `m ≤ k(m-1) + 1`.
This uses the fact that strictly monotone functions satisfy `i ≤ k(i)` for all `i`.
-/
private lemma strictMono_length_le_max_succ ...
```

### 6. Test After Every Extraction

**Workflow with LSP:**
1. Extract helper lemma
2. `lean_diagnostic_messages(file)` on helper
3. Update main theorem to use helper
4. `lean_diagnostic_messages(file)` on main theorem
5. Fix any type mismatches
6. Repeat

**Don't:** Make multiple changes then check - errors compound!

---

## Refactoring Decision Tree

```
Is the proof > 50 lines?
├─ Yes: Look for natural boundaries (use lean_goal to inspect states)
│   ├─ Found arithmetic bounds?
│   │   ├─ Can extract without `let` bindings? → Extract to private helper
│   │   └─ Uses complex `let` bindings? → Consider inlining
│   ├─ Found permutation construction?
│   │   └─ Reusable pattern? → Extract (ensure parameter clarity)
│   └─ Found measure manipulations?
│       └─ Uses `let` bindings? → Prefer inlining (definitional issues)
└─ No: Probably fine as-is

When extracting:
1. Make helper `private` if proof-specific
2. Avoid `let` bindings in helper signatures (use explicit parameters)
3. If omega fails, add explicit intermediate steps (use calc)
4. Document what the helper proves and why
5. Test compilation after each extraction with lean_diagnostic_messages
```

---

## Benefits of Refactoring

**Maintainability:**
- Easier to understand small proofs
- Easier to modify without breaking
- Clear dependencies between lemmas

**Reusability:**
- Helper lemmas useful in other contexts
- Avoid reproving same intermediate results
- Build library of project-specific lemmas

**Testing:**
- Test helpers independently
- Isolate errors to specific lemmas
- Faster compilation (smaller units)

**Collaboration:**
- Easier to review small lemmas
- Clear boundaries for parallel work
- Better documentation opportunities

---

## Anti-Patterns

**❌ Over-refactoring:**
- Creating helpers used only once
- Extracting every `have` statement
- Too many small lemmas (harder to navigate)

**❌ Under-refactoring:**
- 500+ line proofs
- Multiple independent results in one theorem
- Repeated code instead of shared helpers

**❌ Poor parameter choices:**
- Extracting with 15+ parameters
- Including unnecessary generality
- Making helpers too specific to one use case

**✅ Good balance:**
- Extract when reusable or conceptually distinct
- Aim for 20-80 line helpers
- Parameters capture essential dependencies only

---

## See Also

- [lean-lsp-tools-api.md](lean-lsp-tools-api.md) - LSP tools for goal inspection
- [proof-golfing.md](proof-golfing.md) - Simplifying proofs after compilation
- [mathlib-style.md](mathlib-style.md) - Naming conventions
