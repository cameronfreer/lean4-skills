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

## Example Workflow (To Be Populated)

*This section will be updated with a detailed example from actual refactoring work, showing:*
- *Initial monolithic proof with specific line numbers*
- *Goal states at different points (from `lean_goal`)*
- *Decision process for where to extract*
- *Final extracted structure*
- *Verification steps*

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
