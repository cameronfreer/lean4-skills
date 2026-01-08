---
description: Extract long have-blocks into separate lemmas for cleaner proofs
allowed-tools: Bash(bash:*)
---

# Extract Long Have-Blocks

Interactive workflow for refactoring long `have` statements (>30 lines) into separate helper lemmas.

**Reference:** See [proof-refactoring.md](../skills/lean4-theorem-proving/references/proof-refactoring.md) for detailed patterns and decision tree.

## Workflow

### 1. Scan for Candidates

**If file not specified, ask:**
```
Which file would you like to refactor?
```

**Scan for long have-blocks:**

Read the file and identify `have` statements where the proof spans 30+ lines.

**Report candidates:**
```
Found N long have-blocks in [file]:

1. Line 42: `have h_bound : ∀ i, k i < n := by` (47 lines)
   Goal type: ∀ i, k i < n

2. Line 156: `have h_meas : Measurable f := by` (35 lines)
   Goal type: Measurable f

3. Line 245: `have h_eq : μ = ν := by` (52 lines)
   Goal type: μ = ν

Which would you like to extract? (1/2/3/all/skip)
```

### 2. Analyze Selected Have-Block

**For chosen candidate:**

a) **Read surrounding context:**
- What theorem/lemma contains this have?
- What hypotheses are available?
- Is the have used multiple times or just once?

b) **Determine parameters needed:**
```
Analyzing `have h_bound : ∀ i, k i < n := by`...

Required parameters:
- k : Fin m → ℕ (used in goal)
- hk_mono : StrictMono k (used in proof)
- n : ℕ (appears in goal)

Optional parameters (could be inlined):
- m : ℕ (inferred from k's type)
```

c) **Check if extractable:**
- Does it use local `let` bindings? (May cause definitional issues)
- Is it domain-specific or generic?
- Would extraction reduce clarity?

### 3. Generate Helper Lemma

**Propose extraction:**

```lean
-- BEFORE (inline):
theorem main_theorem ... := by
  ...
  have h_bound : ∀ i, k i < n := by
    intro i
    simp only [n]
    have : k i ≤ k ⟨m', Nat.lt_succ_self m'⟩ := by
      apply StrictMono.monotone hk_mono
      exact Fin.le_last i
    omega
  ...

-- AFTER (extracted):

-- Helper for bounding strictly monotone function values
private lemma strictMono_bound {m : ℕ} (k : Fin m → ℕ) (hk : StrictMono k)
    (i : Fin m) : k i < k ⟨m - 1, by omega⟩ + 1 := by
  have : k i ≤ k ⟨m - 1, by omega⟩ := StrictMono.monotone hk (Fin.le_last i)
  omega

theorem main_theorem ... := by
  ...
  have h_bound : ∀ i, k i < n := fun i => strictMono_bound k hk_mono i
  ...
```

**Present options:**
```
Proposed extraction:

Helper name: strictMono_bound (or suggest alternative)
Parameters: k, hk (minimal)
Visibility: private (proof-specific) or public?

Preview the change? (yes/different-name/more-params/cancel)
```

### 4. Apply Extraction

**If user approves:**

a) **Add helper lemma** (before the theorem)

b) **Replace have-block** with call to helper

c) **Verify compilation:**
```bash
lake build [file]
```

d) **Report result:**
```
✅ Extraction successful!

Changes:
- Added: private lemma strictMono_bound (12 lines)
- Replaced: 47-line have-block with 1-line call
- Net change: -34 lines

Main theorem now reads more clearly.

Continue with next candidate? (yes/no)
```

### 5. Handle Issues

**If extraction fails:**

```
❌ Extraction failed: type mismatch

The helper's return type doesn't match the original have.

Analysis:
- Helper returns: k i < k (Fin.last m) + 1
- Original had: k i < n
- Issue: n was a let-binding that's not available in helper

Options:
1. Add n as parameter with equality proof
2. Inline the let-binding
3. Keep original (don't extract)
4. Manual edit

Choose: (1/2/3/4)
```

**Common issues:**
- **Let-binding scope:** Add explicit parameter with `hparam : param = expr`
- **Type inference:** Add explicit type annotations
- **Universe issues:** May need to generalize types

## Quick Reference

**Extraction checklist:**
- [ ] Have-block is 30+ lines
- [ ] Goal is self-contained (not mid-calculation)
- [ ] No local let-bindings (or willing to parameterize)
- [ ] Parameters ≤ 6 (otherwise consider inlining)
- [ ] Helper would be reusable or improve clarity

**Naming conventions:**
- Use snake_case
- Describe what it proves: `bounded_by_integral`, `measurable_composition`
- Avoid: `helper1`, `aux`, `temp`

**When NOT to extract:**
- Have-block is < 30 lines
- Would require 10+ parameters
- Goal is part of larger calculation
- Extraction obscures proof flow
- Already well-commented and clear

## Integration with LSP

**If lean-lsp MCP available:**

```python
# Get goal at have-block location
lean_goal(file, line=have_line)

# Check for errors after extraction
lean_diagnostic_messages(file)

# Verify types align
lean_hover_info(file, line=helper_call_line, column)
```

## Related Commands

- `/analyze-sorries` - Find incomplete proofs
- `/fill-sorry` - Fill individual sorries
- `/golf-proofs` - Simplify after extraction
- `/check-axioms` - Verify no axioms introduced

## References

- [proof-refactoring.md](../skills/lean4-theorem-proving/references/proof-refactoring.md) - Full refactoring patterns
- [mathlib-style.md](../skills/lean4-theorem-proving/references/mathlib-style.md) - Naming conventions
