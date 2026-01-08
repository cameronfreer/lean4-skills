---
description: Use when Lean 4 proofs have unnecessary have-blocks that could be inlined, or long/reused have-blocks that should be extracted to lemmas
allowed-tools: Bash(lake:*), Bash(bash:*), mcp__lean-lsp__*
---

# Refactor Have-Blocks

Interactive workflow for refactoring `have` statements - either inlining them (proving directly at use site) or extracting them to separate helper lemmas.

**First ask: Do you need the `have` at all?**

Proofs with many `have` statements are often not idiomatic. In mathlib style, you frequently prove results inline where they're needed rather than naming intermediates. Consider eliminating `have` entirely when:
- The result is only used once (just prove it inline)
- The proof fits naturally as an argument to another tactic
- Naming the intermediate doesn't aid understanding

Only keep `have` when:
- The result is used multiple times
- The proof is complex enough that naming genuinely aids readability
- You need the hypothesis name for later tactics (e.g., `exact h`, `rw [h]`)

**When to extract (if `have` is needed):**
- Have-block is long (20+ lines is a good heuristic, but not a hard rule)
- Have-block is reused in multiple places
- Have-block has clear standalone meaning
- Extraction would make main proof easier to follow

**Reference:** See [proof-refactoring.md](../skills/lean4-theorem-proving/references/proof-refactoring.md) for detailed patterns and decision tree.

## Workflow

### 1. Scan for Candidates

**If file not specified, ask:**
```
Which file would you like to refactor?
```

**Scan for refactoring candidates:**

Read the file and identify `have` statements that could be refactored (long proofs, single-use intermediates, or hurting readability).

**Report candidates:**
```
Found N have-blocks to consider in [file]:

1. Line 42: `have h_bound : ∀ i, k i < n := by` (47 lines)
   Used: 1 time | Recommendation: inline or extract

2. Line 156: `have h_meas : Measurable f := by` (8 lines)
   Used: 1 time | Recommendation: inline

3. Line 245: `have h_eq : μ = ν := by` (52 lines)
   Used: 3 times | Recommendation: extract

Which would you like to refactor? (1/2/3/all/skip)
```

### 2. Analyze and Recommend

**For chosen candidate, determine:**

a) **Usage analysis:**
- How many times is the result used?
- Is the name needed for tactics (rw, exact, simp)?
- Could the proof be passed directly as an argument?

b) **Recommend approach:**
```
Analyzing `have h_bound : ∀ i, k i < n := by`...

Usage: h_bound used 1 time at line 89: `exact h_bound i`
Proof length: 47 lines

Options:
1. INLINE - eliminate have, prove directly at use site
2. EXTRACT - move to separate lemma (if reusable or clearer)
3. KEEP - leave as-is (if naming aids understanding)

Recommendation: INLINE (single use, can prove at call site)
Proceed with inline? (yes/extract/keep/cancel)
```

**For multi-use:**
```
Usage: h_meas used 3 times (lines 160, 172, 185)
Proof length: 35 lines

Options:
1. EXTRACT - move to separate lemma (recommended for multi-use)
2. KEEP - leave as-is

Recommendation: EXTRACT (reused, worth naming)
Proceed with extraction? (yes/keep/cancel)
```

### 3a. Inline the Have (if chosen)

**Transform:**
```lean
-- BEFORE:
have h_bound : ∀ i, k i < n := by
  intro i
  -- [proof]
exact h_bound i

-- AFTER:
exact (by intro i; ... : ∀ i, k i < n) i
-- or more idiomatically:
exact proof_term_here
```

**Verify and report:**
```
✅ Inlined successfully!

Changes:
- Removed: 47-line have-block
- Modified: line 89, now proves inline

Proof is now shorter and more direct.
```

### 3b. Extract to Lemma (if chosen)

**Determine parameters needed:**
```
Required parameters:
- k : Fin m → ℕ (used in goal)
- hk_mono : StrictMono k (used in proof)
- n : ℕ (appears in goal)

Optional parameters (could be inlined):
- m : ℕ (inferred from k's type)
```

**Check if extractable:**
- Does it use local `let` bindings? (May cause definitional issues)
- Is it domain-specific or generic?
- Would extraction reduce clarity?

**Propose extraction:**

```
-- BEFORE (inline):
theorem main_theorem ... := by
  ...
  have h_bound : ∀ i, k i < n := by
    intro i
    -- [30+ lines of proof here]
    ...
    omega
  ...

-- AFTER (extracted):

private lemma helper_bound {m : ℕ} (k : Fin m → ℕ) (hk : StrictMono k)
    (i : Fin m) : k i < k (Fin.last m) + 1 := by
  have : k i ≤ k (Fin.last m) := StrictMono.monotone hk (Fin.le_last i)
  omega

theorem main_theorem ... := by
  ...
  have h_bound : ∀ i, k i < n := fun i => helper_bound k hk_mono i
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

### 4. Apply Changes

**If user approves, apply the chosen refactoring:**

**For inline:**
a) Remove the have-block
b) Replace uses with inline proof
c) Verify compilation

**For extract:**
a) Add helper lemma (before the theorem)
b) Replace have-block with call to helper
c) Verify compilation

```bash
lake build [file]
```

**Report result:**
```
✅ Refactoring successful!

Changes:
- [Inline] Removed: 47-line have-block, proved inline at use site
- [Extract] Added: private lemma strictMono_bound (12 lines), replaced 47-line have-block

Continue with next candidate? (yes/no)
```

### 5. Handle Issues

**If inline fails:**
- Proof depends on hypothesis name in non-trivial way → try extract instead
- Multiple uses weren't detected → switch to extract
- Inline proof too complex → may need to keep as-is or extract

**If extraction fails:**

```
❌ Extraction failed: type mismatch

Analysis:
- Helper returns: k i < k (Fin.last m) + 1
- Original had: k i < n
- Issue: n was a let-binding that's not available in helper

Options:
1. Add n as parameter with equality proof
2. Try inline instead
3. Keep original (don't refactor)
4. Manual edit

Choose: (1/2/3/4)
```

**Common extraction issues:**
- **Let-binding scope:** Add explicit parameter with `hparam : param = expr`
- **Type inference:** Add explicit type annotations
- **Universe issues:** May need to generalize types

## Quick Reference

**Decision tree:**
1. Is the `have` used only once? → Consider **inline**
2. Is the `have` used multiple times? → Consider **extract**
3. Would extraction require 10+ parameters? → **Keep** or **inline**
4. Is the proof complex but self-contained? → **Extract**

**Inline checklist:**
- [ ] Result used only once (or can duplicate short proof)
- [ ] Proof fits naturally at use site
- [ ] No need to reference hypothesis name elsewhere

**Extraction checklist:**
- [ ] Goal is self-contained (not mid-calculation)
- [ ] No local let-bindings (or willing to parameterize)
- [ ] Parameters ≤ 6
- [ ] Helper would be reusable or improve clarity

**Naming conventions (for extracted lemmas):**
- Use snake_case
- Describe what it proves: `bounded_by_integral`, `measurable_composition`
- Avoid: `helper1`, `aux`, `temp`

**When to keep as-is:**
- Short have-block that's already clear
- Naming genuinely aids understanding
- Neither inline nor extract improves readability

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
