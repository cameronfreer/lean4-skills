---
name: golf
description: Optimize Lean proofs for brevity and clarity
user_invocable: true
---

# Lean4 Golf

Optimize Lean proofs that already compile. Reduce tactic count, shorten proofs, improve readability.

**Prerequisite:** Code must compile. Run `lake build` first.

---

## Usage

```
/lean4:golf                     # Golf entire project
/lean4:golf File.lean           # Golf specific file
/lean4:golf File.lean:42        # Golf proof at specific line
/lean4:golf --dry-run           # Show opportunities without applying
```

---

## What It Does

1. **Verify Build** - Ensure code compiles before optimizing
2. **Find Opportunities** - Detect golfable patterns
3. **Verify Safety** - Check usage counts before inlining
4. **Apply Optimizations** - Make changes with verification
5. **Report Results** - Show savings and saturation

---

## Golfing Patterns (Priority Order)

### Instant Wins (Always Apply)

| Pattern | Before | After |
|---------|--------|-------|
| rw + exact | `rw [h]; exact trivial` | `rwa [h]` |
| ext + rfl | `ext x; rfl` | `rfl` |
| simp + rfl | `simp; rfl` | `simp` |
| constructor + exact | `constructor; exact h1; exact h2` | `exact ⟨h1, h2⟩` |

### Safe with Verification

| Pattern | Condition | Action |
|---------|-----------|--------|
| Inline let | Used ≤2 times | Inline |
| Inline have | Used once, ≤1 line | Inline |
| Remove redundant ext | Types match | Remove |

### Skip (False Positive Risk)

- Let bindings used 3+ times (would expand code)
- Complex have blocks (readability matters)
- Named hypotheses used in error messages

---

## Workflow

### Step 1: Verify Build

```bash
lake build
```

If build fails, stop and suggest `/lean4:autoprover` first.

### Step 2: Find Opportunities

**With LSP (preferred):**
```
Use lean_hover_info to understand proof structure
Use lean_goal to see what each tactic does
```

**Fallback (if LSP unavailable):**
```bash
${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/find_golfable.py [file] --filter-false-positives
```

### Step 3: Verify Safety

Before inlining any binding, check usage count:

```bash
${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/analyze_let_usage.py [file] --line [line]
```

Or manually count references in the proof with `grep` or by reading the code.

**Rules:**
- 1-2 uses: Safe to inline
- 3-4 uses: Probably skip (40% false positive)
- 5+ uses: Never inline

### Step 4: Apply Optimizations

For each safe optimization:
1. Make the change
2. Run `lake build` to verify
3. If fails, revert immediately
4. If succeeds, continue

### Step 5: Report

```markdown
## Golf Results

**File:** Core.lean
**Optimizations applied:** 5
**Optimizations skipped:** 2 (safety)
**Build status:** ✓ passing

**Changes:**
- Line 23: `rw [h]; exact` → `rwa [h]` (-1 line)
- Line 45: Inlined `let x := ...` (-2 lines)
- Line 78: `ext; rfl` → `rfl` (-1 line)
...

**Total savings:** 8 lines, ~12% reduction

**Skipped (false positive risk):**
- Line 56: `let bound` used 4 times
- Line 89: `have` block is 15 lines (readability)
```

---

## Saturation Detection

Stop golfing when:
- Success rate drops below 20%
- Last 3 attempts all failed/reverted
- Remaining opportunities are all "skip" category

Report saturation:
```
Saturation reached after 12 optimizations.
Remaining 3 opportunities are false positives or low-value.
```

---

## Dry Run Mode

With `--dry-run`, show opportunities without applying:

```markdown
## Golf Opportunities (Dry Run)

**File:** Core.lean

| Line | Pattern | Confidence | Savings |
|------|---------|------------|---------|
| 23 | rw + exact → rwa | High | 1 line |
| 45 | Inline let (1 use) | High | 2 lines |
| 56 | Inline let (4 uses) | Skip | - |
| 78 | ext + rfl → rfl | High | 1 line |

**Estimated savings:** 4 lines from 3 safe optimizations
**Run without --dry-run to apply**
```

---

## Integration with Review

`/lean4:review` includes golfing suggestions in read-only mode.
`/lean4:golf` actually applies the changes.

Typical workflow:
```
/lean4:review           # See opportunities
/lean4:golf --dry-run   # Confirm what will change
/lean4:golf             # Apply changes
/lean4:checkpoint       # Save progress
```

---

## Example

```
User: /lean4:golf Core.lean

Claude: Verifying build...
✓ Core.lean compiles

Finding golfing opportunities...

Found 6 patterns:
- 4 instant wins (rw+exact, ext+rfl)
- 1 safe inline (let used once)
- 1 skip (let used 5 times)

Applying optimizations...

[1/5] Line 23: rw [h]; exact → rwa [h]
  Building... ✓

[2/5] Line 45: ext x; rfl → rfl
  Building... ✓

[3/5] Line 67: Inline let bound := ...
  Checking usage... 1 reference, safe
  Building... ✓

[4/5] Line 89: simp [*]; rfl → simp [*]
  Building... ✓

[5/5] Line 112: constructor; exact; exact → exact ⟨_, _⟩
  Building... ✓

## Golf Results

Optimizations applied: 5/6
Skipped: 1 (let used 5 times)
Total savings: 7 lines (~10%)
Build status: ✓ passing
```

---

## See Also

- `/lean4:review` - See golfing suggestions (read-only)
- `/lean4:checkpoint` - Save after golfing
- [proof-golfing.md](../skills/lean4/references/proof-golfing.md) - Full pattern reference
- [proof-golfing-safety.md](../skills/lean4/references/proof-golfing-safety.md) - False positive guide
