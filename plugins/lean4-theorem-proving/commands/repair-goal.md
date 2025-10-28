---
name: repair-goal
description: Repair a specific proof goal at a given line using compiler-guided feedback
allowed-tools:
  - Bash
  - Read
  - Edit
  - Task
  - TodoWrite
  - mcp__lean-lsp__*
---

# Repair Specific Goal

Run compiler-guided repair on a specific goal at `<PATH>:<LINE>`.

**Use when:** You know exactly which goal is failing and want focused repair.

**Strategy:** Same as repair-file, but stops after fixing the target goal.

---

## Parameters

- `<PATH>`: Path to Lean file (required)
- `<LINE>`: Line number of failing goal (required)
- `--max-attempts=12`: Maximum attempts (default: 12, lower than full file)
- `--context-lines=5`: Lines of context to show (default: 5)

---

## Workflow

### Phase 1: Locate Target

1. **Read file** to verify goal exists:
   ```
   Read(<PATH>, offset=<LINE>-5, limit=10)
   ```

2. **Extract goal via LSP** (if available):
   ```
   mcp__lean-lsp__lean_goal(<PATH>, <LINE>, column=0)
   ```

   This gives you the precise goal state and local context.

3. **Compile to get error**:
   ```bash
   lake build <PATH> 2> .repair/errs.txt
   ```

4. **Verify error is at target line**:
   Parse error, check if `error.line == <LINE>`.

   If not at target line:
   ```
   ⚠️  Target line <LINE> compiles successfully.
   The actual error is at line {error.line}.

   Would you like to repair line {error.line} instead? [y/N]
   ```

### Phase 2: Focused Repair Loop

Same as repair-file, but with constraints:

**Additional checks each iteration:**
1. After applying patch, verify error line changed
2. If error moves to different line → continue
3. If error stays at <LINE> → continue repairs
4. If <LINE> now compiles but new error elsewhere → STOP

**Success condition:**
- Goal at <LINE> compiles (even if file has other errors)
- Report which goal was fixed

**Stop conditions:**
1. Goal at <LINE> compiles ✓
2. Max attempts reached
3. Same error 3 times at <LINE>

### Phase 3: Report

**Success:**
```
✅ Goal at line <LINE> repaired!

Before:
  42 | theorem foo : P := by
  43 |   exact bar  -- ❌ type mismatch

After:
  42 | theorem foo : P := by
  43 |   convert bar using 2
  44 |   simp

Attempts: N
Strategy: {solver_cascade / agent_stage1 / agent_stage2}
```

**Partial success:**
```
⚠️  Goal at line <LINE> fixed, but file has other errors

Fixed goal:
  Line <LINE>: ✓

Remaining errors:
  Line 58: unsolved goals
  Line 91: type mismatch

Run /lean4-theorem-proving:repair-file to fix all errors.
```

---

## Example

User runs:
```
/lean4-theorem-proving:repair-goal MyProof.lean 42
```

You execute:
```
Target: MyProof.lean:42

Reading goal state...
⊢ Continuous f

Compiling...
❌ type mismatch at line 42

Attempt 1/12:
  Error at target: ✓
  Solver cascade: ❌
  Agent (Stage 1): ✓ Generated patch
  Applied: ✓

Compiling...
✅ Goal at line 42 now compiles!

✅ Goal repaired successfully!
```

---

## Use Cases

**1. Interactive development**
- User writes proof outline with sorries
- Fills each sorry one by one
- `/repair-goal Foo.lean 42` for each

**2. Incremental fixes**
- File has 10 errors
- Fix them one at a time in logical order
- Each goal gets focused attention

**3. Testing repair strategies**
- Try repair on specific goal
- If fails, try different approach
- Faster iteration than full file

---

## Implementation Notes

**Prefer LSP when available:**
```
goal_state = mcp__lean-lsp__lean_goal(<PATH>, <LINE>, 0)
```

This gives exact goal and context without compilation.

**Focus attention:**
- Error context highlights target line
- Agent prompt emphasizes "fix ONLY line <LINE>"
- Don't try to fix unrelated errors

**Early exit:**
As soon as target line compiles, STOP. Don't continue to fix other errors.

---

*Compiler-guided repair inspired by APOLLO (https://arxiv.org/abs/2505.05758)*
