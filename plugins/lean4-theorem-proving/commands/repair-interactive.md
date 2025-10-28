---
name: repair-interactive
description: Interactive compiler-guided repair with user confirmation at each step
allowed-tools:
  - Bash
  - Read
  - Edit
  - Task
  - TodoWrite
  - AskUserQuestion
---

# Interactive Proof Repair

Run compiler-guided repair on `<PATH>` with user confirmation at each step.

**Use when:**
- Learning how repair works
- Want control over which fixes to apply
- Debugging complex proof failures
- Building confidence before automated repair

---

## Parameters

- `<PATH>`: Path to Lean file (required)
- `--show-context=true`: Show code context with each error (default: true)

---

## Workflow

### Phase 1: Initial Assessment

1. **Compile and show status**:
   ```bash
   lake build <PATH> 2> .repair/errs.txt
   ```

2. **Show error summary**:
   ```
   📊 File: <PATH>
   Status: ❌ Compilation failed

   Error:
   - Type: type_mismatch
   - Line: 42
   - Message: type mismatch
     expected: Continuous f
     got: Measurable f

   Code:
    40 | theorem example (h : Measurable f) : Continuous f := by
    41 |   -- This should show continuity
    42 |   exact h  ❌
    43 |

   Ready to start repair? [y/N]
   ```

3. **User confirms** → Continue to Phase 2

### Phase 2: Iterative Repair (Interactive)

For each attempt:

**Step 1: Show Options**

Use `AskUserQuestion`:
```
What should I try for this error?

Options:
1. Try solver cascade (automated: rfl, simp, ring, ...)
2. Call repair agent (Stage 1: Haiku, fast)
3. Call repair agent (Stage 2: Sonnet, precise)
4. Show me the error context again
5. Let me fix it manually (skip to next error)
6. Stop repair
```

**Step 2: Execute Choice**

**Choice 1: Solver Cascade**
```bash
python3 scripts/solverCascade.py .repair/context.json <PATH>
```

Show output:
```
🔍 Trying solver cascade...
   rfl: ❌
   simp: ❌
   ring: ❌
   linarith: ✅ Success!

Generated patch:
--- <PATH>
+++ <PATH>
@@ -42,1 +42,1 @@
-  exact h
+  linarith
```

Ask:
```
Apply this patch? [y/N/d for diff]
```

**Choice 2/3: Agent Repair**

Dispatch agent, show result:
```
🧠 Calling lean4-proof-repair agent (Stage {1/2})...

Agent generated patch:
--- <PATH>
+++ <PATH>
@@ -42,1 +42,2 @@
-  exact h
+  convert continuous_of_measurable h using 2
+  simp
```

Ask:
```
Apply this patch? [y/N/d for diff/e to edit]

Options:
- y: Apply as-is
- N: Skip, try different approach
- d: Show detailed diff
- e: Let me edit the patch first
```

**Choice 4: Show Context**

Re-display error with more context:
```
Read(<PATH>, line-10, line+10)
```

With error annotations.

**Choice 5: Manual Fix**

```
I'll skip to the next error. Make your manual changes, then:
1. Save the file
2. Run /lean4-theorem-proving:repair-interactive again
```

Exit repair loop.

**Choice 6: Stop**

```
Stopping repair.

Progress:
- Attempts made: N
- Patches applied: K
- Current state: {compiling / has errors}

Resume later with: /lean4-theorem-proving:repair-interactive <PATH>
```

**Step 3: Apply Patch (if approved)**

```bash
git apply .repair/patch.diff
```

Show result:
```
✓ Patch applied

Changes:
  Modified: 2 lines
  Added: 1 line
  Removed: 0 lines
```

**Step 4: Recompile**

```bash
lake build <PATH>
```

Show outcome:
```
Recompiling...
- ✅ Fixed line 42!
- ❌ New error at line 58: unsolved goals

Continue to next error? [y/N]
```

### Phase 3: Summary

After user stops or all errors fixed:

```
📊 Repair Session Summary

File: <PATH>
Duration: {time}

Attempts: N
├─ Solver cascade: K successful
├─ Agent Stage 1: L successful
├─ Agent Stage 2: M successful
└─ Manual skips: P

Final status:
✅ File compiles successfully!
 or
⚠️  Remaining errors: R

Attempt log: .repair/attempts.ndjson
```

---

## Example Session

```
User: /lean4-theorem-proving:repair-interactive MyProof.lean