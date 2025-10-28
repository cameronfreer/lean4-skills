---
name: repair-file
description: Run compiler-guided proof repair on a Lean file using iterative error feedback and automated solvers
allowed-tools:
  - Bash
  - Read
  - Edit
  - Task
  - Glob
  - Grep
  - TodoWrite
---

# Compiler-Guided Proof Repair

Run iterative proof repair on `<PATH>` using compiler feedback to drive targeted fixes.

**Strategy:** Compile → Parse Error → Try Solvers → Agent Repair → Apply → Verify (loop)

**Inspired by:** APOLLO (https://arxiv.org/abs/2505.05758) - compiler-guided repair with low sampling budgets

---

## Parameters

- `<PATH>`: Path to Lean file to repair (required)
- `--max-attempts=24`: Maximum repair attempts (default: 24)
- `--repeat-limit=3`: Bail after N identical errors (default: 3)
- `--stage2-threshold=3`: Escalate to Stage 2 after N repeats (default: 3)

---

## Workflow

You will orchestrate a compiler-guided repair loop:

### Phase 1: Setup
1. Verify file exists: `Read(<PATH>)`
2. Create repair directory: `.repair/`
3. Initialize attempt log: `.repair/attempts.ndjson`
4. Create todo list tracking attempts

### Phase 2: Repair Loop

For each attempt (up to `--max-attempts`):

**Step 1: Compile**
```bash
lake build <PATH> 2> .repair/errs.txt
```
- If succeeds → DONE! Report success and exit
- If fails → continue to Step 2

**Step 2: Parse Error**
```bash
python3 scripts/parseLeanErrors.py .repair/errs.txt > .repair/context.json
```

Extract from context.json:
- `errorHash`: Track for repeats
- `errorType`: Route to appropriate fix
- `message`: Show to user
- `goal`, `localContext`, `codeSnippet`: Provide to agent

**Step 3: Check for Repeated Error**
- If `errorHash` same as previous:
  - Increment repeat counter
  - If counter >= `--repeat-limit`:
    - If stage == 1: Escalate to Stage 2, reset counter
    - If stage == 2: BAIL (same error after strong model)
- Else: Reset repeat counter

**Step 4: Try Solver Cascade** (fast path)
```bash
python3 scripts/solverCascade.py .repair/context.json <PATH> > .repair/solver.diff
```

Solver order: `rfl → simp → ring → linarith → nlinarith → omega → exact? → apply? → aesop`

- If solver succeeds (exit 0):
  ```bash
  git apply .repair/solver.diff
  ```
  → Continue to next attempt (recompile)
- If all solvers fail → Continue to Step 5

**Step 5: Agent Repair**

Dispatch `lean4-proof-repair` agent with Task tool:

```markdown
You are repairing a Lean proof with compiler-guided feedback.

**Error Context:**
FILE: <PATH>
ERROR_TYPE: {errorType}
ERROR_HASH: {errorHash}
LINE: {line}
COLUMN: {column}

MESSAGE:
{message}

GOAL:
{goal}

LOCAL CONTEXT:
{localContext}

CODE SNIPPET:
{codeSnippet}

**Stage:** {stage}
(Stage 1 = Haiku fast, Stage 2 = Sonnet precise)

**Task:**
Generate a MINIMAL unified diff that fixes this error.

**Output:** ONLY the unified diff. No explanations.

Consult `.claude/docs/lean4/compiler-guided-repair.md` for repair strategies.
```

**Agent configuration:**
- If stage == 1: Use `lean4-proof-repair` (Haiku, thinking off)
- If stage == 2: Same agent, but it uses Sonnet internally

**Step 6: Apply Patch**

Agent returns diff. Apply it:
```bash
git apply --ignore-whitespace .repair/agent.diff
```

If apply fails:
```bash
git apply --ignore-whitespace --3way .repair/agent.diff
```

If both fail:
- Log failed attempt
- Continue to next iteration

**Step 7: Log Attempt**

Append to `.repair/attempts.ndjson`:
```json
{
  "attempt": N,
  "errorHash": "...",
  "errorType": "...",
  "stage": 1 or 2,
  "solverSuccess": true/false,
  "agentCalled": true/false,
  "patchApplied": true/false,
  "elapsed": seconds
}
```

### Phase 3: Completion

**Success:**
```
✅ Proof repair SUCCESSFUL after N attempts!

Summary:
- File: <PATH>
- Total attempts: N
- Solver cascade wins: K
- Agent repairs: M
- Stage 2 escalations: L
- Total time: Xs

Attempt log: .repair/attempts.ndjson
```

**Failure:**
```
❌ Repair failed after N attempts

Last error:
- Type: {errorType}
- Hash: {errorHash}
- Message: {message}

Attempt log: .repair/attempts.ndjson

Suggestions:
- Review .repair/attempts.ndjson to see what was tried
- Try /lean4-theorem-proving:repair-interactive for manual control
- Escalate complex errors to manual review
```

---

## Example

User runs:
```
/lean4-theorem-proving:repair-file MyProofs.lean --max-attempts=12
```

You execute:
```
Attempt 1/12:
  Compile: ❌ type mismatch at line 42
  Solver cascade: ❌ (tried 9 solvers)
  Agent (Stage 1): ✓ Generated patch
  Applied: ✓

Attempt 2/12:
  Compile: ❌ unsolved goals at line 45
  Solver cascade: ✓ (simp succeeded!)
  Applied: ✓

Attempt 3/12:
  Compile: ✅ SUCCESS!

✅ Proof repair SUCCESSFUL after 3 attempts!
```

---

## Implementation Notes

**Use TodoWrite to track:**
```
1. Compile and check (Attempt 1/24)
2. Fix error: type_mismatch (Attempt 2/24)
3. Fix error: unsolved_goals (Attempt 3/24)
...
```

Mark completed as you go.

**Error handling:**
- If parseLeanErrors.py fails: Report and exit
- If solverCascade.py crashes: Log and continue (skip to agent)
- If agent errors: Log and continue (try next attempt)
- If max attempts reached: Report failure with diagnostics

**Budget management:**
- Stage 1: Haiku, fast (most cases)
- Stage 2: Sonnet, precise (complex cases)
- Solver cascade: Free (automated)
- Cost-effective compared to blind sampling

---

## Key Success Factors

1. **Tight loop:** Each attempt is fast (2-10s)
2. **Solver first:** Many cases solved without LLM
3. **Low K:** Single sample per attempt (K=1)
4. **Early stopping:** Bail on repeated errors
5. **Stage escalation:** Strong model only when needed
6. **Structured logging:** Learn from attempts

---

*Compiler-guided repair inspired by APOLLO (https://arxiv.org/abs/2505.05758)*
