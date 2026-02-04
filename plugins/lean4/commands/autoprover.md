---
name: autoprover
description: Planning-first agentic theorem-proving loop with guardrails
user_invocable: true
---

# Lean4 Autoprover

Main entry point for automated theorem proving with planning-first workflow and safety guardrails.

---

## Phase 1: Planning (MANDATORY)

**Before any proof work, gather user preferences:**

### 1.1 Discover Current State

Run sorry analysis to understand scope:

```bash
${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/sorry_analyzer.py . --format=json
```

Report summary:
- Total sorries found
- Files affected
- Complexity distribution (easy/medium/hard)

### 1.2 Ask Planning Questions

Use AskUserQuestion to gather preferences:

**Question 1 - Ingredients Policy:**
- **mathlib-only** (Recommended) - Only use lemmas from mathlib imports
- **project-local OK** - Can use lemmas defined in this project
- **specific imports** - User specifies allowed imports

**Question 2 - Fill Scope:**
- **all sorries** - Fill every sorry in the project
- **specific files** - User specifies which files
- **tagged only** - Only sorries marked with `-- FILL` comment

**Question 3 - Touch Policy:**
- **minimal** (Recommended) - Only modify lines containing sorries
- **refactor OK** - Can extract helpers, reorganize proofs
- **full access** - Can modify any file as needed

**Question 4 - Review Cadence:**
- **every sorry** - Pause after each sorry for confirmation
- **every file** - Pause after completing each file
- **every 5** (Recommended) - Pause every 5 sorries
- **manual** - Run until done or stuck, then report

### 1.3 Present Plan Preview

After gathering preferences, show the user:

```markdown
## Autoprover Plan

**Scope:** [N] sorries across [M] files
**Policy:** [ingredients] / [touch] / [review cadence]

### Attack Order (easiest first)

1. `File1.lean:42` - `helper_lemma` (easy: type equality)
2. `File1.lean:89` - `main_theorem` (medium: needs mathlib search)
3. `File2.lean:15` - `auxiliary_fact` (hard: may need refactoring)
...

### Estimated Changes

- Lines to modify: ~[X]
- New commits: ~[Y]
- Files affected: [list]

**Ready to proceed?** (yes/no/adjust)
```

**User must confirm before any writes.**

---

## Phase 2: Main Loop

Execute the following loop until all sorries are filled or user stops:

### 2.1 DISCOVER

```bash
${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/sorry_analyzer.py . --format=json
```

Parse output to get prioritized sorry queue (easiest first based on goal complexity).

### 2.2 SELECT

Pick next sorry from queue. Read context:
- Goal type and local context
- Surrounding proof structure
- Available hypotheses

### 2.3 ATTEMPT

**Step A: Search mathlib first**
```bash
bash $LEAN4_SCRIPTS/smart_search.sh "goal description" --source=all
```

If exact lemma found → apply directly.

**Step B: Try automated tactics**
Solver cascade (in order, stop on first success):
1. `rfl`
2. `simp`
3. `ring` / `linarith` / `nlinarith` / `omega`
4. `exact?` / `apply?`
5. `aesop`

**Step C: If automation fails, dispatch agent**
- Simple sorries → `lean4-sorry-filler` (fast, Haiku)
- Complex sorries → `lean4-sorry-filler-deep` (thorough, Opus)

### 2.4 VALIDATE

After each sorry fill:

```bash
lake build
```

If build fails:
- Dispatch `lean4-proof-repair` agent
- Max 3 repair attempts per sorry
- If still failing, mark as "needs manual attention" and continue

Check axioms:
```bash
bash $LEAN4_SCRIPTS/check_axioms.sh [file]
```

Verify:
- No new custom axioms introduced
- Sorry count decreased (not increased!)

### 2.5 COMMIT

Create atomic commit for each filled sorry:

```bash
git add [file]
git commit -m "fill(lean4): [theorem_name] - [brief description]"
```

**NEVER use `--amend`** - each sorry gets its own commit for easy rollback.

### 2.6 CHECKPOINT

At review cadence intervals, run `/lean4:checkpoint` internally:
- Verify build passes
- Verify axiom hygiene
- Report progress

### 2.7 REVIEW

At configured cadence, pause and report:

```markdown
## Progress Report

**Filled:** [X] / [total] sorries
**Files:** [list of modified files]
**Commits:** [N] new commits

**Current sorry:** [file:line - name]
**Status:** [working / stuck / complete]

**Options:**
- **continue** - Keep going
- **stop** - Stop here, keep progress
- **adjust** - Change settings
- **rollback [N]** - Undo last N commits
```

Wait for user input before continuing.

### 2.8 REPEAT

Return to step 2.1 until:
- All sorries filled, OR
- User stops, OR
- Stuck on same sorry 3 times (escalate to user)

---

## Phase 3: Completion

When all sorries are filled (or user stops):

```markdown
## Autoprover Complete

**Session Summary:**
- Sorries filled: [X] / [total]
- Commits created: [N]
- Files modified: [list]
- Time elapsed: [duration]

**Remaining work:**
- [list any unfilled sorries with notes]

**Next steps:**
1. Run `/lean4:review` for code review
2. Push manually when ready: `git push`
3. Create PR manually: `gh pr create`

**Guardrails reminder:**
Push and PR creation are blocked during autoprover.
This ensures you review changes before sharing.
```

---

## Guardrails (Enforced by Hooks)

The following are **blocked** during autoprover sessions:

| Command | Why Blocked | Alternative |
|---------|-------------|-------------|
| `git push` | Ensure review before sharing | Push manually after `/lean4:checkpoint` |
| `git commit --amend` | Preserve rollback granularity | Each sorry = one commit |
| `gh pr create` | Ensure review before PR | Create PR manually after review |

These guardrails are enforced by `hooks/guardrails.sh`.

---

## Fallback Behaviors

**If sorry_analyzer.py unavailable:**
```bash
grep -rn "sorry" --include="*.lean" .
```

**If smart_search.sh unavailable:**
- Use LSP `lean_leansearch` if available
- Fall back to `grep` in `.lake/packages/mathlib`

**If lake build times out:**
- Build individual file: `lake build ProjectName.FileName`
- Skip slow files, continue with others

**If agent fails repeatedly:**
- Mark sorry as "needs manual attention"
- Continue with next sorry
- Report at review checkpoint

---

## Example Session

```
User: /lean4:autoprover

Claude: Running sorry analysis...

Found 12 sorries across 3 files:
- Core.lean: 5 sorries (2 easy, 2 medium, 1 hard)
- Helpers.lean: 4 sorries (3 easy, 1 medium)
- Main.lean: 3 sorries (1 easy, 2 hard)

[Asks planning questions via AskUserQuestion]

User selects: mathlib-only, all sorries, minimal touch, every 5

Claude:
## Autoprover Plan

Scope: 12 sorries across 3 files
Policy: mathlib-only / minimal / review every 5

Attack Order:
1. Helpers.lean:15 - trivial_lemma (easy)
2. Helpers.lean:28 - helper_bound (easy)
...

Ready to proceed? (yes/no/adjust)

User: yes

Claude: Starting autoprover...

[1/12] Helpers.lean:15 - trivial_lemma
  Searching mathlib... found exact lemma
  Applying: exact Nat.add_comm
  Building... ✓
  Committing... ✓

[2/12] Helpers.lean:28 - helper_bound
  Searching mathlib... no exact match
  Trying automation... linarith succeeds
  Building... ✓
  Committing... ✓

...

[5/12] Progress checkpoint
  Filled: 5/12 sorries
  Continue? (yes/stop/adjust)

User: continue

...

[12/12] Complete!

Session Summary:
- Sorries filled: 12/12
- Commits created: 12
- Files modified: Core.lean, Helpers.lean, Main.lean

Next steps:
1. Run /lean4:review for code review
2. Push manually when ready
```

---

## See Also

- `/lean4:checkpoint` - Manual checkpoint creation
- `/lean4:review` - Read-only code review
- `/lean4:doctor` - Diagnostics and troubleshooting
- [sorry-filling.md](../skills/lean4/references/sorry-filling.md) - Detailed sorry-filling patterns
- [compiler-guided-repair.md](../skills/lean4/references/compiler-guided-repair.md) - Repair workflow details
