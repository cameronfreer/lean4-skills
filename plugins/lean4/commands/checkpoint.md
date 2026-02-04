---
name: checkpoint
description: Save progress with a safe commit checkpoint
user_invocable: true
---

# Lean4 Checkpoint

Creates a verified checkpoint of your current proof progress.

---

## What It Does

1. **Verify Build** - Runs `lake build` to ensure code compiles
2. **Check Axioms** - Verifies no unwanted custom axioms
3. **Count Sorries** - Reports current sorry count
4. **Create Commit** - Commits with descriptive checkpoint message
5. **Report Status** - Shows what was saved

---

## Usage

```
/lean4:checkpoint
/lean4:checkpoint "optional custom message"
```

---

## Workflow

### Step 1: Verify Build

```bash
lake build
```

If build fails:
- Report errors
- Do NOT create checkpoint
- Suggest fixes or `/lean4:autoprover` to continue

### Step 2: Check Axioms

```bash
bash $LEAN4_SCRIPTS/check_axioms_inline.sh src/*.lean
# For recursive: shopt -s globstar && bash $LEAN4_SCRIPTS/check_axioms_inline.sh **/*.lean
# Note: Adjust path to match your project layout (e.g., *.lean for flat projects)
```

Report:
- Standard axioms (OK): `propext`, `Classical.choice`, `Quot.sound`
- Custom axioms (WARNING): List with locations

### Step 3: Count Sorries

```bash
${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/sorry_analyzer.py . --format=summary
```

Report:
- Total sorry count
- Files with sorries

### Step 4: Stage and Commit

```bash
git add -A
git status --short
```

Show user what will be committed. Then:

```bash
git commit -m "checkpoint(lean4): [summary]

Sorries: [N]
Axioms: [standard only / M custom]
Build: passing"
```

**NEVER use `--amend`** - each checkpoint is a new commit.

### Step 5: Report

```markdown
## Checkpoint Created

**Commit:** [hash] - [message]
**Build:** ✓ passing
**Sorries:** [N] remaining
**Axioms:** [status]

**Next steps:**
- Continue with `/lean4:autoprover`
- Review with `/lean4:review`
- Push manually when ready: `git push`
```

---

## When to Use

- **During autoprover** - Called automatically at review cadence
- **Manual save points** - When you want to preserve progress
- **Before risky changes** - Create rollback point
- **End of session** - Save work before stopping

---

## What It Does NOT Do

- **Does NOT push** - You push manually after review
- **Does NOT create PR** - You create PR manually
- **Does NOT amend** - Each checkpoint = new commit

These are intentional guardrails to ensure you review before sharing.

---

## Rollback

If you need to undo a checkpoint:

```bash
# Undo last commit, keep changes staged
git reset --soft HEAD~1

# Undo last commit, keep changes unstaged
git reset HEAD~1

# Undo last N commits
git reset HEAD~N
```

**Warning:** Only use these before pushing.

---

## Example

```
User: /lean4:checkpoint

Claude: Creating checkpoint...

Building project...
✓ lake build passed

Checking axioms...
✓ Standard axioms only (propext, Classical.choice)

Counting sorries...
→ 3 sorries remaining in 2 files

Staging changes...
→ 5 files modified

Creating commit...
✓ Commit a1b2c3d: checkpoint(lean4): 3 sorries remaining, build passing

## Checkpoint Created

Commit: a1b2c3d - checkpoint(lean4): 3 sorries remaining, build passing
Build: ✓ passing
Sorries: 3 remaining
Axioms: standard only

Next steps:
- Continue with /lean4:autoprover
- Push manually when ready: git push
```

---

## See Also

- `/lean4:autoprover` - Main theorem-proving workflow
- `/lean4:review` - Read-only code review
- `/lean4:doctor` - Diagnostics
