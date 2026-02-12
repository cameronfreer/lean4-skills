---
name: checkpoint
description: Save progress with a safe commit checkpoint
user_invocable: true
---

# Lean4 Checkpoint

Creates a verified checkpoint of your current proof progress.

## Usage

```
/lean4:checkpoint
/lean4:checkpoint "optional custom message"
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| message | No | Custom commit message suffix |

## Actions

1. **Verify Build** - Run `lake build` to ensure code compiles (this is a project-wide gate — runs full `lake build`, not file-level)
2. **Check Axioms** - Verify no unwanted custom axioms:
   ```bash
   bash $LEAN4_SCRIPTS/check_axioms_inline.sh src/*.lean
   ```
3. **Count Sorries** - Report current sorry count:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/sorry_analyzer.py . --format=summary
   ```
4. **Stage and Commit** - Stage changes and create commit:
   ```bash
   git add -A && git status --short
   git commit -m "checkpoint(lean4): [summary]"
   ```
5. **Report Status** - Show what was saved

## Output

```markdown
## Checkpoint Created

**Commit:** [hash] - [message]
**Build:** ✓ passing
**Sorries:** [N] remaining
**Axioms:** [status]

**Next steps:**
- Continue with `/lean4:prove`
- Push manually when ready: `git push`
```

## Safety

- Does NOT push to remote (manual only)
- Does NOT create PRs (manual only)
- Does NOT amend commits (each checkpoint = new commit)
- Will NOT create checkpoint if build fails

## Rollback

```bash
git reset --soft HEAD~1   # Undo last, keep staged
git reset HEAD~1          # Undo last, keep unstaged
git reset HEAD~N          # Undo last N commits
```

**Warning:** Only use reset before pushing.

## See Also

- `/lean4:prove` - Guided cycle-by-cycle proving
- `/lean4:review` - Read-only code review
- [Examples](../skills/lean4/references/command-examples.md#checkpoint)
