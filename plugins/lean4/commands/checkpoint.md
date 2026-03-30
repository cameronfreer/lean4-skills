---
name: checkpoint
description: Save progress with a safe commit checkpoint
user_invocable: true
---

# Lean4 Checkpoint

Creates a checkpoint with per-file and project-wide build verification, axiom check, and commit.

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

1. **Verify Touched Files** - For each existing added/modified `.lean` file in the staged set for this checkpoint, compile individually:
   ```bash
   lake env lean <path/to/File.lean>   # from project root
   ```
   If any file fails, stop and report the error before proceeding.
2. **Verify Build** - Run `lake build` for the project-wide gate (catches cross-file issues not visible in per-file compilation)
3. **Check Axioms** - Verify no unwanted custom axioms:
   ```bash
   bash "$LEAN4_SCRIPTS/check_axioms_inline.sh" .
   ```
   Note: checks top-level unindented declarations in the first namespace of each file. Nested namespaces, sections, and indented declarations may not be checked (#92).
4. **Count Sorries** - Report current sorry count:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/sorry_analyzer.py" . --format=summary
   ```
5. **Stage and Commit** - Stage only files touched during this session, then commit:
   ```bash
   git add <files touched during this session>
   git diff --cached --name-only   # print exact staged set
   git commit -m "checkpoint(lean4): [summary]"
   ```
   Never use `git add -A` or broad glob patterns.
6. **Report Status** - Show what was saved

## Output

```markdown
## Checkpoint Created

**Commit:** [hash] - [message]
**Touched files compiled:** ✓ [N] files
**Project build:** ✓ passing
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
- `/lean4:refactor` - Strategy-level proof simplification
- [Examples](../skills/lean4/references/command-examples.md#checkpoint)
