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
/lean4:checkpoint --mathlib-mk-all      # force the mk_all root-file gate
/lean4:checkpoint --no-mathlib-mk-all   # skip the mk_all root-file gate
```

## Invocation Contract

Interpret this command's inputs per the
[Command Invocation Contract](../skills/lean4/references/command-invocation.md).

**Primary path (hook-validated):** If a `validated-invocation` block for this
command appears in context, treat it as the authoritative interpretation of
parser-decidable inputs and do **not** re-parse the raw invocation text for
those inputs. Start by reading all parser-decided fields from the block. Emit
the final **Resolved Inputs** summary from the block values.
See [Validated Invocation Block](../skills/lean4/references/command-invocation.md#validated-invocation-block-host-provided).

**Fallback path (other hosts):** If no `validated-invocation` block is present,
parse the raw invocation text against this command's input table before acting.

Startup requirements:

1. Emit a **Resolved Inputs** block with explicit values, defaults, ignored
   flags, and startup validation errors — including the effective mk_all-gate
   decision and its source (`flag`, the helper's `intent.source`, or
   `helper-failure`).
2. Refuse to start on startup validation errors (e.g. both `--mathlib-mk-all`
   and `--no-mathlib-mk-all`).

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| message | No | Custom commit message suffix |
| --mathlib-mk-all | No | Force the Generated Root Files gate on, overriding project-context detection. Mutually exclusive with `--no-mathlib-mk-all`. |
| --no-mathlib-mk-all | No | Force the Generated Root Files gate off, overriding project-context detection. Mutually exclusive with `--mathlib-mk-all`. |

## Actions

1. **Verify Touched Files** - For each existing added/modified `.lean` file in the **candidate set** for this checkpoint — the files touched during this session that step 5 will stage, determined independently of the current git index (staging happens later) — compile individually:
   ```bash
   lake env lean <path/to/File.lean>   # from project root
   ```
   If any file fails, stop and report the error before proceeding.
2. **Generated Root Files gate (mathlib)** - See [Generated Root Files](#generated-root-files-gate) below. Runs before the project build; skips entirely unless the gate fires.
3. **Verify Build** - Run `lake build` for the project-wide gate (catches cross-file issues not visible in per-file compilation)
4. **Best-effort Axiom Scan** - Scan for non-standard axioms in top-level declarations:
   ```bash
   lean4-skills-check-axioms-inline .
   ```
   Note: checks top-level unindented declarations across all namespaces in each file (nested, sibling, and dotted namespaces are tracked correctly; sections are handled without leaking into the qualified name). Recognizes `theorem|lemma|def|instance|abbrev|example|structure|class|inductive|axiom|constant`, optionally prefixed by `noncomputable`, `unsafe`, `partial`, or `nonrec`. Indented declarations and unicode-identifier decls are not matched — files whose decls all fall in those classes are surfaced as UNVERIFIED (exit 1, not a silent pass). The script temporarily edits files in place while running — only use on version-controlled files, and avoid concurrent editors or watchers.
5. **Count Sorries** - Report current sorry count:
   ```bash
   lean4-skills-sorry-analyzer . --format=summary
   ```
6. **Stage and Commit** - Stage only files touched during this session, then commit:
   ```bash
   git add <files touched during this session>
   git diff --cached --name-only   # print exact staged set
   git commit -m "checkpoint(lean4): [summary]"
   ```
   Never use `git add -A` or broad glob patterns.
7. **Report Status** - Show what was saved

## Generated Root Files gate

Mathlib's generated root-import aggregators (`Mathlib.lean`, `Mathlib/Tactic.lean`, …) go stale when a `.lean` file is added, renamed, or deleted, and mathlib CI runs `lake exe mk_all --check` as a dedicated gate. This step catches that follow-up **before** the main build — but only when the current work is plausibly aimed at upstream mathlib contribution, so a personal mathlib fork used for experimentation is not blocked on every checkpoint.

**1. Resolve whether the gate fires** (precedence — a flag resolving to true wins; explicit false behaves like omission):
- `--mathlib-mk-all` true → gate fires (explicit opt-in).
- else `--no-mathlib-mk-all` true → gate skipped; done.
- else run `lean4-skills-project-context --from "$PWD"` and validate the full record exactly as `/lean4:draft` does: `schema` = `project-context/v1`, `intent.contributing_upstream` a string in `yes | no | unknown`, `intent.source` a string in its domain — any missing/non-string/out-of-domain value is malformed helper output. `yes` → gate fires; `no`, `unknown`, or malformed/failed helper → gate skipped. `mk_all_declared` is **never** consulted; availability is decided by actually running the command.

**Explicit opt-in never fails open.** When the gate was requested explicitly (`--mathlib-mk-all`), an inability to locate the project root or inspect the candidate set is a **stop**, not a silent skip. Inferred intent may fail open (skip); an explicitly requested gate may not.

**2. Detect root-affecting candidate changes.** The **candidate set** is the session-touched files this checkpoint will stage — not unrelated local work. Pass them NUL-delimited to the helper, anchored at the project root the previous step returned (its non-null top-level `root`):
```bash
printf '%s\0' "${candidate_paths[@]}" \
  | lean4-skills-checkpoint-mathlib-roots --root "$project_root"
```
It emits a `checkpoint-mathlib-roots/v1` JSON record listing added/deleted `.lean` files under `<root>/Mathlib/` (renames surface as delete + add). Exit 0 = valid (including no changes); 2 = usage; 4 = git/operational failure. On exit 4 (or a null `root`), **stop** — activation cannot be determined safely; do not skip and do not proceed to the build. If `changes` is empty, there is nothing to check → proceed to Verify Build.

**3. Run the check.** When `changes` is non-empty, run `lake exe mk_all --check` from `$project_root` and **preserve its output verbatim**:
- Output explicitly names outdated files → stop before Verify Build; report those lines as-is and print the remediation `lake exe mk_all` (the same string [diagnose §16](../skills/lean4/references/compilation-errors.md#16-cannot-import-non-module-from-module) surfaces). **Never** auto-rewrite root files.
- Any other nonzero (executable unavailable, Lake error) → preserve the output, state the gate **could not complete**, stop before Verify Build, and do **not** invent stale filenames.
- Exit 0 → roots are current; proceed.

**Global-check limitation (honest scope note).** The candidate set controls only whether the gate *activates*; once activated, `lake exe mk_all --check` inspects the actual checkout, so unrelated local changes can affect its result. This does not violate "unrelated work must not trigger the gate" — activation is candidate-scoped — but candidate-level isolation would require a clean-worktree/stash mechanism, which is out of scope for v1.

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
