# Claude Code Migration: V3 → V4

> This guide is specific to Claude Code's plugin system. Non-Claude hosts don't have V3 artifacts to migrate.

This guide helps you upgrade from the legacy 3-plugin system (v3.x) to the unified v4 plugin.

## What Changed

### Plugin Structure

| V3 (3 plugins) | V4 (unified) |
|----------------|--------------|
| `lean4-theorem-proving` | `lean4` |
| `lean4-memories` | Removed (unreliable) |
| `lean4-subagents` | Integrated into `lean4` |

### Commands

| V3 Command | V4 Command |
|------------|------------|
| `/lean4-theorem-proving:fill-sorry` | `/lean4:prove` (or `/lean4:autoprove`) |
| `/lean4-theorem-proving:repair-file` | `/lean4:prove --repair-only` |
| `/lean4-theorem-proving:check-axioms` | `/lean4:checkpoint` (includes axiom check) |
| `/lean4-theorem-proving:golf-proofs` | `/lean4:golf` |
| `/lean4-theorem-proving:build-lean` | Use `lake build` directly |
| `/lean4-theorem-proving:search-mathlib` | Use LSP `lean_leansearch` or scripts |
| (no equivalent) | `/lean4:review` (NEW) |
| (no equivalent) | `/lean4:refactor` (NEW) |
| (no equivalent) | `/lean4:doctor` (NEW) |
| (no equivalent) | `/lean4:disprove` (NEW) |

### Environment Variables

| V3 | V4 |
|----|-----|
| `.claude/tools/lean4/` | `$LEAN4_SCRIPTS/` |
| `.claude/docs/lean4/` | `$LEAN4_REFS/` |
| (copied into workspace) | (stays in plugin directory) |

## Upgrade Steps

### Step 1: Uninstall Old Plugins

```bash
/plugin uninstall lean4-theorem-proving
/plugin uninstall lean4-memories
/plugin uninstall lean4-subagents
```

### Step 2: Install Unified Plugin

```bash
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4
```

### Step 3: Verify Installation

```bash
/lean4:doctor
```

This runs diagnostics to ensure everything is working.

### Step 4: Optional Cleanup

Old plugins may have created files in your workspace:

```
.claude/tools/lean4/      # Scripts (now in plugin)
.claude/docs/lean4/       # Docs (now in plugin)
```

These are now inert (unused) but can be removed:

```bash
rm -rf .claude/tools/lean4 .claude/docs/lean4
```

Or run `/lean4:doctor cleanup` for guided removal.

## Workflow Changes

### V3 Workflow (manual steps)

```
1. /lean4-theorem-proving:fill-sorry  # One at a time
2. lake build                         # Manual verification
3. /lean4-theorem-proving:check-axioms
4. git commit                         # Manual
```

### V4 Workflow (guided proving)

```
1. /lean4:prove            # Guided: asks preferences, cycle-by-cycle
2. (prove handles fills, builds, commits per cycle)
3. /lean4:review           # Read-only quality check
4. /lean4:refactor         # Strategy-level simplification (optional)
5. /lean4:golf             # Tactic-level optimization (optional)
6. /lean4:checkpoint       # Verified save point
7. git push                # Manual (safety guardrail)
```

Or for unattended work: `/lean4:autoprove` (autonomous with explicit stop budgets).

## Key Differences

### Planning Phase (NEW)

`/lean4:prove` asks for your preferences at startup (if not passed via flags):
- **Planning preference:** Start with a planning phase or skip straight to work
- **Review source:** Internal (planner mode) / External (interactive handoff) / Both / None

### Safety Guardrails (NEW)

V4 blocks certain git operations when working inside a Lean project (detected by `lakefile.lean`, `lean-toolchain`, or `lakefile.toml` in the directory tree). Outside Lean projects, guardrails do not fire.

- `git push` - Use `/lean4:checkpoint`, then push manually
- `git commit --amend` - Each change is a new commit
- `gh pr create` - Review first with `/lean4:review`

Override with `LEAN4_GUARDRAILS_DISABLE=1` (skip all) or `LEAN4_GUARDRAILS_FORCE=1` (enforce everywhere). `LEAN4_GUARDRAILS_DISABLE` takes precedence over `LEAN4_GUARDRAILS_FORCE`.

Two independent soft-gate policies (each `ask` | `allow` | `block`, default `ask`):
- `LEAN4_GUARDRAILS_COLLAB_POLICY` — controls `git push`, `git commit --amend`, `gh pr create`.
- `LEAN4_GUARDRAILS_DESTRUCTIVE_POLICY` — controls path-scoped destructive ops (`git checkout -- <path…>`, `git restore <path…>`).

For a single soft-gated command in `ask` mode, prefix with the bypass token instead (command prefix only, not an env var): `LEAN4_GUARDRAILS_BYPASS=1 git push origin main`. The token applies to either soft-gate category.

**Whole-worktree** destructive operations (`git reset --hard`, `git clean -f`/`-fd`/`-fdx`, `git checkout .`/`-- .`/`-- :/`/`HEAD -- .`, `git restore .`/`./`/`:/`, `git restore --staged --worktree`) remain **hard-blocked** regardless of either policy or the bypass token. The blast radius is unbounded and reflog can't recover uncommitted edits; `clean -f` can't recover untracked files at all. Pure unstaging (`git restore --staged <anything>` without `--worktree`) is always allowed since it only touches the index.

### Memory System (REMOVED)

The v3 `lean4-memories` plugin is not included in v4. It was unreliable and has been removed. The proving workflow provides better guidance without the memory overhead.

## Legacy Access

If you need the old 3-plugin version:

### Pin to Legacy Tag

```bash
/plugin marketplace add cameronfreer/lean4-skills@v3.4.2-legacy
```

### Or Use Legacy Branch

```bash
/plugin marketplace add cameronfreer/lean4-skills#legacy-marketplace
```

## Troubleshooting

### "LEAN4_SCRIPTS not set"

The bootstrap hook didn't run. Try:
1. Restart Claude Code session
2. Run `/lean4:doctor` to check environment

### Commands not found

Make sure you installed from the v4 version:
```bash
/plugin install lean4
```

### Scripts not working

The scripts now live in the plugin directory. Use `$LEAN4_SCRIPTS/` prefix:
```bash
${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/sorry_analyzer.py" . --format=summary --report-only
```

Both `lib/scripts/` and `scripts/` (compat alias) resolve to the same directory. If your environment doesn't preserve symlinks (e.g., archive extraction), use `$LEAN4_SCRIPTS` as the canonical path.

### Need help?

Run `/lean4:doctor` for full diagnostics.

## V4.5.1 → V4.5.2

**Collab policy split + `host` mode default.** The single
`LEAN4_GUARDRAILS_COLLAB_POLICY` knob is replaced by three per-op
policies, each with a new `host` value that defers to Claude Code's
native `Bash(...)` permission rule (`allow`/`ask`/`deny`). The default
for each per-op policy is `host`, which stops the hook from blocking
ordinary `git push` with `exit 2` + bypass-token retries — Claude
Code's permission layer handles consent natively (including
"ask once, remember" UX).

### Env var changes

| Old (v4.5.1) | New (v4.5.2+) |
|---|---|
| `LEAN4_GUARDRAILS_COLLAB_POLICY=ask` (default) | Per-op default: `host` (each of PUSH/AMEND/PR_CREATE) |
| Single knob for push + amend + pr-create | `LEAN4_GUARDRAILS_PUSH_POLICY`, `LEAN4_GUARDRAILS_AMEND_POLICY`, `LEAN4_GUARDRAILS_PR_CREATE_POLICY` (each `host` \| `ask` \| `allow` \| `block`) |

### Back-compat: no action needed if you set `COLLAB_POLICY`

The legacy `LEAN4_GUARDRAILS_COLLAB_POLICY` var is honored as the
fallback for any per-op policy you haven't explicitly set. So:

- If you set `COLLAB_POLICY=allow` in your settings, all three
  ops continue to soft-gate with `allow` semantics (unchanged).
- If you set `COLLAB_POLICY=block`, same (unchanged).
- If you set `COLLAB_POLICY=ask` explicitly, push/amend/pr-create
  continue to block-until-bypass (unchanged).
- If you didn't set `COLLAB_POLICY` and relied on its `ask` default,
  **your default is now `host`**. To preserve the old behavior,
  add `LEAN4_GUARDRAILS_COLLAB_POLICY=ask` to your settings.

You can also mix: set `COLLAB_POLICY=ask` (everything blocks until
bypass) but `LEAN4_GUARDRAILS_PUSH_POLICY=host` (only push delegates
to Claude Code). Per-op vars always win for the op they cover.

### Push variants hard-blocked (new tier-3, non-bypassable)

Five push forms that previously fell through the soft-gate are now
hard-blocked regardless of `PUSH_POLICY` — same posture as
`git reset --hard`:

- `git push --force` / `-f`
- `git push --force-with-lease[=<ref>]`
- `git push --mirror`
- `git push --delete` / `-d <ref>`
- `git push <remote> :<ref>` (legacy ref-delete syntax)

Escape hatch: `LEAN4_GUARDRAILS_DISABLE=1 git push --force ...` for
the specific command. `--dry-run` and `git stash push` remain
exempted from all push gates (unchanged).

### Recommended `.claude/settings.local.json`

With `host` as the default, you'll want to tell Claude Code to
`ask` before push and pr-create (otherwise the model could push
without any prompt):

```json
{
  "permissions": {
    "ask": [
      "Bash(git push *)",
      "Bash(gh pr create *)",
      "Bash(git commit --amend *)"
    ]
  }
}
```

Claude Code then handles "ask once, remember" via its native
permission UI — typically a per-session approval that doesn't
re-prompt on subsequent invocations.

## V4.4.0 → V4.4.1

**Proof-editing agents renamed** to drop the `lean4-` prefix, fixing the dispatch name stutter.

| Old name | New name | Old dispatch | New dispatch |
|----------|----------|--------------|--------------|
| `lean4-sorry-filler-deep` | `sorry-filler-deep` | `lean4:lean4-sorry-filler-deep` | `lean4:sorry-filler-deep` |
| `lean4-proof-repair` | `proof-repair` | `lean4:lean4-proof-repair` | `lean4:proof-repair` |
| `lean4-proof-golfer` | `proof-golfer` | `lean4:lean4-proof-golfer` | `lean4:proof-golfer` |
| `lean4-axiom-eliminator` | `axiom-eliminator` | `lean4:lean4-axiom-eliminator` | `lean4:axiom-eliminator` |

If you have external tooling or scripts that dispatch agents by the old names, update them to the new names.

## V4.3.x → V4.4.0

**Separates drafting from proving** with a cleaner command surface.

### What Changed and Why

- `draft` is the honest name for "translate informal → formal skeleton." Old `formalize` did this plus proof attempts, which muddied the separation from `prove`.
- `formalize` now means the full pipeline: draft a skeleton and prove it. This is a superset of old behavior.
- `autoformalize` surfaces the `autoprove --formalize=auto` workflow as a first-class command with cleaner flag names.
- Proof engines (`prove`/`autoprove`) no longer touch declaration headers. If the statement is wrong, they recommend `redraft` instead of silently rewriting.

### Migration Table

| Old invocation | What to use now | Compatibility |
|---|---|---|
| `/lean4:formalize "claim"` | `/lean4:formalize "claim"` (superset: now also proves) or `/lean4:draft "claim"` (skeleton only) | Yes — formalize still accepts this |
| `/lean4:formalize --rigor=axiomatic "claim"` | `/lean4:formalize --rigor=axiomatic "claim"` | Yes — rigor stays on formalize |
| `/lean4:formalize "claim"` → save → `/lean4:prove` later | `/lean4:draft "claim"` → save → `/lean4:prove` (cleaner separation) | Yes — old formalize still works for this pattern too |
| `/lean4:autoprove --formalize=auto --source=paper.pdf --claim-select=first --formalize-out=Paper.lean` | `/lean4:autoformalize --source=paper.pdf --claim-select=first --out=Paper.lean` | Old flags still accepted on autoprove (deprecated, functional) |
| `/lean4:autoprove --formalize=auto --formalize-rigor=checked ...` | `/lean4:autoformalize --rigor=checked ...` | `--formalize-rigor` → `--rigor` on autoformalize |
| `/lean4:autoprove --formalize=restage` | Old flag still works (deprecated). For interactive redrafting of existing scope, use `/lean4:formalize`. | No first-class autonomous replacement — `autoformalize` requires `--source` |
| `/lean4:prove --deep` with statement generalization | Statement changes now require `/lean4:formalize`; prove emits `next_action = redraft` | **Behavioral narrowing** — only breaking change |

## V4.0.4 → V4.0.5

**`/lean4:autoprover` split into two commands:**
- `/lean4:prove` — guided, cycle-by-cycle (asks before each cycle)
- `/lean4:autoprove` — autonomous, with explicit stop budgets

Both share the same cycle engine and most flags. Key differences:
- **prove-only:** `--deep=ask` (interactive prompt), `--planning=ask`, `--commit=ask` (per-commit confirmation)
- **autoprove-only:** `--max-cycles`, `--max-total-runtime`, `--max-stuck-cycles`, `--max-consecutive-deep-cycles` (autoprove coerces `--commit=ask` and `--review-source=external` to non-interactive values)
- **Different defaults:** autoprove uses `--batch-size=2`, `--deep=stuck`, `--golf=never`, `--commit=auto`; prove uses `--batch-size=1`, `--deep=never`, `--golf=prompt`, `--commit=ask`

## V4.0.8 → V4.0.9

**v4.0.9:** Grind, simprocs, metaprogramming, linters, FFI, verso-docs, and profiling content (from PR #10, Alok Singh) integrated as reference files in `plugins/lean4/skills/lean4/references/`. No separate plugins needed.

New reference files: `grind-tactic.md`, `simproc-patterns.md`, `metaprogramming-patterns.md`, `linter-authoring.md`, `ffi-patterns.md`, `verso-docs.md`, `profiling-workflows.md`. All are outside the default prove/autoprove loop.

## See Also

- [README.md](README.md) - Plugin documentation
- [SKILL.md](skills/lean4/SKILL.md) - Core skill reference
- [Commands](commands/) - Command documentation
