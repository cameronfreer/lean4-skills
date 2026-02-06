# Migration Guide: V3 → V4

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
| (no equivalent) | `/lean4:doctor` (NEW) |

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
4. /lean4:golf             # Optional optimization
5. /lean4:checkpoint       # Verified save point
6. git push                # Manual (safety guardrail)
```

Or for unattended work: `/lean4:autoprove` (autonomous with stop rules).

## Key Differences

### Planning Phase (NEW)

V4 asks for your preferences before making changes:
- **Scope:** All sorries / specific files / specific theorems
- **Approach:** Conservative / Balanced / Aggressive
- **Review cadence:** Every change / every 5 / manual

### Safety Guardrails (NEW)

V4 blocks certain git operations during sessions:
- `git push` - Use `/lean4:checkpoint`, then push manually
- `git commit --amend` - Each change is a new commit
- `gh pr create` - Review first with `/lean4:review`

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
$LEAN4_SCRIPTS/sorry_analyzer.py .
```

### Need help?

Run `/lean4:doctor` for full diagnostics.

## V4.0.4 → V4.0.5

**`/lean4:autoprover` split into two commands:**
- `/lean4:prove` — guided, cycle-by-cycle (asks before each cycle)
- `/lean4:autoprove` — autonomous, with hard stop rules

Both share the same cycle engine and most flags. Key differences:
- **prove-only:** `--deep=ask` (interactive prompt), `--planning=ask`
- **autoprove-only:** `--max-cycles`, `--max-total-runtime`, `--max-stuck-cycles`, `--max-consecutive-deep-cycles`
- **Different defaults:** autoprove uses `--batch-size=2`, `--deep=stuck`, `--golf=never`; prove uses `--batch-size=1`, `--deep=never`, `--golf=prompt`

## See Also

- [README.md](README.md) - Plugin documentation
- [SKILL.md](skills/lean4/SKILL.md) - Core skill reference
- [Commands](commands/) - Command documentation
