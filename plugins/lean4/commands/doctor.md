---
name: doctor
description: Diagnostics, cleanup, and migration help
user_invocable: true
---

# Lean4 Doctor

Diagnostics, troubleshooting, and migration assistance for the Lean4 plugin.

## Usage

```
/lean4:doctor                    # Full diagnostic (plugin + workspace)
/lean4:doctor env                # Environment only
/lean4:doctor migrate            # Detect legacy installs (read-only)
/lean4:doctor migrate --global   # Include user-level ~/.claude scan
/lean4:doctor cleanup            # Show stale files + removal commands
/lean4:doctor cleanup --apply    # Actually remove stale files
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| mode | No | `env`, `migrate`, `cleanup`, or full (default) |
| --global | No | Include user-level paths (~/); migrate only |
| --apply | No | Execute removals; cleanup only |

## Actions

### 1. Environment Check

| Tool | Check | Required |
|------|-------|----------|
| `lean` | `lean --version` | Yes |
| `lake` | `lake --version` | Yes |
| `python3` | `python3 --version` | For scripts |
| `git` | `git --version` | For commits |
| `rg` | `rg --version` | Optional (faster search) |

Environment variables: `LEAN4_PLUGIN_ROOT`, `LEAN4_SCRIPTS`, `LEAN4_REFS`, `LEAN4_PYTHON_BIN`

### 1b. MCP Tools

| Check | Detection | Status |
|-------|-----------|--------|
| Lean LSP MCP | `lean_goal` tool available in this session | Optional (sub-second feedback) |
`✓ … available` or `⚠ … unavailable — see INSTALLATION.md`

### 2. Plugin Check

Verify structure and permissions:
```
plugins/lean4/
├── .claude-plugin/plugin.json
├── commands/     (*.md command files)
├── hooks/        (executable .sh)
├── skills/lean4/ (SKILL.md + references/)
├── agents/       (4 files)
└── lib/scripts/  (12 files, executable)
```

### 3. Project Check

- `lakefile.lean` and `lean-toolchain` present
- `lake build` passes
- Sorry count reported

### 4. Migration Detection (read-only)

Detects legacy v3 artifacts without making changes.

**Legacy plugin installs:**
```
~/.claude/plugins/lean4-theorem-proving/
~/.claude/plugins/lean4-subagents/
~/.claude/plugins/lean4-memories/
```

**Stale environment variables:**
- `LEAN4_PLUGIN_ROOT` pointing to old path (e.g., `lean4-theorem-proving`)
- `LEAN4_SCRIPTS` not under current plugin
- `LEAN4_REFS` not under current plugin

**Name mapping (v3 → v4):**

| V3 | V4 |
|----|-----|
| `lean4-theorem-proving` | `lean4` |
| `lean4-memories` | Removed |
| `lean4-subagents` | Integrated |
| `/lean4-theorem-proving:*` | `/lean4:*` |

**With `--global`:** Also scans user-level `~/.claude/` for duplicates or stale plugin versions. Only when explicitly requested.

### 5. Cleanup

Detects and optionally removes obsolete artifacts.

**Workspace paths checked:**
```
.claude/tools/lean4/
.claude/docs/lean4/
.claude/lean4-*/           # Any lean4-* directories
```

**User-level paths (with --global):**
```
~/.claude/plugins/lean4-theorem-proving/
~/.claude/plugins/lean4-subagents/
~/.claude/plugins/lean4-memories/
```

**Behavior:**
- Default: Report findings, show `rm -rf` commands, do NOT execute
- With `--apply`: Interactive per-item confirmation

**Interactive prompt (`--apply`):**
```
Found 3 items to clean:
  [1] .claude/tools/lean4/
  [2] .claude/docs/lean4/
  [3] .claude/lean4-memories/

Remove .claude/tools/lean4/? [y/n/a/q] y
  ✓ Removed

Remove .claude/docs/lean4/? [y/n/a/q] n
  → Skipped

Remove .claude/lean4-memories/? [y/n/a/q] q
  → Quit (1 removed, 1 skipped, 1 remaining)
```
Keys: y=remove this, n=keep this, a=remove all remaining, q=quit now

## Output

**Full diagnostic:**
```markdown
## Lean4 Doctor Report

### Environment
✓ lean 4.x.x
✓ lake 4.x.x
...

### MCP Tools
✓ Lean LSP MCP tools available in this session (lean_goal)

### Plugin
✓ LEAN4_PLUGIN_ROOT set
✓ Scripts executable
...

### Project
✓ Build passes
→ N sorries in M files

### Status: Ready
```

**Migration report:**
```markdown
## Migration Check

### Legacy Plugins
⚠ Found: ~/.claude/plugins/lean4-theorem-proving/
  → Uninstall or remove this directory

### Stale Environment
✓ LEAN4_PLUGIN_ROOT points to current plugin

### Summary
Found 1 stale item. Run `/lean4:doctor cleanup` to see removal commands.
```

**Cleanup report:**
```markdown
## Cleanup Report

### Stale Files Found
.claude/tools/lean4/
.claude/docs/lean4/

### Removal Commands
rm -rf .claude/tools/lean4/
rm -rf .claude/docs/lean4/

No changes made. Run `/lean4:doctor cleanup --apply` to remove.
```

## Troubleshooting

| Issue | Fix |
|-------|-----|
| LEAN4_SCRIPTS not set | Restart session, check hooks.json |
| lake not found | Install via elan |
| Scripts not executable | `chmod +x $LEAN4_SCRIPTS/*.sh` |
| Build fails | `lake update && lake clean && lake build` |
| Fresh worktree rebuild is slow / LSP times out on first use | Prime cache (`lake cache get` or `lake exe cache get`), then `lake build`; do not symlink `.lake/build` from another worktree |
| Stale build after `lake clean` | Hydrate cache (`lake cache get` or `lake exe cache get`), then `lake build` |
| Legacy plugin detected | Uninstall old plugin, remove directory |
| Stale env vars | Restart session after removing old plugin |
| Commands not found after migration | Check `/lean4:*` not `/lean4-theorem-proving:*` |
| `rg` not found | Install via package manager — see [ripgrep](../../../INSTALLATION.md#optional-ripgrep) |
| Lean LSP MCP tools unavailable | Check `claude mcp list` (Claude Code); if missing, `claude mcp add --transport stdio --scope user lean-lsp -- uvx lean-lsp-mcp` or see [INSTALLATION.md](../../../INSTALLATION.md#lean-lsp-mcp-server-all-hosts) |

## Safety

- All modes are read-only by default
- `migrate` never makes changes (detection only)
- `cleanup` shows commands but does not execute without `--apply`
- `cleanup --apply` prompts per-item (y/n/a/q) - users can keep specific items
- `--global` only scans `~/` when explicitly requested
- Does not modify Lean source files

## See Also

- `/lean4:prove` - Guided cycle-by-cycle proving
- `/lean4:checkpoint` - Save progress
- [Examples](../skills/lean4/references/command-examples.md#doctor)
