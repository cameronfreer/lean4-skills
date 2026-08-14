---
name: diagnose
description: Diagnostics, cleanup, and migration help
user_invocable: true
---

# Lean4 Diagnostics

Diagnostics, troubleshooting, and migration assistance for the Lean4 plugin.

## Usage

```
/lean4:diagnose                    # Full diagnostic (plugin + workspace)
/lean4:diagnose env                # Environment only
/lean4:diagnose migrate            # Detect legacy installs (read-only)
/lean4:diagnose migrate --global   # Include user-level ~/.claude scan
/lean4:diagnose cleanup            # Show stale files + removal commands
/lean4:diagnose cleanup --apply    # Actually remove stale files
/lean4:diagnose <pasted error>     # Error triage: match against known patterns
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| mode | No | `env`, `migrate`, `cleanup`, or full (default) |
| --global | No | Include user-level paths (~/); migrate only |
| --apply | No | Execute removals; cleanup only |
| error text | No | Positional text whose first token is not a recognized mode is treated as pasted diagnostic text for error triage |

**Dispatch** is decided by the **first positional token** only:
- a recognized mode (`env`, `migrate`, `cleanup`) or no positional token → existing mode behavior (default full diagnostic when absent);
- otherwise → treat the positional text as pasted diagnostic input for error triage.

Mode-specific flags (`--global`, `--apply`) remain flags in every case — they are never treated as error text.

**Error triage precedence:** pasted text is matched against the specific patterns in [compilation-errors.md](../skills/lean4/references/compilation-errors.md) (Quick Reference Table first), including the module-system patterns below, **before** falling back to the generic `Build fails → lake update && lake clean && lake build` row. A specific match wins over the generic remediation.

## Actions

### 1. Environment Check

| Tool | Check | Required |
|------|-------|----------|
| `lean` | `lean --version` | Yes |
| `lake` | `lake --version` | Yes |
| `python3` | `python3 --version` | For scripts |
| `git` | `git --version` | For commits |
| `rg` | `rg --version` | Optional (faster search) |

Persistent-environment hosts use `LEAN4_PLUGIN_ROOT`, `LEAN4_SCRIPTS`,
`LEAN4_REFS`, and `LEAN4_PYTHON_BIN`. Trusted native Codex installs instead
receive absolute SessionStart paths; those values are not shell exports.

Run the shared preflight **without depending on PATH**, which may be absent.

**Native Codex plugin:** use the literal absolute SessionStart `preflight` value:

```bash
/absolute/plugin/root/bin/lean4-skills-preflight --codex
```

If trusted context is missing, report this canonical recovery block:

```text
1. Review and trust the lean4 plugin hooks in /hooks.
2. Start a new Codex task (re-runs the SessionStart hook).
3. Run the absolute <plugin-root>/bin/lean4-skills-preflight --codex command; if it is missing, reinstall the plugin.
```

**Persistent environment (including Claude Code):**

```bash
if command -v lean4-skills-preflight >/dev/null 2>&1; then
    lean4-skills-preflight
elif [[ -n "${LEAN4_PLUGIN_ROOT:-}" && -x "$LEAN4_PLUGIN_ROOT/bin/lean4-skills-preflight" ]]; then
    "$LEAN4_PLUGIN_ROOT/bin/lean4-skills-preflight"
else
    echo "Lean4 bootstrap environment is not fully set up in this Claude Code session." >&2
    echo "  Recovery:" >&2
    echo "    1. Run /lean4:diagnose env for a full diagnosis." >&2
    echo "    2. Restart the Claude Code session (re-runs the SessionStart bootstrap hook)." >&2
    echo "    3. If it persists, check the plugin hook/bootstrap state (hooks.json, bootstrap.sh)." >&2
fi
```

The persistent preflight checks `LEAN4_*`, PATH, and wrappers. Codex checks the
installed tree and absolute wrappers. Each has a canonical recovery block.

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
├── .codex-plugin/plugin.json
├── commands/     (*.md command files)
├── hooks/        (Claude + Codex hook configs; executable hooks)
├── skills/lean4/ (SKILL.md + references/)
├── agents/       (4 files)
├── bin/          (lean4-skills-* wrappers; absolute under Codex, on PATH under Claude)
└── lib/scripts/  (executable .py / .sh internals)
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
## Lean4 Diagnostics Report

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
Found 1 stale item. Run `/lean4:diagnose cleanup` to see removal commands.
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

No changes made. Run `/lean4:diagnose cleanup --apply` to remove.
```

## Troubleshooting

| Issue | Fix |
|-------|-----|
| Native Codex bare wrapper not found on PATH | Expected: invoke the literal absolute `bin_dir/lean4-skills-*` path supplied by trusted SessionStart. Codex does not document persistent plugin PATH mutation. |
| LEAN4_SCRIPTS not set | 1. Run `/lean4:diagnose env` for a full diagnosis. 2. Restart the Claude Code session (re-runs the SessionStart bootstrap hook). 3. If it persists, check the plugin hook/bootstrap state (hooks.json, bootstrap.sh). |
| `lean4-skills-*` wrapper not found on PATH | 1. Run `/lean4:diagnose env` for a full diagnosis. 2. Restart the Claude Code session (re-runs the SessionStart bootstrap hook). 3. If it persists, check the plugin hook/bootstrap state (hooks.json, bootstrap.sh). |
| lake not found | Install via elan |
| Scripts not executable | Wrappers should be shipped executable — check `command -v lean4-skills-sorry-analyzer`. For unwrapped internals: `chmod +x $LEAN4_SCRIPTS/*.sh $LEAN4_SCRIPTS/*.py` |
| Build fails | `lake update && lake clean && lake build` |
| Fresh worktree rebuild is slow / LSP times out on first use | Prime cache (`lake cache get` or `lake exe cache get`), then `lake build`; do not symlink `.lake/build` from another worktree |
| Stale build after `lake clean` | Hydrate cache (`lake cache get` or `lake exe cache get`), then `lake build` |
| Legacy plugin detected | Uninstall old plugin, remove directory |
| Stale env vars | Restart session after removing old plugin |
| Commands not found after migration | Check `/lean4:*` not `/lean4-theorem-proving:*` |
| `rg` not found | Install via package manager — see [ripgrep](../../../INSTALLATION.md#optional-ripgrep) |
| Lean LSP MCP tools unavailable | Check `claude mcp list` (Claude Code); if missing, `claude mcp add --transport stdio --scope user lean-lsp -- uvx lean-lsp-mcp` or see [INSTALLATION.md](../../../INSTALLATION.md#lean-lsp-mcp-server-all-hosts) |

Under Codex, PreToolUse is advisory and is not a security boundary.

### Module-System Troubleshooting

Error-triggered guidance for the Lean module system (post-2025-11-19 mathlib). These patterns take precedence over the generic `Build fails` row above; each links to a worked entry in [compilation-errors.md](../skills/lean4/references/compilation-errors.md).

| Error pattern | Fix |
|---------------|-----|
| ``cannot import non-`module` X from `module` `` | `X` lacks a `module` header, or an aggregator is plain-style. Plain `lake exe mk_all` preserves the existing style; use `lake exe mk_all --module` to create **or convert** a module-style aggregator. Import-list staleness is a separate companion problem — [§ 16](../skills/lean4/references/compilation-errors.md#16-cannot-import-non-module-from-module) |
| `Unknown identifier` for a name that exists upstream; `Expected a definition with an exposed body`; `backward.privateInPublic` warning | Module visibility: private-by-default declarations / non-exposed bodies. Use the public API, `import all` (same library only), or upstream `public`/`@[expose]` — [§ 17](../skills/lean4/references/compilation-errors.md#17-module-visibility-name-exists-upstream-but-is-not-exported) |
| ``Invalid `meta` definition ..., not marked `meta` `` vs ``may not access declaration ... marked as `meta` `` | Two *opposite* meta-phase failures: the first may need `meta import`; for the second, `meta import` is not the fix — the consumer becomes `meta` or uses a non-meta implementation — [§ 18](../skills/lean4/references/compilation-errors.md#18-meta-phase-errors-meta-import-public-meta-import) |
| Old-style plain `import` header in a module-system repo | Rewrite to the [mathlib-style.md](../skills/lean4/references/mathlib-style.md#1-file-header-copyright-module-imports-critical) header (`module`, grouped `public import`/`import`, `public section`), then `lake exe mk_all` — [§ 19](../skills/lean4/references/compilation-errors.md#19-old-style-header-in-a-module-system-repo) |

The `lake exe mk_all` remediation string here is the same one `/lean4:checkpoint`'s mk_all gate (#111) will surface at checkpoint time — users hitting it mid-build and at checkpoint get one consistent instruction.

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
- [Examples](../skills/lean4/references/command-examples.md#diagnose)
