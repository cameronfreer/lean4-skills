---
name: doctor
description: Diagnostics, cleanup, and migration help
user_invocable: true
---

# Lean4 Doctor

Diagnostics, troubleshooting, and migration assistance for the Lean4 plugin.

## Usage

```
/lean4:doctor              # Full diagnostic
/lean4:doctor env          # Environment only
/lean4:doctor migrate      # Migration assistance
/lean4:doctor cleanup      # Remove obsolete files
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| mode | No | `env`, `migrate`, `cleanup`, or full (default) |

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

### 2. Plugin Check

Verify structure and permissions:
```
plugins/lean4/
├── .claude-plugin/plugin.json
├── commands/     (5 files)
├── hooks/        (executable .sh)
├── skills/lean4/ (SKILL.md + references/)
├── agents/       (5 files)
└── lib/scripts/  (12 files, executable)
```

### 3. Project Check

- `lakefile.lean` and `lean-toolchain` present
- `lake build` passes
- Sorry count reported

### 4. Migration (v3 → v4)

| V3 | V4 |
|----|-----|
| `lean4-theorem-proving` | `lean4` |
| `lean4-memories` | Removed |
| `lean4-subagents` | Integrated |
| `/lean4-theorem-proving:*` | `/lean4:*` |

### 5. Cleanup

Remove obsolete v3 artifacts: `.claude/tools/lean4/`, `.claude/docs/lean4/`

## Output

```markdown
## Lean4 Doctor Report

### Environment
✓ lean 4.x.x
✓ lake 4.x.x
...

### Plugin
✓ LEAN4_PLUGIN_ROOT set
✓ Scripts executable
...

### Project
✓ Build passes
→ N sorries in M files

### Status: Ready
```

## Troubleshooting

| Issue | Fix |
|-------|-----|
| LEAN4_SCRIPTS not set | Restart session, check hooks.json |
| lake not found | Install via elan |
| Scripts not executable | `chmod +x $LEAN4_SCRIPTS/*.sh` |
| Build fails | `lake update && lake clean && lake build` |

## Safety

- Read-only diagnostics
- Cleanup requires confirmation
- Does not modify Lean files

## See Also

- `/lean4:autoprover` - Main workflow
- `/lean4:checkpoint` - Save progress
- [Examples](../skills/lean4/references/command-examples.md#doctor)
