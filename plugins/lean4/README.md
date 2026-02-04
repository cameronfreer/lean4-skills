# Lean 4 Plugin

Unified Lean 4 theorem proving with planning-first autoprover.

## Commands

| Command | Description |
|---------|-------------|
| `/lean4:autoprover` | Main entry - planning-first sorry filling and repair |
| `/lean4:checkpoint` | Verified save point (build + axiom check + commit) |
| `/lean4:review` | Read-only quality review with optional external hooks |
| `/lean4:golf` | Optimize proofs for brevity |
| `/lean4:doctor` | Diagnostics and migration help |

## Quick Start

```bash
/lean4:autoprover          # Start filling sorries
/lean4:review              # Check quality (read-only)
/lean4:golf                # Optimize proofs
/lean4:checkpoint          # Verified commit
git push                   # Manual, after review
```

## Key Features

### Planning-First Workflow

Before any changes, autoprover asks:
- **Scope:** All sorries / specific files / specific theorems
- **Approach:** Conservative / Balanced / Aggressive
- **Review cadence:** Every change / every 5 / manual

### Safety Guardrails

Blocked during sessions:
- `git push` → Use `/lean4:checkpoint`, then push manually
- `git commit --amend` → Each change is a new commit
- `gh pr create` → Review first with `/lean4:review`

### LSP-First Approach

The plugin prefers Lean LSP MCP tools for sub-second feedback:
```
lean_goal(file, line)                    # See exact goal
lean_leansearch("natural language")       # Search mathlib
lean_loogle("type pattern")               # Type-based search
lean_multi_attempt(file, line, tactics)   # Test multiple tactics
```

Scripts serve as fallback when LSP is unavailable.

## Environment Variables

Set by `bootstrap.sh` at session start:

| Variable | Purpose |
|----------|---------|
| `LEAN4_PLUGIN_ROOT` | Plugin installation path |
| `LEAN4_SCRIPTS` | Scripts directory |
| `LEAN4_REFS` | References directory |
| `LEAN4_PYTHON_BIN` | Python interpreter |

## File Structure

```
plugins/lean4/
├── .claude-plugin/plugin.json
├── commands/           # User-invocable commands
├── skills/lean4/
│   ├── SKILL.md        # Core skill reference
│   └── references/     # 23 reference docs
├── agents/             # 5 specialized agents
├── hooks/              # Bootstrap and guardrails
└── lib/scripts/        # 12 hard-primitive scripts
```

## Upgrading from V3

See [MIGRATION.md](MIGRATION.md) for upgrade guide.

## See Also

- [SKILL.md](skills/lean4/SKILL.md) - Core skill reference
- [Commands](commands/) - Command documentation
- [Scripts](lib/scripts/README.md) - Script reference
