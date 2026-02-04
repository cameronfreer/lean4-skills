# Lean 4 Skills for Claude

Claude Code plugin for automated Lean 4 theorem proving with planning-first workflow.

## Installation

```bash
# Add marketplace
/plugin marketplace add cameronfreer/lean4-skills

# Install plugin
/plugin install lean4
```

## Commands

| Command | Description |
|---------|-------------|
| `/lean4:autoprover` | Main entry - planning-first sorry filling and repair |
| `/lean4:checkpoint` | Verified save point (build + axiom check + commit) |
| `/lean4:review` | Read-only quality review with optional external hooks |
| `/lean4:golf` | Optimize proofs for brevity |
| `/lean4:doctor` | Diagnostics and migration help |

## Quick Start

```
/lean4:autoprover          # Start filling sorries
/lean4:review              # Check quality (read-only)
/lean4:golf                # Optimize proofs
/lean4:checkpoint          # Verified commit
git push                   # Manual, after review
```

## Features

- **Planning-first workflow** - Establishes scope before any changes
- **LSP-first approach** - Sub-second feedback via Lean LSP MCP
- **Search before prove** - 90% of sorries exist in mathlib
- **Safety guardrails** - Blocks push/amend/pr during sessions
- **Atomic commits** - One sorry = one commit for easy rollback

## Recommended: Lean LSP MCP Server

The [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) server provides sub-second feedback:

```
lean_goal(file, line)                    # See exact goal
lean_leansearch("natural language")       # Search mathlib
lean_loogle("type pattern")               # Type-based search
lean_multi_attempt(file, line, ["simp", "ring"])  # Test tactics
```

**Setup:** See [INSTALLATION.md](INSTALLATION.md#lean-lsp-server)

## Migrating from V3

If upgrading from the 3-plugin system:

```bash
# Uninstall old plugins
/plugin uninstall lean4-theorem-proving
/plugin uninstall lean4-memories
/plugin uninstall lean4-subagents

# Install unified plugin
/plugin install lean4

# Verify
/lean4:doctor
```

**Legacy access:** Pin to `@v3.4.2-legacy` or use `#legacy-marketplace` branch.

See `/lean4:doctor migrate` for detailed migration help.

## Documentation

- [SKILL.md](plugins/lean4/skills/lean4/SKILL.md) - Core skill reference
- [INSTALLATION.md](INSTALLATION.md) - Setup guide
- [Commands](plugins/lean4/commands/) - Command documentation

## Changelog

**v4.0.0** (February 2026)
- Unified into single `lean4` plugin
- New `/lean4:autoprover` - planning-first workflow
- New `/lean4:golf` - standalone proof optimization
- LSP-first approach throughout
- Safety guardrails (blocks push/amend/pr)
- Removed memory integration (didn't work reliably)

**v3.4.2** (January 2026) - [Legacy branch](../../tree/legacy-marketplace)
- Last version of 3-plugin system
- Available via `@v3.4.2-legacy` tag

## Contributing

Issues and PRs welcome at https://github.com/cameronfreer/lean4-skills

## License

MIT License - see [LICENSE](LICENSE)
