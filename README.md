# Lean 4 Skills for Claude

[![Run in Smithery](https://smithery.ai/badge/skills/cameronfreer)](https://smithery.ai/skills?ns=cameronfreer&utm_source=github&utm_medium=badge)

Claude Code plugin for automated Lean 4 theorem proving with guided and autonomous proving commands.

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
| `/lean4:prove` | Guided cycle-by-cycle theorem proving |
| `/lean4:autoprove` | Autonomous multi-cycle proving with stop rules |
| `/lean4:checkpoint` | Verified save point (build + axiom check + commit) |
| `/lean4:review` | Read-only quality review with optional external hooks |
| `/lean4:golf` | Optimize proofs for brevity |
| `/lean4:doctor` | Diagnostics and migration help |

## Quick Start

```
/lean4:prove               # Guided sorry filling (interactive)
/lean4:autoprove           # Or autonomous (unattended)
/lean4:review              # Check quality (read-only)
/lean4:golf                # Optimize proofs
/lean4:checkpoint          # Verified commit
git push                   # Manual, after review
```

## How It Works

**`/lean4:prove`** — Guided, interactive. Asks preferences at startup, prompts before each commit, pauses between cycles. Start here.

**`/lean4:autoprove`** — Autonomous, unattended. No questionnaire, auto-commits, loops until done or a stop condition fires (max cycles/time/stuck).

Both run the same cycle engine: **Plan → Work → Checkpoint → Review → Replan → Continue/Stop**. Each sorry gets a mathlib search, tactic attempts, and validation. By default, each successful fill is committed individually (`--commit` controls this). When stuck, both force a review + replan.

**Without a command:** Editing `.lean` files activates the skill for one bounded pass — fix the immediate issue, then suggest `/lean4:prove` or `/lean4:autoprove` for more.

The other commands: **`/lean4:review`** (read-only quality check), **`/lean4:checkpoint`** (build + axiom check + commit), **`/lean4:golf`** (proof optimization), **`/lean4:doctor`** (diagnostics).

See [plugin README](plugins/lean4/README.md) for the full command guide.

## Recommended: Lean LSP MCP Server

[lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) provides sub-second feedback and search (LeanSearch, Loogle, LeanFinder). **Setup:** See [INSTALLATION.md](INSTALLATION.md#lean-lsp-server)

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

**v4.0.5** (February 2026)
- Split `/lean4:autoprover` into `/lean4:prove` (guided) and `/lean4:autoprove` (autonomous)
- prove: asks before each cycle, startup questionnaire, interactive deep approval
- autoprove: autonomous loop with hard stop rules, structured summary on stop
- Shared cycle engine: plan → work → checkpoint → review → replan → continue/stop
- Stuck definition uses exact signature hashing for precision
- Checkpoint skips commit on empty diff

**v4.0.0** (February 2026)
- Unified into single `lean4` plugin
- New `/lean4:autoprover` - planning-first workflow
- New `/lean4:golf` - standalone proof optimization
- LSP-first approach throughout
- Safety guardrails in Lean projects (blocks push/amend/pr; one-shot bypass for collaboration ops). See [plugin README safety section](plugins/lean4/README.md#safety-guardrails).
- Removed memory integration (didn't work reliably)

**v3.4.2** (January 2026) - [Legacy branch](../../tree/legacy-marketplace)
- Last version of 3-plugin system
- Available via `@v3.4.2-legacy` tag

## Contributing

Issues and PRs welcome at https://github.com/cameronfreer/lean4-skills

## License

MIT License - see [LICENSE](LICENSE)
