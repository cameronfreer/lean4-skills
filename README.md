# Lean 4 Skills

[![Run in Smithery](https://smithery.ai/badge/skills/cameronfreer)](https://smithery.ai/skills?ns=cameronfreer&utm_source=github&utm_medium=badge)

Lean 4 workflow pack for AI coding agents. Gives your agent a structured
prove/review/golf loop, mathlib search, axiom checking, and safety guardrails.
The workflows are host-agnostic — Claude Code, Codex, Gemini CLI, Cursor, and
others all use the same core skill; only the invocation surface differs.

## Workflows

| Workflow | Description |
|---|---|
| prove | Guided cycle-by-cycle theorem proving |
| autoprove | Autonomous multi-cycle proving with stop rules |
| checkpoint | Verified save point (build + axiom check + commit) |
| review | Read-only quality review |
| golf | Optimize proofs for brevity |
| learn | Interactive teaching, mathlib exploration, and autoformalization |
| doctor | Diagnostics and migration help |

**Claude Code:** invoke as `/lean4:<name>`. **Other hosts:** follow the corresponding workflow in [SKILL.md](plugins/lean4/skills/lean4/SKILL.md).

## Quick Start

```
/lean4:prove               # Guided sorry filling (interactive)
/lean4:autoprove           # Or autonomous (unattended)
/lean4:review              # Check quality (read-only)
/lean4:golf                # Optimize proofs
/lean4:learn               # Interactive teaching, mathlib, formalization
/lean4:checkpoint          # Verified commit
git push                   # Manual, after review
```

Other hosts: point your agent at [SKILL.md](plugins/lean4/skills/lean4/SKILL.md).

## How It Works

**`/lean4:prove`** — Guided, interactive. Asks preferences at startup, prompts before each commit, pauses between cycles. Start here.

**`/lean4:autoprove`** — Autonomous, unattended. No questionnaire, auto-commits, loops until done or a stop condition fires (max cycles/time/stuck).

Both run the same cycle engine: **Plan → Work → Checkpoint → Review → Replan → Continue/Stop**. Each sorry gets a mathlib search, tactic attempts, and validation. By default, each successful fill is committed individually (`--commit` controls this). When stuck, both force a review + replan.

**Without a command:** Editing `.lean` files activates the skill for one bounded pass — fix the immediate issue, then suggest `/lean4:prove` or `/lean4:autoprove` for more.

The other commands: **`/lean4:review`** (read-only quality check), **`/lean4:checkpoint`** (build + axiom check + commit), **`/lean4:golf`** (proof optimization), **`/lean4:learn`** (interactive teaching, mathlib exploration, autoformalization), **`/lean4:doctor`** (diagnostics).

See [plugin README](plugins/lean4/README.md) for the full command guide.

## Lean LSP MCP Server (Highly Recommended)

[lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) provides **sub-second
feedback** instead of 30+ second `lake build` cycles. Works with any MCP-capable host.

**What you get:**
- `lean_goal` — exact goal state at any line
- `lean_local_search` / `lean_leanfinder` / `lean_leansearch` / `lean_loogle` — mathlib search
- `lean_multi_attempt` — test multiple tactics in parallel
- `lean_hammer_premise` — premise suggestions for simp/aesop/grind

**Setup:** a few minutes. See [INSTALLATION.md → MCP Server](INSTALLATION.md#lean-lsp-mcp-server-all-hosts)

## Installation

### Claude Code (native plugin)

```bash
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4
```

### OpenAI Codex CLI

```bash
git clone https://github.com/cameronfreer/lean4-skills.git
```

See [INSTALLATION.md → Codex](INSTALLATION.md#openai-codex-cli) for AGENTS.md setup and MCP config.

### Gemini CLI

```bash
git clone https://github.com/cameronfreer/lean4-skills.git
```

See [INSTALLATION.md → Gemini](INSTALLATION.md#gemini-cli) for GEMINI.md setup.

### OpenCode

```bash
git clone https://github.com/cameronfreer/lean4-skills.git
```

See [INSTALLATION.md → OpenCode](INSTALLATION.md#opencode) for skill setup.

### Cursor / Windsurf / Other Agents

```bash
git clone https://github.com/cameronfreer/lean4-skills.git
```

See [INSTALLATION.md → Generic](INSTALLATION.md#any-agent-generic) for setup.

## Compatibility

| Host | Status | Workflow |
|---|---|---|
| Claude Code | Full native | `/lean4:*` slash commands, hooks, guardrails |
| OpenAI Codex | Documented, not CI-verified | SKILL.md + scripts + optional MCP |
| Gemini CLI | Documented, not CI-verified | GEMINI.md context + scripts + optional MCP |
| Cursor | Documented, not CI-verified | Project rules + scripts |
| Windsurf | Documented, not CI-verified | Project rules + scripts |
| OpenCode | Documented, not CI-verified | SKILL.md + scripts + optional MCP |
| Other agents | Best-effort | Markdown + shell scripts + optional MCP |

## Documentation

- [SKILL.md](plugins/lean4/skills/lean4/SKILL.md) - Core skill reference
- [INSTALLATION.md](INSTALLATION.md) - Setup guide
- [Commands](plugins/lean4/commands/) - Command documentation
- [Advanced References](plugins/lean4/skills/lean4/references/) - grind, simprocs, metaprogramming, linters, FFI, verso-docs, profiling
- [CHANGELOG.md](CHANGELOG.md) - Version history
- Migrating from V3 (Claude Code): see [MIGRATION.md](plugins/lean4/MIGRATION.md)

## Changelog

See [CHANGELOG.md](CHANGELOG.md) for version history.

## Contributing

Issues and PRs welcome at https://github.com/cameronfreer/lean4-skills

## License

MIT License - see [LICENSE](LICENSE)
