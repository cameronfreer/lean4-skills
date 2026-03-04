# Lean 4 Skills

[![Run in Smithery](https://smithery.ai/badge/skills/cameronfreer)](https://smithery.ai/skills?ns=cameronfreer&utm_source=github&utm_medium=badge)

Lean 4 workflow pack for AI coding agents. Claude Code has a native plugin adapter; Codex, Gemini CLI, OpenCode, Cursor, and other hosts use the same workflows via markdown + scripts, optionally MCP.

## Compatibility

| Host | Status | Workflow |
|---|---|---|
| Claude Code | Full native | `/lean4:*` slash commands, hooks, guardrails |
| OpenAI Codex | Documented, not CI-verified | SKILL.md + scripts + MCP |
| Gemini CLI | Documented, not CI-verified | GEMINI.md context + scripts + MCP |
| Cursor | Documented, not CI-verified | Project rules + scripts |
| Windsurf | Documented, not CI-verified | Project rules + scripts |
| OpenCode | Documented, not CI-verified | SKILL.md + scripts + MCP |
| Other agents | Best-effort | Markdown + shell scripts + MCP if available |

## Lean LSP MCP Server (Highly Recommended — All Hosts)

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

## Commands (Claude Code Adapter)

> `/lean4:*` commands are Claude Code adapter syntax. Other hosts invoke the same
> workflows by referencing the skill content directly or running the underlying scripts.

| Command | Description |
|---------|-------------|
| `/lean4:prove` | Guided cycle-by-cycle theorem proving |
| `/lean4:autoprove` | Autonomous multi-cycle proving with stop rules |
| `/lean4:checkpoint` | Verified save point (build + axiom check + commit) |
| `/lean4:review` | Read-only quality review with optional external hooks |
| `/lean4:golf` | Optimize proofs for brevity |
| `/lean4:learn` | Interactive teaching, mathlib exploration, and autoformalization |
| `/lean4:doctor` | Diagnostics and migration help |

## Quick Start

> Quick Start shows Claude Code adapter commands. For other hosts, see
> [Installation](#installation) and use the workflows described in
> [SKILL.md](plugins/lean4/skills/lean4/SKILL.md) directly.

```
/lean4:prove               # Guided sorry filling (interactive)
/lean4:autoprove           # Or autonomous (unattended)
/lean4:review              # Check quality (read-only)
/lean4:golf                # Optimize proofs
/lean4:learn               # Interactive teaching, mathlib, formalization
/lean4:checkpoint          # Verified commit
git push                   # Manual, after review
```

## How It Works (Claude Code Adapter)

> These workflows are invoked via `/lean4:*` slash commands in Claude Code.
> Other hosts can follow the same workflow definitions in SKILL.md.

**`/lean4:prove`** — Guided, interactive. Asks preferences at startup, prompts before each commit, pauses between cycles. Start here.

**`/lean4:autoprove`** — Autonomous, unattended. No questionnaire, auto-commits, loops until done or a stop condition fires (max cycles/time/stuck).

Both run the same cycle engine: **Plan → Work → Checkpoint → Review → Replan → Continue/Stop**. Each sorry gets a mathlib search, tactic attempts, and validation. By default, each successful fill is committed individually (`--commit` controls this). When stuck, both force a review + replan.

**Without a command:** Editing `.lean` files activates the skill for one bounded pass — fix the immediate issue, then suggest `/lean4:prove` or `/lean4:autoprove` for more.

The other commands: **`/lean4:review`** (read-only quality check), **`/lean4:checkpoint`** (build + axiom check + commit), **`/lean4:golf`** (proof optimization), **`/lean4:learn`** (interactive teaching, mathlib exploration, autoformalization), **`/lean4:doctor`** (diagnostics).

See [plugin README](plugins/lean4/README.md) for the full command guide.

## Migrating from V3 (Claude Code)

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
- [Advanced References](plugins/lean4/skills/lean4/references/) - grind, simprocs, metaprogramming, linters, FFI, verso-docs, profiling

## Changelog

**v4.1.0** (February 2026)
- New [`/lean4:learn`](plugins/lean4/commands/learn.md) command: interactive teaching, mathlib exploration, autoformalization
- Two-layer architecture: Lean-backed verification (always runs) + presentation layer (informal/supporting/formal)
- Intent classification (`--intent`), game-style tracks (`--style=game`), source handling (`--source`)
- Verification status model with `--verify=best-effort|strict`

**v4.0.9** (February 2026)
- Integrated advanced references from PR #10 (Alok Singh): grind tactic, simprocs, metaprogramming, linters, FFI, verso-docs, profiling
- All new content is reference-only, outside default prove/autoprove loop
- Lint guards for scope guards, SKILL.md cross-references, stale plugin paths, and command frontmatter

**v4.0.8** (February 2026)
- Three-tier build verification policy (diagnostics → `lake env lean` → `lake build`)
- Fixed incorrect `lake build FILE.lean` patterns across references
- Lint check prevents `lake build` with file arguments from regressing

**v4.0.7** (February 2026)
- Custom syntax reference: notations, macros, elaborators, DSLs (from PR #5, Alok Singh)
- DSL scaffold template with precedence-correct examples
- Version-compat note for MetaM/TacticM API drift across toolchains

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
