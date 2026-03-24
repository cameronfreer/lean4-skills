# Lean 4 Skills

Lean 4 workflow pack for AI coding agents. Gives your agent a structured
prove/review/golf loop, mathlib search, axiom checking, and safety guardrails.
The workflows are host-agnostic — Claude Code, Codex, Gemini CLI, Cursor, and
others all use the same core skill; only the invocation surface differs.

## Workflows

| Workflow | Description |
|---|---|
| draft | Draft Lean declaration skeletons from informal claims |
| formalize | Interactive formalization — drafting plus guided proving |
| autoformalize | Autonomous end-to-end formalization from informal sources |
| prove | Guided cycle-by-cycle theorem proving |
| autoprove | Autonomous multi-cycle proving with stop rules |
| checkpoint | Verified save point (build + axiom check + commit) |
| review | Read-only quality review |
| refactor | Leverage mathlib, extract helpers, simplify proof strategies |
| golf | Improve proofs for directness, clarity, performance, and brevity |
| learn | Interactive teaching and mathlib exploration |
| doctor | Diagnostics and migration help |

**Claude Code:** invoke as `/lean4:<name>`. **Other hosts:** follow the corresponding workflow in [SKILL.md](plugins/lean4/skills/lean4/SKILL.md).

Typical session: `draft` (or `formalize` / `autoformalize`) → `prove` (or `autoprove`) → `review` → `refactor` → `golf` → `checkpoint` → `git push`.

## How It Works

- **`draft`** — Skeleton-only drafting from informal claims. Use when you want Lean declarations without a full prove run.
- **`formalize`** — Interactive synthesis. Drafts a skeleton, then runs guided prove cycles with user interaction.
- **`autoformalize`** — Autonomous synthesis. Extracts claims from a source, drafts skeletons, and proves them unattended.
- **`prove`** — Guided proof engine for existing declarations. Asks preferences at startup, prompts before each commit, pauses between cycles.
- **`autoprove`** — Autonomous proof engine for existing declarations. Auto-commits, loops until a stop condition fires (max cycles, max time, or stuck).
- The proof engines share one cycle engine: **Plan → Work → Checkpoint → Review → Replan → Continue/Stop**. Each sorry gets a mathlib search, tactic attempts, and validation. `--commit` controls per-fill commit behavior. When stuck, both force a review + replan.
- `formalize` and `autoformalize` wrap drafting around that same engine. Statement and header changes belong there — `prove` and `autoprove` keep declaration headers immutable.
- Editing `.lean` files without a command activates the skill for one bounded pass — fix the immediate issue, then suggest the right next command: `draft` / `formalize` for statement work, `prove` / `autoprove` for proof work.

See [plugin README](plugins/lean4/README.md) for the full command guide.

## Installation

### Claude Code (native plugin)

```bash
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4
```

Optionally, install the contribution helper to draft bug reports, feature requests, or shareable insights from your editor:

```bash
/plugin install lean4-contribute
```

### Other Hosts

Clone (shallow) and follow the setup for your host:

```bash
git clone --depth 1 https://github.com/cameronfreer/lean4-skills.git
```

- **Codex CLI** — add to `AGENTS.md` + env vars. See [INSTALLATION.md → Codex](INSTALLATION.md#openai-codex-cli)
- **Gemini CLI** — add to `GEMINI.md` + env vars. See [INSTALLATION.md → Gemini](INSTALLATION.md#gemini-cli)
- **Cursor** — project rules → SKILL.md + env vars. See [INSTALLATION.md → Cursor](INSTALLATION.md#cursor)
- **Windsurf** — project rules → SKILL.md + env vars. See [INSTALLATION.md → Windsurf](INSTALLATION.md#windsurf)
- **OpenCode** — copy to `.opencode/skills/` + env vars. See [INSTALLATION.md → OpenCode](INSTALLATION.md#opencode)
- **Other agents** — point agent at SKILL.md + env vars. See [INSTALLATION.md → Generic](INSTALLATION.md#any-agent-generic)

## Lean LSP MCP Server (Optional, Highly Recommended)

The skill works standalone, but plays especially well with [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) — faster mathlib search and **sub-second feedback** instead of 30+ second `lake build` cycles. Works with any MCP-capable host.

**What you get:**
- `lean_goal` — exact goal state at any line
- `lean_local_search` / `lean_leanfinder` / `lean_leansearch` / `lean_loogle` — mathlib search
- `lean_multi_attempt` — test multiple tactics in parallel
- `lean_hammer_premise` — premise suggestions for simp/aesop/grind
- `lean_diagnostic_messages` — per-file error/warning check without a full `lake build`
- …and more (hover info, goal-conditioned search, state inspection, etc.)

**Claude Code** (run from your Lean project root):
```bash
# User-scoped — available in all your projects
claude mcp add --transport stdio --scope user lean-lsp -- uvx lean-lsp-mcp

# Or project-scoped — shared via .mcp.json
claude mcp add --transport stdio --scope project lean-lsp -- uvx lean-lsp-mcp
```

> **Tip:** User-scoped (`--scope user`) is recommended — it has been more reliable
> for keeping MCP tools visible inside proof-editing subagents. Project-scoped
> servers may not propagate to plugin subagents in some Claude Code versions.

**Other hosts:** See [INSTALLATION.md → MCP Server](INSTALLATION.md#lean-lsp-mcp-server-all-hosts)

## Compatibility

| Host | Status | Workflow |
|---|---|---|
| Claude Code | Full native | SKILL.md + scripts + `/lean4:*` commands, hooks, guardrails, subagents |
| Codex / Gemini / OpenCode | Documented\* | SKILL.md + scripts |
| Cursor / Windsurf | Documented\* | Project rules → SKILL.md + scripts |

\*Documented setup patterns, not CI-verified.

## Documentation

- [INSTALLATION.md](INSTALLATION.md) - Setup guide

**lean4 plugin**
- [SKILL.md](plugins/lean4/skills/lean4/SKILL.md) - Core skill reference
- [Commands](plugins/lean4/commands/) - Command documentation
- [References](plugins/lean4/skills/lean4/references/) - cycle engine, mathlib style, proof golfing, tactic patterns, grind, metaprogramming, and more

**lean4-contribute plugin** — opt-in helper for filing issues on this repo from your editor
- [README](plugins/lean4-contribute/README.md) - Full command guide and privacy details
- `/lean4-contribute:bug-report` — draft a bug report (plugin bugs, not Lean/mathlib issues)
- `/lean4-contribute:feature-request` — request a workflow the plugin doesn't support yet
- `/lean4-contribute:share-insight` — share a reusable pattern or antipattern from your session

---

- [CHANGELOG.md](CHANGELOG.md) - Version history
- Migrating from v3 (Claude Code): see [MIGRATION.md](plugins/lean4/MIGRATION.md)

## Changelog

See [CHANGELOG.md](CHANGELOG.md) for version history.

## Contributing

Issues and PRs welcome at https://github.com/cameronfreer/lean4-skills.

If you have the `lean4-contribute` plugin installed, your coding agent may
suggest filing bug reports, feature requests, or sharing insights at natural
stopping points. Drafting starts only after you opt in; submission has its own
separate confirmation. Each draft is shown in full before anything is sent.

## License & Citation

MIT licensed. See [LICENSE](LICENSE) for more information.

Citing this repository is highly appreciated but not required by the license. See also [CITATION.cff](CITATION.cff).

```bibtex
@software{lean4-skills,
  author = {Cameron Freer},
  title = {Lean 4 {Skills}: Theorem proving skill and workflow pack for {AI} coding agents},
  url = {https://github.com/cameronfreer/lean4-skills},
  month = oct,
  year = {2025}
}
```
