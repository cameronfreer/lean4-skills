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
| autoprove | Autonomous multi-cycle proving with explicit stop budgets |
| disprove | Guided counterexample search with certified refutation |
| checkpoint | Save point (per-file + project build, axiom check, commit) |
| review | Read-only quality review |
| refactor | Leverage mathlib, extract helpers, simplify proof strategies |
| golf | Improve proofs for directness, clarity, performance, and brevity |
| learn | Interactive teaching and mathlib exploration |
| doctor | Diagnostics and migration help |

**Claude Code:** invoke as `/lean4:<name>`. **Other hosts:** follow the corresponding workflow in [SKILL.md](plugins/lean4/skills/lean4/SKILL.md).

Typical session: `draft` (or `formalize` / `autoformalize`) → `prove` (or `autoprove`) → `review` → `refactor` → `golf` → `checkpoint` → `git push`. Use `disprove` instead of `prove` when you want to refute a statement rather than prove it.

CLI-like inputs are validated by a host-agnostic parser
(`plugins/lean4/lib/command_args/`) for the seven parameter-heavy commands
(`draft`, `learn`, `formalize`, `autoformalize`, `prove`, `autoprove`,
`disprove`). The
Claude Code adapter pre-validates `/lean4:*` prompts via a `UserPromptSubmit`
hook; other hosts fall back to model-parsed startup. Commands must announce
resolved inputs, reject invalid startup configs, and treat wall-clock budgets
as best-effort rather than host-enforced timeouts. See the
[Command Invocation Contract](plugins/lean4/skills/lean4/references/command-invocation.md).

## How It Works

- **`draft`** — Skeleton-only drafting from informal claims. Use when you want Lean declarations without a full prove run.
- **`formalize`** — Interactive synthesis. Drafts a skeleton, then runs guided prove cycles with user interaction.
- **`autoformalize`** — Autonomous synthesis. Extracts claims from a source, drafts skeletons, and proves them unattended.
- **`prove`** — Guided proof engine for existing declarations. Asks preferences at startup, prompts before each commit, pauses between cycles.
- **`autoprove`** — Autonomous proof engine for existing declarations. Auto-commits, loops until a stop budget fires (max cycles, wall-clock budget, or stuck). The wall-clock budget is checked between cycles; it is not a host timeout.
- **`disprove`** — Guided counterexample-search engine for existing declarations. Each cycle's Plan phase generates dynamic Step 0 (knowledge search) / Step 1 (method) / Step 2 (config) menus seeded by accumulated evidence. Reports `REFUTED` **only** when Lean typechecks a proof of the negation; otherwise `WITNESS_UNCERTIFIED` (candidate but uncertified) or `INCONCLUSIVE` (no candidate within budgets). Append-only: never rewrites an existing `theorem T : P := by sorry`.
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

### Codex

Quick install — run this in Codex chat, not in your shell:

```text
$skill-installer Install the `lean4` skill from
https://github.com/cameronfreer/lean4-skills/tree/main/plugins/lean4/skills/lean4
```

Then invoke it with `$lean4`, or let Codex activate it automatically
for Lean 4 tasks (if it does not appear, restart Codex). This installs the core skill only (instructions +
references, no helper scripts) — see
[INSTALLATION.md → Codex](INSTALLATION.md#openai-codex-cli) for the full setup.

### Other Hosts

Every major host now discovers Agent Skills natively. The recommended
full setup is one checkout + one symlink + one env block
([details](INSTALLATION.md#portable-checkout--helper-runtime-all-hosts)):

```bash
git clone https://github.com/cameronfreer/lean4-skills.git "$HOME/.local/share/lean4-skills"
mkdir -p "$HOME/.agents/skills"
src="$HOME/.local/share/lean4-skills/plugins/lean4/skills/lean4"
dest="$HOME/.agents/skills/lean4"
if [ -e "$dest" ] && [ ! -L "$dest" ]; then   # back up a prior copy — ln can't replace a real directory
  if mv "$dest" "$dest.bak-$(date +%Y%m%d%H%M%S)-$$"; then
    ln -sfn "$src" "$dest"
  else
    printf 'Could not back up %s; leaving it unchanged.\n' "$dest" >&2
  fi
else
  ln -sfn "$src" "$dest"
fi
```

(Antigravity CLI's global skills live outside `~/.agents/skills` — see
[INSTALLATION.md → Antigravity](INSTALLATION.md#antigravity-cli) for its separate link.)

Skill-only quick installs and host specifics ([what "skill-only" excludes](INSTALLATION.md#installation-tiers)):

- **Gemini CLI** (Enterprise/API-key; consumer access moved to Antigravity, June 2026) — `gemini skills install https://github.com/cameronfreer/lean4-skills.git --path plugins/lean4/skills/lean4 --scope user`. See [INSTALLATION.md → Gemini](INSTALLATION.md#gemini-cli)
- **Antigravity CLI** — `gh skill install cameronfreer/lean4-skills lean4@main --agent antigravity-cli --scope user` (gh ≥ 2.96.0). See [INSTALLATION.md → Antigravity](INSTALLATION.md#antigravity-cli)
- **GitHub Copilot** — `gh skill install cameronfreer/lean4-skills lean4@main --agent github-copilot --scope user` (gh ≥ 2.92.0). See [INSTALLATION.md → Copilot](INSTALLATION.md#github-copilot)
- **Cursor** — native skills (`.agents/skills` / `.cursor/skills`); invoke with `/lean4`. See [INSTALLATION.md → Cursor](INSTALLATION.md#cursor)
- **Windsurf** — native skills; invoke with `@lean4`. See [INSTALLATION.md → Windsurf](INSTALLATION.md#windsurf)
- **OpenCode** — native `skill` tool; discovers `.agents/skills`. See [INSTALLATION.md → OpenCode](INSTALLATION.md#opencode)
- **Other agents** — point agent at SKILL.md + env block. See [INSTALLATION.md → Generic](INSTALLATION.md#any-agent-generic)

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
| Codex / Gemini / Antigravity / OpenCode / Copilot | Documented\* | Native Agent Skills discovery (+ scripts via portable checkout) |
| Cursor / Windsurf | Documented\* | Native Agent Skills discovery (+ scripts via portable checkout) |

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
