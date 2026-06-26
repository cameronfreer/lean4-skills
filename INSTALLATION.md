# Installation Guide

## Environment Bootstrap (All Hosts)

All hosts need these variables. Claude Code sets them automatically via its
bootstrap hook and also adds `plugins/lean4/bin/` to the Bash tool's PATH so
model-facing `lean4-skills-*` wrappers resolve as bare commands. Other hosts
(Codex, Gemini, Cursor, OpenCode, generic) need to set everything manually,
including the PATH export — without it, the model may invoke
`lean4-skills-sorry-analyzer …` and the shell won't find the wrapper.

```bash
export LEAN4_PLUGIN_ROOT=/path/to/lean4-skills/plugins/lean4
export LEAN4_SCRIPTS=$LEAN4_PLUGIN_ROOT/lib/scripts
export LEAN4_REFS=$LEAN4_PLUGIN_ROOT/skills/lean4/references
export PATH="$LEAN4_PLUGIN_ROOT/bin:$PATH"   # so `lean4-skills-*` wrappers resolve
```

Verify the wrappers are on PATH:

```bash
command -v lean4-skills-sorry-analyzer
# expected: /…/plugins/lean4/bin/lean4-skills-sorry-analyzer
```

## Claude Code (Native Plugin)

```bash
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4
```

That's it! The skill activates automatically when working with `.lean` files.

### Verify

```
/lean4:doctor
```

### Platform Notes

#### Windows

**Option 1: VSCode Extension (recommended)**
- Install [Claude Code for VS Code](https://marketplace.visualstudio.com/items?itemName=anthropic.claude-code)
- No Bash required

**Option 2: Git Bash**
- Install [Git for Windows](https://git-scm.com/download/win)
- Use Git Bash for Claude Code CLI

#### macOS / Linux

No special setup required.

### Troubleshooting

#### Plugin Not Loading

1. Check installation: `/plugin list`
2. Restart Claude Code
3. Run `/lean4:doctor`

#### LSP Server Not Working

1. Verify installation: https://github.com/oOo0oOo/lean-lsp-mcp
2. Run `lake build` in your project first (avoids timeouts). If fresh clone/worktree or after `lake clean`, prime cache first: `lake cache get` or `lake exe cache get`.
3. Restart Claude Code
4. Test: try `lean_goal` on a `.lean` file

#### Environment Variables Not Set

The `LEAN4_SCRIPTS` etc. variables are set by the bootstrap hook. If missing:
1. Restart Claude Code session
2. Check `/lean4:doctor env`

#### Scripts Not Executable

The `lean4-skills-*` wrappers under `$LEAN4_PLUGIN_ROOT/bin/` are shipped
executable. Confirm with:

```bash
command -v lean4-skills-sorry-analyzer
```

If you invoke the unwrapped internals under `$LEAN4_SCRIPTS/` directly
(e.g. test fixtures, internal helpers), and a fresh clone left them
non-executable:

```bash
chmod +x $LEAN4_SCRIPTS/*.sh $LEAN4_SCRIPTS/*.py
```

## OpenAI Codex CLI

Set env vars in your shell profile (replace `/path/to` with your actual clone location):

```bash
export LEAN4_PLUGIN_ROOT=/path/to/lean4-skills/plugins/lean4
export LEAN4_SCRIPTS=$LEAN4_PLUGIN_ROOT/lib/scripts
export LEAN4_REFS=$LEAN4_PLUGIN_ROOT/skills/lean4/references
export PATH="$LEAN4_PLUGIN_ROOT/bin:$PATH"   # so `lean4-skills-*` wrappers resolve
```

Add to your project's `AGENTS.md` (model context — not shell env):

```markdown
## Lean 4 Workflows

See /path/to/lean4-skills/plugins/lean4/skills/lean4/SKILL.md for proving workflows.

Environment:
- LEAN4_PLUGIN_ROOT=/path/to/lean4-skills/plugins/lean4
- LEAN4_SCRIPTS=$LEAN4_PLUGIN_ROOT/lib/scripts
- LEAN4_REFS=$LEAN4_PLUGIN_ROOT/skills/lean4/references
```

Codex also supports installing skills as directories and adding MCP servers.
Check [current Codex docs](https://developers.openai.com/codex/skills/) for
the exact commands — examples:

```bash
# Skill install (check current syntax)
# codex skill add /path/to/lean4-skills/plugins/lean4/skills/lean4

# MCP setup (check current syntax)
# codex mcp add lean-lsp -- npx lean-lsp-mcp --project /path/to/lean/project
```

### Verify

```bash
echo "$LEAN4_SCRIPTS"
lean4-skills-sorry-analyzer . --format=summary --report-only
# If MCP configured: test lean_goal on a .lean file
```

## Gemini CLI

Add to your project's `GEMINI.md` (or global `~/.gemini/GEMINI.md`).

**If your Gemini CLI version supports file includes:**

```markdown
## Lean 4 Workflows
@./lean4-skills/plugins/lean4/skills/lean4/SKILL.md
```

**Manual fallback:** Copy relevant sections of SKILL.md into your GEMINI.md,
or instruct Gemini to read the file:

```markdown
## Lean 4 Workflows
Read ./lean4-skills/plugins/lean4/skills/lean4/SKILL.md for proving workflows.
```

Set env vars in your shell profile:

```bash
export LEAN4_PLUGIN_ROOT=/path/to/lean4-skills/plugins/lean4
export LEAN4_SCRIPTS=$LEAN4_PLUGIN_ROOT/lib/scripts
export LEAN4_REFS=$LEAN4_PLUGIN_ROOT/skills/lean4/references
export PATH="$LEAN4_PLUGIN_ROOT/bin:$PATH"   # so `lean4-skills-*` wrappers resolve
```

### Verify

```bash
echo "$LEAN4_SCRIPTS"
lean4-skills-sorry-analyzer . --format=summary --report-only
```

## Cursor

> These are documented setup patterns, not CI-verified adapters.

Create `.cursor/rules/lean4.mdc` in your project:

```yaml
---
description: Lean 4 theorem proving workflows
globs: ["**/*.lean"]
---
```

Then paste the content of `plugins/lean4/skills/lean4/SKILL.md` into the rule body,
or keep it concise and reference the file path for the agent to read.

Set env vars in your terminal profile (Cursor runs commands in your shell).

### Verify

Open a `.lean` file, ask the agent to run:

```bash
lean4-skills-sorry-analyzer . --format=summary --report-only
```

## Windsurf

> These are documented setup patterns, not CI-verified adapters.

Windsurf uses its own rules format. Adapt the Cursor pattern above to
Windsurf's rule system — see [Windsurf docs](https://docs.windsurf.com/windsurf/getting-started)
for the current config format. The core setup is the same: point the agent at
SKILL.md and set the three env vars.

## OpenCode

> These are documented setup patterns, not CI-verified adapters.

If using [oh-my-opencode](https://github.com/nicobailon/oh-my-opencode) or
your OpenCode setup supports skill discovery, place the skill where it can be found.
Replace `/path/to` with the actual location of your clone:

```bash
# Option A: project-level (copies SKILL.md + references/)
mkdir -p .opencode/skills
cp -r "/path/to/lean4-skills/plugins/lean4/skills/lean4" .opencode/skills/

# Option B: global
mkdir -p ~/.config/opencode/skills
cp -r "/path/to/lean4-skills/plugins/lean4/skills/lean4" ~/.config/opencode/skills/
```

**Without oh-my-opencode:** Point OpenCode at SKILL.md via its instructions
file or paste relevant sections into your project's configuration.

Set env vars in your shell profile:

```bash
export LEAN4_PLUGIN_ROOT=/path/to/lean4-skills/plugins/lean4
export LEAN4_SCRIPTS=$LEAN4_PLUGIN_ROOT/lib/scripts
export LEAN4_REFS=$LEAN4_PLUGIN_ROOT/skills/lean4/references
export PATH="$LEAN4_PLUGIN_ROOT/bin:$PATH"   # so `lean4-skills-*` wrappers resolve
```

OpenCode supports MCP servers — see [OpenCode docs](https://opencode.ai/docs/)
for current MCP setup commands.

### Verify

```bash
echo "$LEAN4_SCRIPTS"
lean4-skills-sorry-analyzer . --format=summary --report-only
```

## Any Agent (Generic)

Any LLM coding agent that can read markdown and run shell commands can use this pack:

1. Clone the repo
2. Set the four env vars (see [Environment Bootstrap](#environment-bootstrap-all-hosts) above) — including `PATH` so the `lean4-skills-*` wrappers resolve as bare commands
3. Point your agent at `plugins/lean4/skills/lean4/SKILL.md` as system context
4. Scripts work standalone — no adapter needed:
   ```bash
   lean4-skills-sorry-analyzer . --format=summary --report-only
   lean4-skills-check-axioms-inline path/to/YourFile.lean --report-only
   lean4-skills-search-mathlib "continuous" name
   ```
5. If your agent supports MCP, add lean-lsp-mcp for faster mathlib search and sub-second feedback

**Optional — skill auto-discovery:** Some setups may support discovering
skills at `.agents/skills/<name>/SKILL.md`. This is host-dependent — check
your agent's docs for supported discovery paths. If supported:

```bash
# Unix/macOS — symlink
mkdir -p .agents/skills
ln -s "/path/to/lean4-skills/plugins/lean4/skills/lean4" .agents/skills/lean4

# Unix/macOS — copy
mkdir -p .agents/skills
cp -r "/path/to/lean4-skills/plugins/lean4/skills/lean4" .agents/skills/lean4

# Windows (Git Bash)
mkdir -p .agents/skills
cp -r "/path/to/lean4-skills/plugins/lean4/skills/lean4" .agents/skills/lean4

# Windows (PowerShell)
New-Item -ItemType Directory -Force -Path .agents\skills
Copy-Item -Recurse "path\to\lean4-skills\plugins\lean4\skills\lean4" .agents\skills\lean4
```

### Verify

```bash
echo "$LEAN4_SCRIPTS"                        # bootstrap set the env var
command -v lean4-skills-sorry-analyzer        # wrapper resolves on PATH
lean4-skills-sorry-analyzer . --format=summary --report-only
```

## Lean LSP MCP Server (All Hosts)

[lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) provides faster mathlib
search and sub-second feedback. Works with any MCP-capable host. Setup: a few minutes.

**What you get:**
- `lean_goal(file, line)` — See exact goal at cursor
- `lean_local_search("keyword")` — Fast local + mathlib (unlimited)
- `lean_leanfinder("goal or query")` — Semantic, goal-aware (rate-limited)
- `lean_leansearch("natural language")` — Semantic search (rate-limited)
- `lean_loogle("?a → ?b → _")` — Type-pattern (rate-limited)
- `lean_hammer_premise(file, line, col)` — Premise suggestions for simp/aesop/grind (rate-limited)
- `lean_multi_attempt(file, line, snippets=[...])` — Test multiple tactics
- `lean_diagnostic_messages(file)` — Per-file error/warning check without a full `lake build`
- …and more (hover info, goal-conditioned search, state inspection, etc.)

**One-time setup:** ~5 minutes. Highly recommended.

Per-host MCP configuration (check each host's latest docs for current syntax):
- **Claude Code** (run from your Lean project root): `claude mcp add --transport stdio --scope user lean-lsp -- uvx lean-lsp-mcp`
- **Codex CLI:** Check [Codex docs](https://developers.openai.com/codex/) for MCP setup
- **Gemini CLI:** Check [Gemini CLI docs](https://github.com/google-gemini/gemini-cli) for MCP setup
- **OpenCode:** Check [OpenCode docs](https://opencode.ai/docs/) for MCP setup
- **Other hosts:** `npx lean-lsp-mcp --project /path/to/lean/project` — connect via your agent's MCP configuration

## Optional: ripgrep

Install `ripgrep` for faster searches:

```bash
# macOS
brew install ripgrep

# Linux
sudo apt install ripgrep

# Windows
winget install BurntSushi.ripgrep.MSVC
```

The workflows and scripts work without it, but searches are slower.

## Migrating from V3 (Claude Code Only)

If you have the old 3-plugin system:

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

### What Changed

| V3 | V4 |
|----|-----|
| 3 plugins | 1 unified plugin |
| `/lean4-theorem-proving:*` | `/lean4:*` |
| `.claude/tools/lean4/` scripts | `$LEAN4_SCRIPTS/` (internal) |
| Memory integration | Removed (didn't work) |

### Legacy Access

```bash
# Pin to legacy tag
/plugin marketplace add cameronfreer/lean4-skills@v3.4.2-legacy

# Or use legacy branch
/plugin marketplace add cameronfreer/lean4-skills#legacy-marketplace
```

## Getting Help

- **Plugin diagnostics (Claude Code):** `/lean4:doctor` — checks environment, plugin, and project
- **Issues:** https://github.com/cameronfreer/lean4-skills/issues
- **LSP server:** https://github.com/oOo0oOo/lean-lsp-mcp/issues
- **Claude Code:** `/help`
