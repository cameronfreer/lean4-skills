# Installation Guide

## Installation Tiers

Three install shapes, referenced throughout this guide:

- **Tier 1 — Core skill only.** Host-native installers or direct
  skill-directory copies/links. Installs or copies
  `plugins/lean4/skills/lean4/` — SKILL.md, bundled references, and
  OpenAI UI metadata. It does **not** install the helper runtime
  (`lean4-skills-*` wrappers and their scripts) or register plugin
  commands, lifecycle hooks, or subagent definitions. What you get is
  the instructions and references: the skill's LSP-first workflows
  operate when your host separately provides Lean LSP tools (see
  [Lean LSP MCP Server](#lean-lsp-mcp-server-all-hosts)); script-backed
  steps need Tier 2.
- **Tier 2 — Portable checkout + helper runtime.** One cloned checkout,
  an `.agents/skills` symlink for native discovery, and one environment
  block. Adds the helper runtime (wrappers on PATH, `$LEAN4_SCRIPTS`) to
  the core skill. Does not recreate host-specific commands, hooks, or
  subagent definitions. See
  [Portable Checkout + Helper Runtime](#portable-checkout--helper-runtime-all-hosts).
- **Tier 3 — Native plugin.** The complete experience — commands, hooks,
  guardrails, subagents. Claude Code today (next section); a native
  Codex plugin is tracked in
  [#153](https://github.com/cameronfreer/lean4-skills/issues/153).

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

## Portable Checkout + Helper Runtime (All Hosts)

The recommended full setup (Tier 2) for every host except Claude Code.
Codex, Cursor, Windsurf, OpenCode, GitHub Copilot, and Gemini CLI all
discover Agent Skills from `~/.agents/skills` (and its project-level
`.agents/skills` counterpart); Codex documents symlink support — for a
host that doesn't state it or doesn't follow symlinks, copy instead.

One maintained checkout, one link:

```bash
git clone https://github.com/cameronfreer/lean4-skills.git "$HOME/.local/share/lean4-skills"
mkdir -p "$HOME/.agents/skills"
rm -rf "$HOME/.agents/skills/lean4"   # clear any prior copy first — see note below
ln -sfn "$HOME/.local/share/lean4-skills/plugins/lean4/skills/lean4" "$HOME/.agents/skills/lean4"
```

The `rm -rf` guard matters when upgrading from a Tier-1 copy:
`ln -sfn` replaces an existing sym*link* but not an existing real
directory — without the guard it would nest the link inside the old
copy (`lean4/lean4`) while the stale top-level copy stays active.

Then add the environment block to your shell profile (`~/.bashrc`,
`~/.zshrc`, …). This is the canonical copy — the host sections below
link here instead of repeating it:

```bash
export LEAN4_PLUGIN_ROOT="$HOME/.local/share/lean4-skills/plugins/lean4"
export LEAN4_SCRIPTS=$LEAN4_PLUGIN_ROOT/lib/scripts
export LEAN4_REFS=$LEAN4_PLUGIN_ROOT/skills/lean4/references
export PATH="$LEAN4_PLUGIN_ROOT/bin:$PATH"   # so `lean4-skills-*` wrappers resolve
```

### Verify

```bash
command -v lean4-skills-sorry-analyzer
# expected: …/lean4-skills/plugins/lean4/bin/lean4-skills-sorry-analyzer
lean4-skills-sorry-analyzer . --format=summary --report-only
```

### Portability notes

- The helper runtime requires a POSIX-compatible shell. On Windows use
  WSL or Git Bash; without one, use a Tier-1 copy (below) — the skill's
  LSP-first workflows don't need the scripts.
- GUI hosts must actually inherit the shell-profile exports to see the
  wrappers. If `command -v lean4-skills-sorry-analyzer` succeeds in your
  terminal but the agent can't find it, launch the app from that
  terminal or set the variables in the host's own environment settings.

### Windows copy variant (no symlink)

The `Remove-Item` / `rm -rf` first matters: copying onto an existing
destination directory nests the source inside it (`lean4/lean4`),
leaving the discovered top-level skill stale.

```powershell
New-Item -ItemType Directory -Force -Path $HOME\.agents\skills
Remove-Item -Recurse -Force -ErrorAction SilentlyContinue $HOME\.agents\skills\lean4
Copy-Item -Recurse "$HOME\.local\share\lean4-skills\plugins\lean4\skills\lean4" $HOME\.agents\skills\lean4
```

Git Bash equivalent:

```bash
mkdir -p ~/.agents/skills
rm -rf ~/.agents/skills/lean4
cp -r "$HOME/.local/share/lean4-skills/plugins/lean4/skills/lean4" ~/.agents/skills/lean4
```

A copy does not track the checkout — re-run the replace-copy above
after each update.

### Update

```bash
git -C "$HOME/.local/share/lean4-skills" pull
```

The symlink keeps pointing at the updated checkout; copies must be
replaced (delete, then re-copy — see the copy variant above).

### Uninstall

```bash
rm -f "$HOME/.agents/skills/lean4"        # rm -rf if you copied
rm -rf "$HOME/.local/share/lean4-skills"
```

Then remove the environment block from your shell profile.

## OpenAI Codex CLI

**Quick install (Tier 1 — core skill only).** Run this in Codex chat,
not in your shell:

```text
$skill-installer Install the `lean4` skill from
https://github.com/cameronfreer/lean4-skills/tree/main/plugins/lean4/skills/lean4
```

On your next turn, invoke it explicitly with `$lean4`, or let Codex
activate it automatically for Lean 4 tasks. This installs the core
skill instructions, references, and metadata only — not the
`lean4-skills-*` helper executables, plugin hooks, subagent
definitions, or the Claude Code `/lean4:*` command surface.

> `$skill-installer` manages its own install location under
> `$CODEX_HOME/skills` (`~/.codex/skills` by default), while manual
> checkout/link installs belong in `~/.agents/skills`. Don't assume or
> prescribe the installer's destination — after installing, verify that
> `$lean4` is discovered (type `$` or run `/skills`).

**Full setup (Tier 2, recommended).** Use the
[Portable Checkout + Helper Runtime](#portable-checkout--helper-runtime-all-hosts)
— Codex discovers `.agents/skills` in your project and home directory
and follows symlinked skill directories.

> **Moving from Tier 1 to Tier 2:** Codex does not merge duplicate
> same-name skills, so a `$skill-installer` copy under
> `$CODEX_HOME/skills/lean4` and the Tier-2 `~/.agents/skills/lean4`
> link can both appear. Remove the installer copy
> (`rm -rf "${CODEX_HOME:-$HOME/.codex}/skills/lean4"`) when you switch.

**Optional `AGENTS.md` pointer.** `AGENTS.md` is for durable project
guidance, not installation. If your project uses one, a single line is
enough:

```markdown
For Lean 4 proving workflows, use the `lean4` skill ($lean4).
```

**MCP:** check the [Codex MCP docs](https://learn.chatgpt.com/docs/extend/mcp)
for the exact command — e.g.:

```bash
codex mcp add lean-lsp -- uvx lean-lsp-mcp
```

### Verify

In Codex chat, type `$` — `lean4` should appear in the skill list. With
the full setup, also:

```bash
command -v lean4-skills-sorry-analyzer
lean4-skills-sorry-analyzer . --format=summary --report-only
```

## Gemini CLI

> **Availability:** consumer Gemini CLI access (free / Google AI Pro /
> Ultra) transitioned to [Antigravity CLI](#antigravity-cli) on
> June 18, 2026; Gemini CLI continues for Standard/Enterprise licenses
> and supported API-key users. The instructions below apply to
> supported Gemini CLI installations.

Gemini CLI has native Agent Skills: it discovers `.gemini/skills/` and
the portable `.agents/skills/` locations (project and user scope), so
the [Portable Checkout](#portable-checkout--helper-runtime-all-hosts)
symlink covers it (Tier 2 — recommended; the canonical environment
block lives there too). Alternatively, link the skill from your
checkout explicitly — from your shell, so `$HOME` expands (Gemini's
interactive `/skills link` passes the path through literally, without
shell expansion):

```bash
gemini skills link "$HOME/.local/share/lean4-skills/plugins/lean4/skills/lean4" --scope user
```

**Quick install (Tier 1 — core skill only):**

```bash
gemini skills install https://github.com/cameronfreer/lean4-skills.git \
  --path plugins/lean4/skills/lean4 --scope user
```

This copies the skill directory only — see
[Installation Tiers](#installation-tiers) for what that excludes.

### Verify

Run `/skills list` in Gemini — `lean4` should appear. With the full
setup, also:

```bash
command -v lean4-skills-sorry-analyzer
lean4-skills-sorry-analyzer . --format=summary --report-only
```

### Antigravity CLI

Antigravity CLI (Gemini CLI's consumer successor) retains Agent Skills
and shares the workspace `.agents/skills/` location, so the
[Portable Checkout](#portable-checkout--helper-runtime-all-hosts)
symlink covers it (Tier 2). Skill-only install (Tier 1) via GitHub CLI
≥ 2.90.0 — note the agent id is `antigravity`, and gh places the skill
(namespaced `lean4/lean4`) under `~/.gemini/antigravity/skills/`:

```bash
gh skill install cameronfreer/lean4-skills lean4@main \
  --agent antigravity --scope user
```

## Cursor

Cursor discovers Agent Skills natively from `.agents/skills/`,
`.cursor/skills/`, `~/.agents/skills/`, and `~/.cursor/skills/` —
the [Portable Checkout](#portable-checkout--helper-runtime-all-hosts)
symlink covers it (Tier 2 — recommended; the canonical environment
block lives there, and Cursor runs commands in your shell). For a
skill-only install (Tier 1), copy `plugins/lean4/skills/lean4/` into
`.cursor/skills/lean4/` instead.

Invoke manually by typing `/lean4` in Agent chat, or let Cursor
activate the skill automatically for Lean 4 tasks. (The previous
`.cursor/rules/lean4.mdc` pattern is obsolete — native skills replace
project rules for this use.)

### Verify

Type `/lean4` in Agent chat — the skill should be listed. With the full
setup, open a `.lean` file and ask the agent to run:

```bash
lean4-skills-sorry-analyzer . --format=summary --report-only
```

## Windsurf

Windsurf (Cascade) discovers skills from `.windsurf/skills/` and
`~/.codeium/windsurf/skills/`, plus the portable `.agents/skills/` and
`~/.agents/skills/` locations — the
[Portable Checkout](#portable-checkout--helper-runtime-all-hosts)
covers it (Tier 2). For a skill-only install (Tier 1), copy
`plugins/lean4/skills/lean4/` into `.windsurf/skills/lean4/`.

Invoke manually with `@lean4` in Cascade. See the
[Windsurf skills docs](https://docs.devin.ai/desktop/cascade/skills)
for current behavior.

## OpenCode

OpenCode loads skills on demand through its native `skill` tool. It
discovers `.opencode/skills/`, `.claude/skills/`, and `.agents/skills/`
in the project, plus `~/.config/opencode/skills/`, `~/.claude/skills/`,
and `~/.agents/skills/` globally — the
[Portable Checkout](#portable-checkout--helper-runtime-all-hosts)
covers it (Tier 2 — recommended; canonical environment block there).
Skill-only copy (Tier 1; the `rm -rf` keeps a re-copy from nesting
`lean4/lean4`):

```bash
mkdir -p ~/.config/opencode/skills
rm -rf ~/.config/opencode/skills/lean4
cp -r "$HOME/.local/share/lean4-skills/plugins/lean4/skills/lean4" ~/.config/opencode/skills/
```

OpenCode supports MCP servers — see [OpenCode docs](https://opencode.ai/docs/)
for current MCP setup commands.

### Verify

Ask OpenCode to use the `lean4` skill — its `skill` tool should load
it. With the full setup, also:

```bash
command -v lean4-skills-sorry-analyzer
lean4-skills-sorry-analyzer . --format=summary --report-only
```

## GitHub Copilot

Copilot discovers Agent Skills in `.github/skills/`, `.claude/skills/`,
and `.agents/skills/` (repository), plus `~/.copilot/skills/` and
`~/.agents/skills/` (personal) — the
[Portable Checkout](#portable-checkout--helper-runtime-all-hosts)
covers personal use (Tier 2). Skills work with the Copilot cloud coding
agent, Copilot CLI, and VS Code agent mode.

**Quick install (Tier 1 — core skill only)** with GitHub CLI ≥ 2.90.0
(`gh skill` is in public preview). Use the plain `lean4` name — the
namespaced `lean4/lean4` selector previews on ≥ 2.91.0 but is not
accepted by `install`. Pin `@main` — an unpinned install resolves the
repository's latest GitHub release, which lags `main`:

```bash
gh skill preview cameronfreer/lean4-skills lean4@main
gh skill install cameronfreer/lean4-skills lean4@main \
  --agent github-copilot --scope user
```

gh stores the installed skill namespaced as `lean4/lean4` under the
agent's skills directory.

This installs the skill directory only — see
[Installation Tiers](#installation-tiers) for what that excludes.

### Verify

```bash
gh skill list
```

`lean4` should appear. With the full setup, also
`command -v lean4-skills-sorry-analyzer`.

## Any Agent (Generic)

Any LLM coding agent that can read markdown and run shell commands can use this pack:

1. Do the [Portable Checkout + Helper Runtime](#portable-checkout--helper-runtime-all-hosts)
   setup — one clone, an optional `.agents/skills` link (if your agent
   supports skill discovery there), and the canonical environment block
2. Point your agent at `plugins/lean4/skills/lean4/SKILL.md` as system context
3. Scripts work standalone — no adapter needed:
   ```bash
   lean4-skills-sorry-analyzer . --format=summary --report-only
   lean4-skills-check-axioms-inline path/to/YourFile.lean --report-only
   lean4-skills-search-mathlib "continuous" name
   ```
4. If your agent supports MCP, add lean-lsp-mcp for faster mathlib search and sub-second feedback

### Verify

```bash
echo "$LEAN4_SCRIPTS"                        # shell-profile env block set the variable
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
