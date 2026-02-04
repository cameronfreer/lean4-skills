# Installation Guide

## Quick Start

```bash
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4
```

That's it! The skill activates automatically when working with `.lean` files.

## Verify Installation

```
/lean4:doctor
```

This checks your environment and reports any issues.

## Recommended: Lean LSP MCP Server

The LSP server provides **sub-second feedback** instead of 30+ second builds.

**Setup:** https://github.com/oOo0oOo/lean-lsp-mcp

**What you get:**
- `lean_goal(file, line)` - See exact goal at cursor
- `lean_local_search("keyword")` - Fast local + mathlib (unlimited)
- `lean_leanfinder("goal or query")` - Semantic, goal-aware (rate-limited)
- `lean_leansearch("natural language")` - Semantic search (rate-limited)
- `lean_loogle("?a → ?b → _")` - Type-pattern (rate-limited)
- `lean_multi_attempt(file, line, snippets=[...])` - Test tactics

**One-time setup:** ~5 minutes. Highly recommended.

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

The plugin works without it, but searches are slower.

## Platform Notes

### Windows

**Option 1: VSCode Extension (recommended)**
- Install [Claude Code for VS Code](https://marketplace.visualstudio.com/items?itemName=anthropic.claude-code)
- No Bash required

**Option 2: Git Bash**
- Install [Git for Windows](https://git-scm.com/download/win)
- Use Git Bash for Claude Code CLI

### macOS / Linux

No special setup required.

## Migrating from V3

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

## Troubleshooting

### Plugin Not Loading

1. Check installation: `/plugin list`
2. Restart Claude Code
3. Run `/lean4:doctor`

### LSP Server Not Working

1. Verify installation: https://github.com/oOo0oOo/lean-lsp-mcp
2. Run `lake build` in your project first (avoids timeouts)
3. Restart Claude Code
4. Test: try `lean_goal` on a `.lean` file

### Environment Variables Not Set

The `LEAN4_SCRIPTS` etc. variables are set by the bootstrap hook. If missing:
1. Restart Claude Code session
2. Check `/lean4:doctor env`

### Scripts Not Executable

```bash
chmod +x $LEAN4_SCRIPTS/*.sh $LEAN4_SCRIPTS/*.py
```

## Getting Help

- **Plugin diagnostics:** `/lean4:doctor` - checks environment, plugin, and project
- **Issues:** https://github.com/cameronfreer/lean4-skills/issues
- **LSP server:** https://github.com/oOo0oOo/lean-lsp-mcp/issues
- **Claude Code:** `/help`
