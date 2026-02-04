---
name: doctor
description: Diagnostics, cleanup, and migration help
user_invocable: true
---

# Lean4 Doctor

Diagnostics, troubleshooting, and migration assistance for the Lean4 plugin.

---

## What It Does

1. **Environment Check** - Verify required tools and variables
2. **Plugin Check** - Verify plugin structure and permissions
3. **Project Check** - Verify Lean project setup
4. **Migration Help** - Assist upgrading from v3 to v4
5. **Cleanup** - Remove obsolete files from previous versions

---

## Usage

```
/lean4:doctor              # Full diagnostic
/lean4:doctor env          # Environment only
/lean4:doctor migrate      # Migration assistance
/lean4:doctor cleanup      # Remove obsolete files
```

---

## Environment Check

### Required Tools

| Tool | Check | Required |
|------|-------|----------|
| `lean` | `lean --version` | Yes |
| `lake` | `lake --version` | Yes |
| `python3` | `python3 --version` | For scripts |
| `git` | `git --version` | For commits |

### Environment Variables

| Variable | Purpose | Set By |
|----------|---------|--------|
| `LEAN4_PLUGIN_ROOT` | Plugin installation path | bootstrap.sh |
| `LEAN4_SCRIPTS` | Scripts directory | bootstrap.sh |
| `LEAN4_REFS` | References directory | bootstrap.sh |
| `LEAN4_PYTHON_BIN` | Python interpreter | bootstrap.sh |

### Optional Tools

| Tool | Check | Benefit |
|------|-------|---------|
| `rg` (ripgrep) | `rg --version` | 10-100x faster search |
| Lean LSP MCP | MCP server check | Sub-second feedback |
| Loogle | API check | Type-based search |
| LeanSearch | API check | Natural language search |

---

## Plugin Check

### Structure Verification

```
plugins/lean4/
├── .claude-plugin/plugin.json  ✓
├── commands/
│   ├── autoprover.md           ✓
│   ├── checkpoint.md           ✓
│   ├── doctor.md               ✓
│   ├── golf.md                 ✓
│   └── review.md               ✓
├── hooks/
│   ├── bootstrap.sh            ✓ (executable)
│   ├── guardrails.sh           ✓ (executable)
│   └── hooks.json              ✓
├── skills/lean4/
│   ├── SKILL.md                ✓
│   └── references/             ✓ (23 files)
├── agents/                     ✓ (5 files)
└── lib/scripts/                ✓ (12 files, executable)
```

### Permission Check

```bash
ls -la $LEAN4_PLUGIN_ROOT/hooks/*.sh
ls -la $LEAN4_SCRIPTS/*.sh $LEAN4_SCRIPTS/*.py
```

All `.sh` and `.py` files should have execute permission.

---

## Project Check

### Lean Project Structure

```
your-project/
├── lakefile.lean    ✓
├── lean-toolchain   ✓
├── lake-manifest.json
└── .lake/
    └── packages/
        └── mathlib/  (if using mathlib)
```

### Build Test

```bash
lake build
```

Report:
- ✓ Build passes, OR
- ✗ Build fails (show first error)

### Sorry Count

```bash
${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/sorry_analyzer.py . --format=summary
```

---

## Migration from V3

### What Changed in V4

| V3 (3 plugins) | V4 (unified) |
|----------------|--------------|
| `lean4-theorem-proving` | `lean4` |
| `lean4-memories` | Removed (did not work reliably) |
| `lean4-subagents` | Integrated into `lean4` |
| `/lean4-theorem-proving:*` commands | `/lean4:*` commands |
| `.claude/tools/lean4/` | `$LEAN4_SCRIPTS/` |

### Migration Steps

**Step 1: Uninstall old plugins**
```
/plugin uninstall lean4-theorem-proving
/plugin uninstall lean4-memories
/plugin uninstall lean4-subagents
```

**Step 2: Install unified plugin**
```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4
```

**Step 3: Verify installation**
```
/lean4:doctor
```

**Step 4: Optional cleanup**

Old plugins may have created files in your workspace:
```
.claude/tools/lean4/      # Scripts (now in plugin)
.claude/docs/lean4/       # Docs (now in plugin)
```

These are now inert but can be removed:
```bash
rm -rf .claude/tools/lean4 .claude/docs/lean4
```

### Legacy Access

If you need the old 3-plugin version:

**Pin to legacy tag:**
```
/plugin marketplace add cameronfreer/lean4-skills@v3.4.2-legacy
```

**Or use legacy branch:**
```
/plugin marketplace add cameronfreer/lean4-skills#legacy-marketplace
```

---

## Cleanup

### Remove Obsolete Files

The `/lean4:doctor cleanup` command will:

1. **Identify** obsolete files from v3:
   - `.claude/tools/lean4/` (if exists)
   - `.claude/docs/lean4/` (if exists)

2. **Show** what will be removed

3. **Ask** for confirmation before deleting

### Manual Cleanup

```bash
# Check what exists
ls -la .claude/tools/lean4/ 2>/dev/null
ls -la .claude/docs/lean4/ 2>/dev/null

# Remove if desired
rm -rf .claude/tools/lean4 .claude/docs/lean4
```

---

## Troubleshooting

### "LEAN4_SCRIPTS not set"

The bootstrap hook didn't run. Try:
1. Restart Claude Code session
2. Verify hooks.json is valid JSON
3. Check bootstrap.sh is executable

### "lake: command not found"

Lean/Lake not installed or not in PATH:
```bash
# Check elan installation
elan show

# Install if needed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### "Scripts not executable"

Fix permissions:
```bash
chmod +x $LEAN4_SCRIPTS/*.sh $LEAN4_SCRIPTS/*.py
```

### "Build fails but worked before"

```bash
# Update dependencies
lake update

# Clean and rebuild
lake clean
lake build
```

### "Guardrails blocking valid command"

If you need to bypass guardrails (use carefully):
- Edit `hooks/guardrails.sh` to allow specific patterns
- Or temporarily disable the hook

---

## Output Format

```markdown
## Lean4 Doctor Report

### Environment
✓ lean 4.x.x
✓ lake 4.x.x
✓ python3 3.x.x
✓ git 2.x.x
⚠️ rg not found (optional, recommended)

### Plugin
✓ LEAN4_PLUGIN_ROOT set
✓ LEAN4_SCRIPTS set
✓ Hooks executable
✓ Scripts executable (12 files)
✓ References present (23 files)
✓ Agents present (5 files)

### Project
✓ lakefile.lean found
✓ lean-toolchain found
✓ Build passes
→ 5 sorries in 2 files

### Migration
✓ No v3 artifacts found
  (or: ⚠️ Found .claude/tools/lean4/ - run /lean4:doctor cleanup)

### Status: Ready
All checks passed. Run /lean4:autoprover to start.
```

---

## Example

```
User: /lean4:doctor

Claude: Running diagnostics...

## Lean4 Doctor Report

### Environment
✓ lean 4.15.0
✓ lake 4.15.0
✓ python3 3.11.2
✓ git 2.43.0
✓ rg 14.1.0

### Plugin
✓ LEAN4_PLUGIN_ROOT=/home/user/.claude/plugins/lean4
✓ LEAN4_SCRIPTS=/home/user/.claude/plugins/lean4/lib/scripts
✓ Hooks executable
✓ Scripts executable (12 files)

### Project
✓ lakefile.lean found
✓ lean-toolchain: leanprover/lean4:v4.15.0
✓ Build passes
→ 3 sorries in Core.lean

### Migration
✓ Clean installation (no v3 artifacts)

### Status: Ready

Your environment is configured correctly.
Run /lean4:autoprover to fill the 3 remaining sorries.
```

---

## See Also

- `/lean4:autoprover` - Main theorem-proving workflow
- `/lean4:checkpoint` - Save verified progress
- `/lean4:review` - Read-only code review
- [INSTALLATION.md](../../INSTALLATION.md) - Setup guide
