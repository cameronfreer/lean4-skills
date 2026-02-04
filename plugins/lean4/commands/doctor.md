---
name: doctor
description: Diagnostics, cleanup, and migration help
user_invocable: true
---

# Lean4 Doctor

**Status:** Stub - full implementation in Phase 4

Diagnostics and cleanup utility for the Lean4 plugin.

## What It Does

1. **Environment Check:** Verifies LEAN4_* environment variables are set
2. **Tool Check:** Verifies lake, lean, and optional tools (loogle, moogle) are available
3. **Plugin Check:** Verifies plugin structure and permissions
4. **Migration Help:** Assists upgrading from v3 to v4

## Usage

Run `/lean4:doctor` when:
- Starting work in a new environment
- Encountering unexpected errors
- After upgrading from v3 to v4

## Migration from V3

If you're upgrading from the legacy 3-plugin system:
1. Uninstall old plugins: `lean4-theorem-proving`, `lean4-memories`, `lean4-subagents`
2. Install unified plugin: `lean4`
3. Run `/lean4:doctor` to verify setup
4. Optionally clean `.claude/tools/lean4` and `.claude/docs/lean4` (now inert)
