---
name: checkpoint
description: Save progress with a safe commit checkpoint
user_invocable: true
---

# Lean4 Checkpoint

**Status:** Stub - full implementation in Phase 4

Creates a safe checkpoint commit for your current proof progress.

## What It Does

1. Runs `lake build` to verify current state compiles
2. Runs axiom check to ensure no unwanted axioms introduced
3. Creates a commit with descriptive message
4. Reports checkpoint status

## Usage

Use `/lean4:checkpoint` when you want to save your progress at a known-good state before continuing work or before pushing manually.

## Notes

- Does NOT push to remote (you do that manually)
- Does NOT amend previous commits (creates new commits only)
- Safe to use multiple times during a session
