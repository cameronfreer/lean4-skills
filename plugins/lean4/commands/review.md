---
name: review
description: Read-only code review of Lean proofs
user_invocable: true
---

# Lean4 Review

**Status:** Stub - full implementation in Phase 4

Read-only review mode for examining Lean proofs without modification.

## What It Does

1. Analyzes proof structure and complexity
2. Identifies potential improvements
3. Checks for style issues
4. Reports axiom usage
5. Suggests golfing opportunities

## Usage

Use `/lean4:review` to get a comprehensive review of your proofs before finalizing.

## Sandbox Mode

Review operates in read-only mode - it will NOT modify any files. This is safe to run at any time without affecting your work.
