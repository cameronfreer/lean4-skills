---
name: autoprover
description: Planning-first agentic theorem-proving loop with guardrails
user_invocable: true
---

# Lean4 Autoprover

**Status:** Stub - full implementation in Phase 4

This is the main entry point for automated theorem proving with planning-first workflow.

## Planning Phase (MANDATORY)

Before any proof work begins, the autoprover will ask:

1. **Ingredients policy:** mathlib-only / project-local OK / specific imports
2. **Fill scope:** all sorries / specific files / tagged only
3. **Touch policy:** read-only / specific files / full access
4. **Review cadence:** every sorry / every file / every 5 / manual

## Main Loop

```
1. DISCOVER: Analyze sorries with priority scoring
2. SELECT: Pick next sorry (easiest first)
3. ATTEMPT: Search mathlib → fill sorry → agent if needed
4. VALIDATE: lake build + check-axioms (no new axioms/sorries)
5. COMMIT: git commit (never amend)
6. CHECKPOINT: Safe save point
7. REVIEW: Stop at cadence, show progress, ask continue/stop/adjust
8. REPEAT
```

## Guardrails

The following are blocked during autoprover sessions:
- `git push` - use `/lean4:checkpoint`, then push manually
- `git commit --amend` - autoprover creates new commits only
- `gh pr create` - review first, then create PR manually
