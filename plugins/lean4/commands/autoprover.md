---
name: autoprover
description: Planning-first agentic theorem-proving loop with guardrails
user_invocable: true
---

# Lean4 Autoprover

Main entry point for automated theorem proving. Planning-first, LSP-powered, with safety guardrails.

## Usage

```
/lean4:autoprover                    # Start interactive session
/lean4:autoprover File.lean          # Focus on specific file
/lean4:autoprover --repair-only      # Fix build errors without filling sorries
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| file | No | Specific file to focus on |
| --repair-only | No | Fix build errors only, skip sorry-filling |

## Philosophy

- **Search before prove** - Most sorries exist in mathlib
- **LSP first** - Sub-second feedback; scripts as fallback
- **Small commits** - Each sorry = one commit for easy rollback
- **Human in loop** - Planning phase mandatory, review checkpoints required

## Actions

### Phase 1: Planning (Required)

1. **Discover state** via LSP or fallback:
   ```
   lean_diagnostic_messages(file)    # errors/warnings
   lean_goal(file, line)             # at each sorry
   ```
2. **Ask preferences** - Scope, approach (conservative/balanced/aggressive), review cadence
3. **Show plan** - List sorries found, get user confirmation

### Phase 2: Main Loop (Per Sorry)

1. **Understand** - `lean_goal` + read surrounding code
2. **Search first** - `lean_leansearch`, `lean_loogle`, `lean_local_search`
3. **Try tactics** - `rfl`, `simp`, `ring`, `linarith`, `exact?`, `aesop`
4. **Validate** - `lake build`, check sorry count decreased
5. **Commit** - `git commit -m "fill: [theorem] - [tactic]"`

### Phase 3: Review Checkpoints

At configured intervals, show progress and options: continue, stop, skip, rollback.

### Phase 4: Completion

Report filled/remaining sorries, suggest next steps.

## Repair Mode

When build fails, shift to repair workflow:

| Error | Typical Fix |
|-------|-------------|
| `type mismatch` | Add coercion, `convert`, fix argument |
| `unknown identifier` | Search mathlib, add import |
| `failed to synthesize` | Add `haveI`/`letI` |
| `timeout` | Narrow `simp`, add explicit types |

## Output

Progress reports at checkpoints; final summary with filled/remaining counts.

## Safety

- `git push` blocked (review first)
- `git commit --amend` blocked (preserve history)
- `gh pr create` blocked (review first)

## See Also

- `/lean4:checkpoint` - Manual save point
- `/lean4:review` - Quality check (read-only)
- `/lean4:golf` - Optimize proofs
- [Examples](../skills/lean4/references/command-examples.md#autoprover)
