---
name: autoprover
description: Planning-first agentic theorem-proving loop with guardrails
user_invocable: true
---

# Lean4 Autoprover

Main entry point for automated theorem proving. Planning-first, LSP-powered, with safety guardrails.

---

## Quick Start

```
/lean4:autoprover                    # Start interactive session
/lean4:autoprover File.lean          # Focus on specific file
/lean4:autoprover --repair-only      # Fix build errors without filling sorries
```

---

## Philosophy

**Search before prove.** Most sorries exist in mathlib. Search exhaustively before writing tactics.

**LSP first, scripts as fallback.** Lean LSP MCP tools provide sub-second feedback. Scripts are backup when LSP unavailable.

**Small commits, easy rollback.** Each sorry = one commit. Never amend. Easy to undo mistakes.

**Human in the loop.** Planning phase is mandatory. Review checkpoints require confirmation.

---

## Phase 1: Planning (Required)

Before any proof work, establish scope and preferences.

### 1.1 Discover Current State

**With LSP (preferred):**
```
lean_diagnostic_messages(file) → get all errors/warnings
lean_goal(file, line) at each sorry → understand what needs proving
```

**Fallback:**
```bash
lake build 2>&1 | head -50
grep -rn "sorry" --include="*.lean" .
```

### 1.2 Planning Questions

Ask user preferences via AskUserQuestion:

**Scope:** All sorries / specific files / specific theorems

**Approach:**
- **Conservative** - Only fill obvious cases, skip anything uncertain
- **Balanced** (default) - Try reasonable approaches, escalate when stuck
- **Aggressive** - Try harder, may need more rollbacks

**Review cadence:** Every change / every file / every 5 / manual checkpoints

### 1.3 Plan Preview

Show before any writes:

```markdown
## Autoprover Plan

**Found:** 8 sorries in 3 files
**Approach:** Balanced
**Review:** Every 5 changes

### Sorries Found
- `Helpers.lean:15` - in `trivial_lemma`
- `Helpers.lean:42` - in `helper_bound`
- `Core.lean:89` - in `main_theorem`
...

**Proceed?** (yes / adjust / cancel)
```

User must confirm before writes begin.

**Note:** The order is file-first (grouped by file), not complexity-ranked. Claude will assess difficulty when working on each sorry.

---

## Phase 2: Main Loop

### For Each Sorry

#### Step 1: Understand the Goal

**With LSP:**
```
lean_goal(file, line) → see exact goal and context
lean_hover_info(file, line, col) → understand types
```

Read surrounding code to understand proof strategy.

#### Step 2: Search First

**Always search before writing tactics.**

**With LSP (preferred):**
```
lean_leansearch("natural language description of goal")
lean_loogle("type pattern like: _ + _ = _ + _")
lean_local_search("keyword from goal")
```

**Fallback:**
```bash
bash $LEAN4_SCRIPTS/smart_search.sh "query" --source=all
```

If exact lemma found → apply it directly.

#### Step 3: Try Simple Tactics

If no exact match, try automation in order:
1. `rfl` - definitional equality
2. `simp` - simplification
3. `ring` / `linarith` / `omega` - arithmetic
4. `exact?` / `apply?` - tactic search (slow but thorough)
5. `aesop` - general automation

**With LSP:**
```
lean_multi_attempt(file, line, ["simp", "ring", "linarith"]) → test multiple tactics
```

**Without LSP:**
Edit file, run `lake build`, check result.

#### Step 4: If Stuck, Think Harder

When simple tactics fail:
- Re-read the goal and hypotheses
- Search mathlib more creatively
- Consider what intermediate steps might help
- Look at similar proofs in the codebase

This is where Claude's reasoning helps more than any script.

#### Step 5: Validate

After each change:
```bash
lake build
```

Check:
- Build passes
- Sorry count decreased (not increased!)
- No new axioms introduced

#### Step 6: Commit

```bash
git add [file]
git commit -m "fill: [theorem_name] - [tactic/lemma used]"
```

**Never amend.** Each fill = one commit = easy rollback.

---

## Repair Mode

When build fails (not just sorries), autoprover shifts to repair:

### Repair Workflow

1. **Parse error** - Understand what went wrong
2. **Classify** - Type mismatch? Unknown ident? Synth failure?
3. **Search** - Look for correct API/lemma
4. **Fix** - Apply minimal change
5. **Verify** - Build again

### Common Repairs

| Error | Typical Fix |
|-------|-------------|
| `type mismatch` | Add coercion, use `convert`, fix argument |
| `unknown identifier` | Search mathlib, add import, fix typo |
| `failed to synthesize` | Add `haveI`/`letI`, check instance availability |
| `timeout` | Narrow `simp`, add explicit types |

### Repair vs Fill

```
/lean4:autoprover              # Fill sorries (requires build passing)
/lean4:autoprover --repair-only # Fix build errors only
```

Repair mode is also triggered automatically when a fill breaks the build.

---

## Phase 3: Review Checkpoints

At configured intervals, pause and report:

```markdown
## Progress

**Filled:** 5/8 sorries
**Commits:** 5 new
**Build:** passing

**Current:** Core.lean:89 - `main_theorem`
**Status:** Searching mathlib...

**Options:**
- `continue` - Keep going
- `stop` - Save progress and exit
- `skip` - Skip current sorry, try next
- `rollback N` - Undo last N commits
```

---

## Phase 4: Completion

```markdown
## Autoprover Complete

**Results:**
- Filled: 7/8 sorries
- Commits: 7
- Remaining: 1 (marked as needs-manual)

**Unfilled:**
- `Core.lean:156` - `hard_lemma`: Needs domain expertise

**Next steps:**
1. `/lean4:review` - Check quality
2. `/lean4:golf` - Optimize proofs
3. `git push` - When ready (manual)
```

---

## Guardrails

Blocked during autoprover (enforced by hooks):

| Action | Why | Alternative |
|--------|-----|-------------|
| `git push` | Review first | Push manually after checkpoint |
| `git commit --amend` | Preserve history | New commits only |
| `gh pr create` | Review first | Create PR manually |

---

## Tips

**When stuck on a sorry:**
- Read the goal type carefully
- Search mathlib with different keywords
- Look at how similar theorems are proved nearby
- Consider if the statement needs adjustment
- Ask: "What would a mathematician do here?"

**When repairs keep failing:**
- Step back and understand the error
- Check if the approach is fundamentally wrong
- Sometimes the fix is in a different file
- Don't fight the type checker - understand what it wants

**For faster iteration:**
- Use Lean LSP MCP for sub-second feedback
- Keep `lake build` running in watch mode
- Work on one sorry at a time, fully complete it

---

## See Also

- `/lean4:checkpoint` - Manual save point
- `/lean4:review` - Quality check (read-only)
- `/lean4:golf` - Optimize proofs
- `/lean4:doctor` - Troubleshooting
