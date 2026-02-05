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
/lean4:autoprover --deep             # Enable escalation for stubborn sorries
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| file | No | Specific file to focus on |
| --repair-only | No | Fix build errors only, skip sorry-filling |
| --deep | No | Allow escalation to deep mode |
| --deep-budget | No | Limit deep mode: `2` (sorries) or `15m` (time) |
| --autonomy | No | `manual`, `assisted` (default), or `auto` |
| --review-every | No | `N` (sorries), `checkpoint` (default), or `never` |
| --codex | No | Use external Codex for reviews (sets review source to External) |
| --golf | No | `prompt` (default), `auto`, or `never` |

## Philosophy

- **Search before prove** - Most sorries exist in mathlib
- **LSP first** - Use `lean_goal` + `lean_local_search` + `lean_multi_attempt` before scripts. Log which tools used per sorry. Only fall back to scripts if LSP unavailable or inconclusive.
- **Small commits** - Each sorry = one commit for easy rollback
- **Human in loop** - Planning phase mandatory, review checkpoints configurable

## Fast Path vs Deep Mode

### Fast Path (Default)

Inline sorry-filling with constraints:
1. `lean_goal` → `lean_local_search` / `lean_leansearch` / `lean_loogle`
2. Generate 2-3 candidates, test with `lean_multi_attempt`
3. Apply shortest working proof
4. **On failure: skip sorry, continue** (no escalation)

**Constraints:** Max 3 candidates, ≤80 lines diff, NO statement changes, NO cross-file refactoring.

### Deep Mode (`--deep`)

Enables escalation for stubborn sorries with mandatory budgets and checkpoints.

**Budget Options:**
- `--deep-budget=2` — max 2 sorries per deep cycle (default)
- `--deep-budget=15m` — max 15 minutes per deep cycle

**Deep Cycle Flow:**
1. Fast path runs first
2. On failure, escalate to deep sorry-filling workflow
3. After each deep attempt:
   - Run `lake build`
   - Commit if clean
   - Summarize what changed
   - Prompt: "Continue deep / Pause / Run review / Stop"

**Statement changes require approval:**
```
## Statement Change Required
Current: theorem foo (x : ℕ) : P x
Proposed: theorem foo (x : ℤ) : P x
Approve? (yes / no / suggest alternative)
```

Deep mode allows: multi-file refactoring, helper extraction, statement generalization (with approval).

## Actions

### Phase 1: Planning (Required)

1. **Discover state** via LSP or fallback:
   ```
   lean_diagnostic_messages(file)    # errors/warnings
   lean_goal(file, line)             # at each sorry
   ```
2. **Ask preferences** - Scope and review cadence
3. **Session Preferences** (once per session):

   **Autonomy Mode:**
   > How much control do you want?
   > 1) Manual — ask before any fix
   > 2) Assisted (recommended) — apply safe fixes, ask before risky/deep
   > 3) Auto — apply fixes + commits + reviews per cadence

   **Review Source:**
   > How should reviews be conducted?
   > 1) Internal (recommended) — Claude reviews and can apply fixes
   > 2) External (Codex) — advice only; user pastes results
   > 3) Both — internal first, then external advice
   > 4) None — no automatic reviews

   Store choice for session. If `--codex` flag passed, set External automatically.

   **Review Cadence** (for assisted/auto modes):
   > When should reviews run?
   > - `--review-every=N` — after every N sorries filled
   > - `--review-every=checkpoint` — at each checkpoint (default)
   > - `--review-every=never` — only on explicit request

   **Falsification Policy:**
   > If a statement looks false, should I:
   > 1) Add counterexample + salvage lemmas only (recommended)
   > 2) Retire original to a def and prove its negation
   > 3) Ask each time

   Default: (1). No statement rewrites, no `¬P` if `theorem T : P := by sorry` exists.

4. **Show plan** - List sorries found, get user confirmation

### Phase 2: Main Loop (Per Sorry)

1. **Understand** - `lean_goal` + read surrounding code
2. **Search first** - `lean_leansearch`, `lean_loogle`, `lean_local_search`
3. **Preflight falsification** (if goal is decidable/finite)
   - Only for: `Fin n`, `Bool`, `Option`, small `Sum` types, bound-quantified `Nat`
   - Try: `decide`, `simp with decide`, `native_decide`
   - Time-boxed: 30-60s max
   - If counterexample found → create `T_counterexample`, skip to salvage
   - If no witness quickly → continue to proof attempts
4. **Try tactics** - `rfl`, `simp`, `ring`, `linarith`, `exact?`, `aesop`
5. **Validate** - `lake build`, check sorry count decreased
6. **Commit** - `git commit -m "fill: [theorem] - [tactic]"`

### Phase 3: Review Checkpoints

**Scope enforcement:** All automatic reviews match the current focus:
- Working on single sorry → `--scope=sorry --line=N`
- Working on file → `--scope=file`
- Autoprover must never trigger `--scope=project`

When triggering review, pass current context:
```
/lean4:review [current_file] --scope=sorry --line=[current_sorry_line]
```

At configured intervals, show progress and options: continue, stop, skip, rollback.

**Stuck detection triggers:**
- Same sorry failed 2-3 times with no new approach
- Same build error repeats after 2 repair attempts
- No sorry count decrease for 10+ minutes
- LSP search returns empty twice for same goal

**When stuck detected:**
1. Run `/lean4:review <file> --scope=sorry --line=N --mode=stuck`
2. Present blockers and ask: "Apply this plan? [yes/no]"

**Stuck → Counterexample/Salvage branch:**

When stuck detected (per existing triggers), offer:
```
Try counterexample/salvage pass for this sorry? [yes/no]
```

If yes:
1. Explicit witness search (small domain or concrete instantiation)
2. If found → create `T_counterexample` lemma
3. Create `T_salvaged` (weaker version that is provable)
4. Follow user's falsification policy for original statement

## Falsification Artifacts

**Counterexample lemma (preferred):**
```lean
/-- Counterexample to the naive statement `T`. -/
theorem T_counterexample : ∃ w : α, ¬ P w := by
  refine ⟨w0, ?_⟩
  -- proof
```

**Salvage lemma:**
```lean
/-- Salvage: a weaker version of `T` that is true. -/
theorem T_salvaged (extra_assumptions...) : Q := by
  -- proof
```

**Safety:** Avoid proving `¬ P` if a `theorem T : P := by sorry` exists—unless user chose policy (2).

### Phase 4: Completion

Report filled/remaining sorries, then prompt:

```
## Session Complete

Filled: 5/8 sorries
Counterexamples: 1 (T_counterexample)
Salvaged: 1 (T_salvaged)
Commits: 7 new

Create verified checkpoint? (build + axiom check + commit)
- [yes] — run /lean4:checkpoint
- [no] — keep commits as-is
```

If yes, run `/lean4:checkpoint` to create a verified save point with axiom check.

**Golf prompt** (if `--golf=prompt` or default):
```
Run /lean4:golf on touched files?
- [yes] — golf each file (prompts per file)
- [no] — skip golfing
```

If `--golf=auto`, run golf automatically on all touched files.
If `--golf=never`, skip entirely.

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
