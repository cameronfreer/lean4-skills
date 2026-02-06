---
name: prove
description: Guided cycle-by-cycle theorem proving with explicit checkpoints
user_invocable: true
---

# Lean4 Prove

Guided, cycle-by-cycle theorem proving. Asks before each cycle, supports deep escalation, and checkpoints your progress.

## Usage

```
/lean4:prove                         # Start guided session
/lean4:prove File.lean               # Focus on specific file
/lean4:prove --repair-only           # Fix build errors without filling sorries
/lean4:prove --deep=stuck            # Enable deep escalation when stuck
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| scope | No | all | Specific file or theorem to focus on |
| --repair-only | No | false | Fix build errors only, skip sorry-filling |
| --planning | No | ask | `ask` (prompt at startup), `on`, or `off` |
| --review-source | No | internal | `internal`, `external`, `both`, or `none` |
| --review-every | No | checkpoint | `N` (sorries), `checkpoint`, or `never` |
| --checkpoint | No | true | Create checkpoint commits after each cycle |
| --deep | No | never | `never`, `ask`, `stuck`, or `always` |
| --deep-sorry-budget | No | 1 | Max sorries per deep invocation |
| --deep-time-budget | No | 10m | Max time per deep invocation |
| --max-deep-per-cycle | No | 1 | Max deep invocations per cycle |
| --batch-size | No | 1 | Sorries to attempt per cycle |
| --commit | No | ask | `ask` (prompt before each commit), `auto`, or `never` |
| --golf | No | prompt | `prompt`, `auto`, or `never` |

## Startup Behavior

If key preferences are not passed via flags, ask once at startup:

**Planning preference:**
> Start with a planning phase? (Recommended for new sessions)
> 1) Yes — discover state, set scope, show plan (recommended)
> 2) No — skip planning, start immediately

**Review source:**
> How should reviews be conducted?
> 1) Internal — planner mode reviews and can apply fixes (recommended)
> 2) External — interactive handoff for advice only
> 3) Both — internal first, then external advice
> 4) None — no automatic reviews

If `--planning=off`, skip initial planning but stuck-triggered replan is still mandatory (see Stuck Definition).

## Actions

Each cycle has 6 phases:

### Phase 1: Plan

1. **Discover state** via LSP or fallback:
   ```
   lean_diagnostic_messages(file)    # errors/warnings
   lean_goal(file, line)             # at each sorry
   ```
2. **Show plan** — list sorries found, proposed order, get confirmation

### Phase 2: Work (Per Sorry)

See [sorry-filling.md](../skills/lean4/references/sorry-filling.md) for detailed tactics.

1. **Understand** — `lean_goal` + read surrounding code
2. **Search first** — `lean_leansearch`, `lean_loogle`, `lean_local_search`
3. **Preflight falsification** (if goal is decidable/finite)
   - Only for: `Fin n`, `Bool`, `Option`, small `Sum` types, bound-quantified `Nat`
   - Try: `decide`, `simp with decide`, `native_decide`
   - Time-boxed: 30–60s max
   - If counterexample found → create `T_counterexample`, skip to salvage
   - If no witness quickly → continue to proof attempts
4. **Try tactics** — `rfl`, `simp`, `ring`, `linarith`, `exact?`, `aesop`
5. **Validate** — Use LSP diagnostics (`lean_diagnostic_messages`) to check sorry count decreased. Reserve `lake build` for review checkpoints or explicit `/lean4:checkpoint`.
6. **Stage & Commit** — If `--commit=never`, skip staging and committing entirely. Otherwise, stage only files touched during this sorry (`git add <edited files>`), then:

   **Commit prompt** (when `--commit=ask`, the default):
   Show the diff and ask before each commit:
   ```
   About to commit: fill: trivial_lemma - exact Nat.zero_le
   Files: Helpers.lean
   Diff: +1 -1 line

   Commit this? [yes / yes-all / no / never]
   ```
   - **yes** — commit this fill, prompt again for the next one
   - **yes-all** — commit this and all future fills without prompting (switches to `auto` for rest of session)
   - **no** — unstage (`git reset HEAD <files>`), skip this fill's commit, prompt again for the next one
   - **never** — unstage (`git reset HEAD <files>`), skip all commits for rest of session (switches to `never` mode)

   On **no** or **never**, always unstage so declined changes are not carried into a later commit.

   If `--commit=auto`, commit without prompting.

**Constraints:** Max 3 candidates per sorry, ≤80 lines diff, NO statement changes, NO cross-file refactoring (fast path).

### Phase 3: Checkpoint

If `--commit=never` (or the user chose **never** at the commit prompt), skip the checkpoint commit entirely — changes remain in the working tree.

Otherwise, if `--checkpoint` is enabled and there is a non-empty diff:
- Stage only files from **accepted** fills that were not already committed individually: `git add <accepted files>`
- Do **not** re-stage files from declined fills — those stay in the working tree only
- Commit: `git commit -m "checkpoint(lean4): [summary]"`

If no files changed during this cycle, emit:
> No changes this cycle — skipping checkpoint

Do NOT create an empty commit. Checkpoint requires a non-empty diff.

### Phase 4: Review

At configured intervals (`--review-every`), run review matching current scope:
- Working on single sorry → `--scope=sorry --line=N`
- Working on file → `--scope=file`
- Never trigger `--scope=project` automatically

### Phase 5: Replan

After review → enter planner mode → produce/update action plan. Work phase follows that plan next cycle.

### Phase 6: Continue / Stop

Prompt the user after each full cycle:

```
Cycle complete. Filled N/M sorries this cycle.
- [continue] — run next cycle
- [stop] — save progress and exit
- [adjust] — change flags for next cycle
```

Never auto-start the next cycle. Always ask.

## Deep Mode

Bounded subroutine for stubborn sorries. Enabled via `--deep`.

| Mode | Behavior |
|------|----------|
| `never` | No deep escalation (default) |
| `ask` | Prompt before each deep invocation |
| `stuck` | Auto-escalate only when stuck |
| `always` | Auto-escalate on any fast-path failure |

**Budget enforcement:**
- `--deep-sorry-budget` — max sorries per deep invocation (default: 1)
- `--deep-time-budget` — max time per deep invocation (default: 10m)
- `--max-deep-per-cycle` — max deep invocations per cycle (default: 1)

If deep budget is exhausted with no progress → stuck.

**Statement changes require approval:**
```
## Statement Change Required
Current: theorem foo (x : ℕ) : P x
Proposed: theorem foo (x : ℤ) : P x
Approve? (yes / no / suggest alternative)
```

Deep mode allows: multi-file refactoring, helper extraction, statement generalization (with approval).

## Stuck Definition

A sorry or repair target is **stuck** when any of these hold:

1. Same sorry failed 2–3 times with no new approach
2. Same build error repeats after 2 repair attempts
3. No sorry count decrease for 10+ minutes
4. LSP search returns empty twice for same goal

**Same blocker** is computed as `(file, line, primary_error_code_or_text_hash)`. Two consecutive iterations producing the same blocker signature = same blocker.

**When stuck detected:**
1. Run `/lean4:review <file> --scope=sorry --line=N --mode=stuck`
2. Summarize findings and create fresh plan (3–6 steps)
3. Present for approval:
   ```
   Review complete. Proposed plan:
   1. [Step from review findings]
   2. ...
   Proceed with this plan? [yes / no / skip]
   ```
4. On approval: continue with new plan
5. On decline/skip: offer counterexample/salvage pass, then move to next sorry

**Important:** Stuck-triggered replan is mandatory even if `--planning=off`. It is a safety mechanism, not optional planning.

### Stuck → Counterexample / Salvage

If user declines the stuck plan, or review includes a falsification flag:
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

**Safety:** Avoid proving `¬ P` if a `theorem T : P := by sorry` exists — unless user explicitly chose negation policy.

## Completion

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

**Golf prompt** (if `--golf=prompt` or default):
```
Run /lean4:golf on touched files?
- [yes] — golf each file
- [no] — skip golfing
```

If `--golf=auto`, run golf automatically. If `--golf=never`, skip entirely.

## Repair Mode

When build fails, shift to repair workflow:

| Error | Typical Fix |
|-------|-------------|
| `type mismatch` | Add coercion, `convert`, fix argument |
| `unknown identifier` | Search mathlib, add import |
| `failed to synthesize` | Add `haveI`/`letI` |
| `timeout` | Narrow `simp`, add explicit types |

For detailed fixes, see [compilation-errors.md](../skills/lean4/references/compilation-errors.md). For persistent issues, [capture a build log](../skills/lean4/references/compilation-errors.md#build-log-capture) for inspection.

## Safety

- `git push` blocked (review first)
- `git commit --amend` blocked (preserve history)
- `gh pr create` blocked (review first)
- `git checkout --`/`git restore`/`git reset --hard`/`git clean` blocked (use `git stash push -u` or revert commit)

## See Also

- `/lean4:autoprove` - Autonomous multi-cycle proving
- `/lean4:checkpoint` - Manual save point
- `/lean4:review` - Quality check (read-only)
- `/lean4:golf` - Optimize proofs
- [Examples](../skills/lean4/references/command-examples.md#prove)
