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
| --deep-snapshot | No | stash | V1: `stash` only |
| --deep-rollback | No | on-regression | `on-regression`, `on-no-improvement`, `always`, or `never` |
| --deep-scope | No | target | `target` or `cross-file` |
| --deep-max-files | No | 1 | Max files per deep invocation |
| --deep-max-lines | No | 120 | Max added+deleted lines per deep invocation |
| --deep-regression-gate | No | strict | `strict` (auto-abort on regression) or `off` |
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

Each cycle has 6 phases — see [cycle-engine.md](../skills/lean4/references/cycle-engine.md) for shared mechanics.

### Phase 1: Plan

See [cycle-engine: LSP-First Protocol](../skills/lean4/references/cycle-engine.md#lsp-first-protocol). Discover sorries via LSP, search with up to 3 tools (~30s), show plan and get confirmation.

### Phase 2: Work (Per Sorry)

See [sorry-filling.md](../skills/lean4/references/sorry-filling.md) and [cycle-engine: LSP-First Protocol](../skills/lean4/references/cycle-engine.md#lsp-first-protocol).

1. Refresh goal → search → generate 2-3 candidates → test via `lean_multi_attempt`
2. Preflight falsification for decidable/finite goals (30-60s max)
3. Tactic cascade if no candidate passed
4. Validate via `lean_diagnostic_messages`
5. Stage & commit (see below)

**Staging rule:** If `--commit=never`, skip staging and committing entirely. Otherwise, stage only the files touched by this fill (`git add <edited files>`) — never `git add -A` or broad patterns.

**Commit behavior** (unique to prove):
Show diff and ask before each commit when `--commit=ask` (default):
```
Commit this? [yes / yes-all / no / never]
```
- **yes** — commit, prompt again next time
- **yes-all** — switch to `auto` for rest of session
- **no** — unstage (`git reset HEAD <files>`), skip this commit
- **never** — unstage, skip all remaining commits for session

**Constraints:** Max 3 candidates per sorry, ≤80 lines diff, NO statement changes, NO cross-file refactoring (fast path). Declaration headers are immutable — if deep mode suggests a header change, it must stop and recommend `/lean4:formalize`.

### Phase 3: Checkpoint

See [cycle-engine: Checkpoint Logic](../skills/lean4/references/cycle-engine.md#checkpoint-logic). Stage only files from **accepted** fills; exclude declined fills and rolled-back deep invocations.

### Phase 4: Review

See [cycle-engine: Review Phase](../skills/lean4/references/cycle-engine.md#review-phase). Runs at configured `--review-every` intervals.

### Phase 5: Replan

See [cycle-engine: Replan Phase](../skills/lean4/references/cycle-engine.md#replan-phase).

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

Bounded subroutine for stubborn sorries. Enabled via `--deep`. Default: `never`.

Modes: `never` | `ask` (prompt first) | `stuck` (auto on stuck) | `always` (auto on any failure).

Statement changes are NOT permitted. Declaration headers are immutable (header fence). If deep concludes the statement is wrong, it emits `next_action = redraft` but does not rewrite. Suggest `/lean4:formalize` for statement work. Deep allows multi-file refactoring and helper extraction within the header fence.

**Safety:** Deep creates a path-scoped pre-deep snapshot (`--deep-snapshot`), enforces scope/diff budgets (`--deep-scope`, `--deep-max-files`, `--deep-max-lines`), and auto-rolls back on regression (`--deep-regression-gate`). Rollback marks the sorry as stuck with reason.

**Validation:** Deep-safety flags are validated at startup; invalid values produce descriptive errors.

See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#deep-mode) for full semantics, definitions, and prove/autoprove comparison.

### Header Fence

Declaration headers (everything from `theorem`/`def`/`lemma` through `:= by`) are snapshotted at deep entry. At each checkpoint, the engine compares headers against the snapshot. Any header change triggers immediate rollback and marks the sorry as stuck with `"deep: header fence — declaration header modified"`. The prove phase itself never modifies headers; statement changes require `/lean4:formalize`.

## Stuck Definition

A sorry is **stuck** when: same failure 2-3x, same build error 2x, no progress 10+ min, or empty LSP search 2x.

**When stuck:** review → fresh plan → present for approval ([yes / no / skip]). On decline: offer counterexample/salvage pass. Handoff must include LSP queries attempted, top candidates, and `lean_multi_attempt` outcomes.

See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#stuck-definition) for full detection logic and blocker signature computation.

## Falsification Artifacts

When a statement is disproved, create `T_counterexample` and `T_salvaged` lemmas. Avoid proving `¬ P` unless user chose negation policy.

See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#falsification-artifacts) for Lean code templates.

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

Compiler-guided repair is **escalation-only** — not the default response to a first failure. Auto-invoke only when compiler errors are the active blocker: same blocker 2x, same build error 2x, or 3+ errors in scope. Apply direct fixes first for straightforward errors. Budgets: max 2 per error signature, max 6 total per cycle. No improvement after 2 attempts → stuck + review + replan.

See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#repair-mode) for full policy and [compilation-errors.md](../skills/lean4/references/compilation-errors.md) for error-specific fixes.

## Safety

Guardrailed git commands are blocked. See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#safety) for the full list.

## See Also

- `/lean4:draft` - Draft Lean declaration skeletons
- `/lean4:autoformalize` - Autonomous end-to-end formalization
- `/lean4:autoprove` - Autonomous multi-cycle proving
- `/lean4:checkpoint` - Manual save point
- `/lean4:review` - Quality check (read-only)
- `/lean4:refactor` - Strategy-level proof simplification
- `/lean4:golf` - Optimize proofs
- [Cycle Engine](../skills/lean4/references/cycle-engine.md) - Shared prove/autoprove mechanics
- [Examples](../skills/lean4/references/command-examples.md#prove)
