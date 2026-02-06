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

LSP-first discovery is **normative** (see [cycle-engine.md](../skills/lean4/references/cycle-engine.md#lsp-first-protocol)).

1. **Discover state** — `lean_diagnostic_messages(file)` for errors/warnings, `lean_goal(file, line)` at each sorry
2. **Search** — up to 3 LSP search tools (~30s): `lean_local_search`, one of `lean_leanfinder`/`lean_leansearch`, and `lean_loogle`. Record top candidates per sorry. Skip extended search for trivial goals.
3. **Show plan** — list sorries found with top candidates, proposed order, get confirmation

### Phase 2: Work (Per Sorry)

See [sorry-filling.md](../skills/lean4/references/sorry-filling.md) for detailed tactics. LSP-first is **normative** (see [cycle-engine.md](../skills/lean4/references/cycle-engine.md#lsp-first-protocol)).

1. **Understand** — refresh `lean_goal(file, line)` + read surrounding code
2. **Search** — up to 2 LSP search tools (`lean_local_search` + one of `lean_leanfinder`/`lean_leansearch`/`lean_loogle`) before script fallback (skip if trivial or prior search was conclusive)
3. **Generate candidates** — 2-3 candidate snippets from search results
4. **Test** — `lean_multi_attempt(file, line, snippets=[...])`, prefer shortest passing candidate
5. **Preflight falsification** (if goal is decidable/finite)
   - Only for: `Fin n`, `Bool`, `Option`, small `Sum` types, bound-quantified `Nat`
   - Try: `decide`, `simp with decide`, `native_decide`
   - Time-boxed: 30–60s max
   - If counterexample found → create `T_counterexample`, skip to salvage
   - If no witness quickly → continue to proof attempts
6. **Try tactics** (if no candidate passed) — `rfl`, `simp`, `ring`, `linarith`, `exact?`, `aesop`
7. **Validate** — Use LSP diagnostics (`lean_diagnostic_messages`) to check sorry count decreased. Reserve `lake build` for review checkpoints or explicit `/lean4:checkpoint`.
8. **Stage & Commit** — If `--commit=never`, skip staging and committing entirely. Otherwise, stage only files touched during this sorry (`git add <edited files>`), then:

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

Bounded subroutine for stubborn sorries. Enabled via `--deep`. Default: `never`.

Modes: `never` | `ask` (prompt first) | `stuck` (auto on stuck) | `always` (auto on any failure).

Statement changes require interactive approval. Deep allows multi-file refactoring, helper extraction, and statement generalization (with approval).

See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#deep-mode) for budget parameters and prove/autoprove comparison.

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

- `/lean4:autoprove` - Autonomous multi-cycle proving
- `/lean4:checkpoint` - Manual save point
- `/lean4:review` - Quality check (read-only)
- `/lean4:golf` - Optimize proofs
- [Cycle Engine](../skills/lean4/references/cycle-engine.md) - Shared prove/autoprove mechanics
- [Examples](../skills/lean4/references/command-examples.md#prove)
