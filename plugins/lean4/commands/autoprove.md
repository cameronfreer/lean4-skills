---
name: autoprove
description: Autonomous multi-cycle theorem proving with hard stop rules
user_invocable: true
---

# Lean4 Autoprove

Autonomous multi-cycle theorem proving. Runs cycles automatically with hard stop conditions and structured summaries.

## Usage

```
/lean4:autoprove                        # Start autonomous session
/lean4:autoprove File.lean              # Focus on specific file
/lean4:autoprove --repair-only          # Fix build errors without filling sorries
/lean4:autoprove --max-cycles=10        # Limit total cycles
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| scope | No | all | Specific file or theorem to focus on |
| --repair-only | No | false | Fix build errors only, skip sorry-filling |
| --planning | No | on | `on` or `off` |
| --review-source | No | internal | `internal`, `external`, `both`, or `none` (see coercion below) |
| --review-every | No | checkpoint | `N` (sorries), `checkpoint`, or `never` |
| --checkpoint | No | true | Create checkpoint commits after each cycle |
| --deep | No | stuck | `never`, `stuck`, or `always` (`ask` coerced to `stuck` — see Deep Mode) |
| --deep-sorry-budget | No | 2 | Max sorries per deep invocation |
| --deep-time-budget | No | 20m | Max time per deep invocation |
| --max-deep-per-cycle | No | 1 | Max deep invocations per cycle |
| --max-consecutive-deep-cycles | No | 2 | Hard cap on consecutive cycles using deep mode |
| --batch-size | No | 2 | Sorries to attempt per cycle |
| --commit | No | auto | `auto` or `never` (`ask` coerced to `auto` — see note below) |
| --golf | No | never | `prompt`, `auto`, or `never` |
| --max-cycles | No | 20 | Hard stop: max total cycles |
| --max-total-runtime | No | 120m | Hard stop: max total runtime |
| --max-stuck-cycles | No | 3 | Hard stop: max consecutive stuck cycles |

### Review Source Coercion

Autoprove accepts all `--review-source` values for flag compatibility with `/lean4:prove`. However, autoprove **never blocks waiting for interactive input**. If the value is `external` or `both`, autoprove coerces to `internal` at startup and emits:

> ⚠ --review-source=external requires interactive handoff. Using internal review for unattended operation.

> **Future autonomous external review:** External review is currently manual-handoff only. Future versions may support autonomous external review via non-interactive CLI execution (e.g., `codex exec`) behind an explicit opt-in flag (`--external-autonomous`). Until then, unattended autoprove runs default to internal review.
>
> Requirements for autonomous external review:
> 1. Stable JSON input/output contract
> 2. Timeout + retry + cost budgets
> 3. Safe fallback to internal review on external failure
> 4. Explicit opt-in flag, not default behavior

## Startup Behavior

No questionnaire. Discover state and start immediately.

1. **Discover state** (LSP-first is **normative**, see [cycle-engine.md](../skills/lean4/references/cycle-engine.md#lsp-first-protocol)):
   - `lean_diagnostic_messages(file)` for errors/warnings
   - `lean_goal(file, line)` at each sorry
   - Up to 3 LSP search tools (~30s); record top candidates per sorry
2. If `--planning=on` (default): run planning phase — list sorries with candidates, set order, then start
3. If `--planning=off`: skip planning, start immediately. Stuck-triggered replan is still mandatory (see Stuck Definition).

## Actions

Each cycle has 6 phases (same engine as `/lean4:prove`):

### Phase 1: Plan

Discover current state via LSP-first protocol (see [cycle-engine.md](../skills/lean4/references/cycle-engine.md#lsp-first-protocol)): `lean_goal` at each sorry, up to 3 LSP search tools (~30s), record top candidates. Identify sorries, set order.

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
8. **Stage & Commit** — If `--commit=never`, skip staging and committing entirely. Otherwise, stage only files touched during this sorry (`git add <edited files>`), then commit:
   `git commit -m "fill: [theorem] - [tactic]"`

   Default `--commit=auto` — commits without prompting. Use `--commit=never` to skip all commits.

   **Note:** `--commit=ask` is accepted for flag compatibility but **coerced to `auto`** at startup:
   > ⚠ --commit=ask requires interactive confirmation. Using auto for unattended operation.

   Autoprove never blocks waiting for interactive input.

**Constraints:** Max 3 candidates per sorry, ≤80 lines diff, NO statement changes, NO cross-file refactoring (fast path).

### Phase 3: Checkpoint

If `--commit=never`, skip the checkpoint commit entirely — changes remain in the working tree.

Otherwise, if `--checkpoint` is enabled and there is a non-empty diff:
- Stage only files modified during this cycle: `git add <touched files>`
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

**Autonomous loop:** Auto-runs cycles without per-cycle user prompts. Checkpoint + review + replan at each cycle boundary ("come up for air").

## Stop Conditions

Autoprove stops when the **first** of these is satisfied:

1. **Completion** — all sorries in scope are filled
2. **Max stuck cycles** — `--max-stuck-cycles` consecutive stuck cycles (default: 3)
3. **Max cycles** — `--max-cycles` total cycles reached (default: 20)
4. **Max runtime** — `--max-total-runtime` elapsed (default: 120m)
5. **Manual user stop** — user interrupts

## Structured Summary on Stop

When autoprove stops (for any reason), emit:

```
## Autoprove Summary

**Reason stopped:** [completion | max-stuck | max-cycles | max-runtime | user-stop]

| Metric | Value |
|--------|-------|
| Sorries before | N |
| Sorries after | M |
| Cycles run | C |
| Stuck cycles | S |
| Deep invocations | D |
| Time elapsed | T |

**Handoff recommendations:**
- [If incomplete: "Run /lean4:prove for guided work on remaining N sorries"]
- [If stuck: "Review stuck blockers: file:line, file:line"]
- [If clean: "All sorries filled. Run /lean4:checkpoint to save."]
```

## Deep Mode

Bounded subroutine for stubborn sorries. Default: `stuck` (auto-escalate when stuck).

Modes: `never` | `stuck` (default, auto on stuck) | `always` (auto on any failure). Note: `ask` is coerced to `stuck` (no interactive prompting in autoprove).

Statement changes are logged but auto-skipped. Use `/lean4:prove` for interactive approval.

See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#deep-mode) for budget parameters and prove/autoprove comparison.

## Stuck Definition

A sorry is **stuck** when: same failure 2-3x, same build error 2x, no progress 10+ min, or empty LSP search 2x.

**When stuck:** auto-review → planner mode → revised plan → next cycle executes plan. On falsification flag: auto counterexample/salvage pass. Handoff must include LSP queries attempted, top candidates, and `lean_multi_attempt` outcomes.

See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#stuck-definition) for full detection logic and blocker signature computation.

## Falsification Artifacts

When a statement is disproved, create `T_counterexample` and `T_salvaged` lemmas. Avoid proving `¬ P` if original sorry exists.

See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#falsification-artifacts) for Lean code templates.

## Repair Mode

Compiler-guided repair is **escalation-only** — not the default response to a first failure. Auto-invoke only when compiler errors are the active blocker: same blocker 2x, same build error 2x, or 3+ errors in scope. Apply direct fixes first. Budgets: max 2 per error signature, max 8 total per cycle. No improvement after 2 attempts → stuck + review + replan. Interactive repair options are coerced to autonomous (auto-select next strategy).

See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#repair-mode) for full policy and [compilation-errors.md](../skills/lean4/references/compilation-errors.md) for error-specific fixes.

## Safety

Guardrailed git commands are blocked. See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#safety) for the full list.

## See Also

- `/lean4:prove` - Guided cycle-by-cycle proving
- `/lean4:checkpoint` - Manual save point
- `/lean4:review` - Quality check (read-only)
- `/lean4:golf` - Optimize proofs
- [Cycle Engine](../skills/lean4/references/cycle-engine.md) - Shared prove/autoprove mechanics
- [Examples](../skills/lean4/references/command-examples.md#autoprove)
