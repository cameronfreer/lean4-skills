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
| --deep-snapshot | No | stash | V1: `stash` only |
| --deep-rollback | No | on-regression | `on-regression`, `on-no-improvement`, `always`, or `never` (see coercion below) |
| --deep-scope | No | target | `target` or `cross-file` |
| --deep-max-files | No | 2 | Max files per deep invocation |
| --deep-max-lines | No | 200 | Max added+deleted lines per deep invocation |
| --deep-regression-gate | No | strict | `strict` or `off` (see coercion below) |
| --batch-size | No | 2 | Sorries to attempt per cycle |
| --commit | No | auto | `auto` or `never` (`ask` coerced to `auto` — see note below) |
| --golf | No | never | `prompt`, `auto`, or `never` |
| --max-cycles | No | 20 | Hard stop: max total cycles |
| --max-total-runtime | No | 120m | Hard stop: max total runtime |
| --max-stuck-cycles | No | 3 | Hard stop: max consecutive stuck cycles |
| --formalize | No | never | `never` \| `bootstrap` \| `restage` \| `auto`. See Formalize Outer Loop. |
| --source | No | — | File path, URL, or PDF for claim extraction. Required when `--formalize=bootstrap\|auto`. |
| --claim-select | No | — | `first` \| `named:"..."` \| `regex:"..."`. Required for unattended `--source`. |
| --claim-batch-size | No | 1 | Claims to formalize per outer loop iteration |
| --formalize-rigor | No | sketch | `sketch` \| `checked`. Rigor for formalize skeleton. |
| --statement-policy | No | preserve | `preserve` \| `rewrite-generated-only` \| `adjacent-drafts`. See cycle-engine. |
| --formalize-out | No | — | Target file for formalized claims. Required if no existing target in scope. |

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

### Formalize Flag Validation

- `--formalize=bootstrap` requires `--source`; error if missing.
- `--formalize=auto` requires `--source`; error if missing.
- `--formalize=restage` does NOT require `--source` — operates on existing scope with restage enabled on stuck.
- `--formalize=never` ignores `--source` (warn if provided).

## Startup Behavior

No questionnaire. Discover state and start immediately.

1. **Discover state** (LSP-first is **normative**, see [cycle-engine.md](../skills/lean4/references/cycle-engine.md#lsp-first-protocol)):
   - `lean_diagnostic_messages(file)` for errors/warnings
   - `lean_goal(file, line)` at each sorry
   - Up to 3 LSP search tools (~30s); record top candidates per sorry
2. If `--planning=on` (default): run planning phase — list sorries with candidates, set order, then start
3. If `--planning=off`: skip planning, start immediately. Stuck-triggered replan is still mandatory (see Stuck Definition).

## Actions

Each cycle has 6 phases — see [cycle-engine.md](../skills/lean4/references/cycle-engine.md) for shared mechanics.

### Phase 1: Plan

See [cycle-engine: LSP-First Protocol](../skills/lean4/references/cycle-engine.md#lsp-first-protocol). Discover sorries via LSP, search with up to 3 tools (~30s), identify sorries, set order.

### Phase 2: Work (Per Sorry)

See [sorry-filling.md](../skills/lean4/references/sorry-filling.md) and [cycle-engine: LSP-First Protocol](../skills/lean4/references/cycle-engine.md#lsp-first-protocol).

1. Refresh goal → search → generate 2-3 candidates → test via `lean_multi_attempt`
2. Preflight falsification for decidable/finite goals (30-60s max)
3. Tactic cascade if no candidate passed
4. Validate via `lean_diagnostic_messages`
5. Stage & commit

**Staging rule:** If `--commit=never`, skip staging and committing entirely. Otherwise, stage only the files touched by this fill (`git add <edited files>`) — never `git add -A` or broad patterns. Commit: `git commit -m "fill: [theorem] - [tactic]"`.

**Commit behavior** (unique to autoprove):
Default `--commit=auto` — commits without prompting. `--commit=ask` is coerced to `auto` at startup:
> ⚠ --commit=ask requires interactive confirmation. Using auto for unattended operation.

Autoprove never blocks waiting for interactive input.

**Constraints:** Max 3 candidates per sorry, ≤80 lines diff, NO statement changes (inner cycle; see Formalize Outer Loop for `--formalize` modes), NO cross-file refactoring (fast path).

### Phase 3: Checkpoint

See [cycle-engine: Checkpoint Logic](../skills/lean4/references/cycle-engine.md#checkpoint-logic). Stage only files from successful work; exclude rolled-back deep invocations.

### Phase 4: Review

See [cycle-engine: Review Phase](../skills/lean4/references/cycle-engine.md#review-phase). Runs at configured `--review-every` intervals.

### Phase 5: Replan

See [cycle-engine: Replan Phase](../skills/lean4/references/cycle-engine.md#replan-phase).

### Phase 6: Continue / Stop

**Autonomous loop:** Auto-runs cycles without per-cycle user prompts. Checkpoint + review + replan at each cycle boundary ("come up for air").

## Formalize Outer Loop

When `--formalize` is not `never`, autoprove wraps the inner 6-phase cycle with source-backed statement acquisition and review-driven routing.

| Mode | Behavior |
|------|----------|
| `never` (default) | No outer loop. Identical to pre-change behavior. |
| `bootstrap` | Extract claims from `--source`, formalize each, then prove. No restage on stuck. |
| `restage` | No claim queue. Run inner cycle on existing scope; on stuck, re-formalize if `next_action=formalize-restage`. |
| `auto` | Full loop: extract + formalize + prove + restage on stuck. |

The inner 6-phase cycle is unchanged. The outer loop reads the stuck-mode `next_action` field from review as its routing gate. See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#formalize-outer-loop) for the full algorithm, provenance tracking, claim queue, and file assembly contract.

## Stop Conditions

Autoprove stops when the **first** of these is satisfied:

1. **Completion** — all sorries in scope are filled
2. **Max stuck cycles** — `--max-stuck-cycles` consecutive stuck cycles (default: 3)
3. **Max cycles** — `--max-cycles` total cycles reached (default: 20)
4. **Max runtime** — `--max-total-runtime` elapsed (default: 120m)
5. **Manual user stop** — user interrupts
6. **Queue empty** — all claims attempted (outer loop only, `--formalize=bootstrap|auto`)

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
| Formalizations | F |

**Handoff recommendations:**
- [If incomplete: "Run /lean4:prove for guided work on remaining N sorries"]
- [If stuck: "Review stuck blockers: file:line, file:line"]
- [If clean: "All sorries filled. Run /lean4:checkpoint to save."]
- [If claims remaining: "N claims remaining in queue. Re-run with same --source to continue."]
```

## Deep Mode

Bounded subroutine for stubborn sorries. Default: `stuck` (auto-escalate when stuck).

Modes: `never` | `stuck` (default, auto on stuck) | `always` (auto on any failure). Note: `ask` is coerced to `stuck` (no interactive prompting in autoprove).

Statement changes are logged but auto-skipped. When `--formalize` is active, statement work is handled by the outer loop's formalize-restage path, not by deep mode. Use `/lean4:prove` for interactive approval.

**Safety:** Deep creates a path-scoped pre-deep snapshot, enforces scope/diff budgets, and auto-rolls back on regression. Rollback marks the sorry as stuck with reason.

**Deep safety coercions** (validated and applied at startup with warnings):
- `--deep-rollback=never` → coerced to `on-regression`
- `--deep-regression-gate=off` → coerced to `strict`

See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#deep-mode) for full semantics, definitions, and prove/autoprove comparison.

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

- `/lean4:formalize` - Turn informal math into Lean statements
- `/lean4:prove` - Guided cycle-by-cycle proving
- `/lean4:checkpoint` - Manual save point
- `/lean4:review` - Quality check (read-only)
- `/lean4:golf` - Optimize proofs
- [Cycle Engine](../skills/lean4/references/cycle-engine.md) - Shared prove/autoprove mechanics
- [Examples](../skills/lean4/references/command-examples.md#autoprove)
