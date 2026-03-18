---
name: autoformalize
description: Autonomous end-to-end formalization from informal sources
user_invocable: true
---

# Lean4 Autoformalize

Autonomous end-to-end formalization: extracts claims from a source, drafts Lean skeletons, and proves them — all unattended. Combines `/lean4:draft` and `/lean4:autoprove` in a single command.

## Usage

```
/lean4:autoformalize --source ./paper.pdf --claim-select=first --out=Paper.lean
/lean4:autoformalize --source ./paper.pdf --claim-select=regex:"Theorem.*" --out=Paper.lean --rigor=checked
/lean4:autoformalize --source ./notes.md --claim-select=named:"Main Lemma" --out=Lemma.lean
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| --source | **yes** | — | File path, URL, or PDF for claim extraction. |
| --claim-select | **yes** | — | `first` \| `named:"..."` \| `regex:"..."`. Queue-extraction filter applied once at startup. |
| --out | **yes** | — | Target file for formalized claims. |
| --statement-policy | no | `rewrite-generated-only` | `preserve` \| `rewrite-generated-only` \| `adjacent-drafts`. |
| --rigor | no | `sketch` | `sketch` \| `checked`. Rigor for drafted skeletons. |
| --draft-mode | no | `skeleton` | `skeleton` \| `attempt`. Passed to draft phase. |
| --draft-elab-check | no | `best-effort` | `best-effort` \| `strict`. Passed to draft phase. |
| --max-cycles | no | 20 | Hard stop: max total cycles per claim |
| --max-total-runtime | no | 120m | Hard stop: max total runtime |
| --max-stuck-cycles | no | 3 | Hard stop: max consecutive stuck cycles per claim |
| --deep | no | stuck | `never`, `stuck`, or `always` |
| --deep-sorry-budget | no | 2 | Max sorries per deep invocation |
| --deep-time-budget | no | 20m | Max time per deep invocation |
| --max-deep-per-cycle | no | 1 | Max deep invocations per cycle |
| --deep-snapshot | no | stash | V1: `stash` only |
| --deep-rollback | no | on-regression | `on-regression` \| `on-no-improvement` \| `always` \| `never` |
| --deep-scope | no | target | `target` \| `cross-file` |
| --deep-max-files | no | 2 | Max files per deep invocation |
| --deep-max-lines | no | 200 | Max added+deleted lines per deep invocation |
| --deep-regression-gate | no | strict | `strict` \| `off` |
| --commit | no | auto | `auto` \| `never` |
| --golf | no | never | `prompt` \| `auto` \| `never` |
| --review-source | no | internal | `internal` \| `none` (coerced from `external`/`both` — see autoprove) |
| --review-every | no | checkpoint | `N` (sorries) \| `checkpoint` \| `never` |

### Flag validation

- `--source` is required; error if missing.
- `--claim-select` is required; error if missing (no unattended guessing).
- `--out` is required when no existing target file is in scope; error if missing.
- `--statement-policy=preserve` is respected but warns: stuck redraft path becomes manual intervention, not automatic rewrite.

## Actions

The synthesis outer loop is the single source of truth for the algorithm. See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#synthesis-outer-loop) for the full algorithm, provenance tracking, claim queue, and file assembly contract.

Summary:
1. Extract claim queue from `--source` (filtered by `--claim-select`) at startup
2. For each claim: draft skeleton → run inner 6-phase prove cycle → on stuck, consult review router
3. On `next_action=redraft`: re-draft (check provenance + statement-policy); commit if allowed
4. Advance to next claim when sorry-free or stop rule fires

## Stop Conditions

Autoformalize stops when the **first** of these is satisfied:

1. **Queue empty** — all claims attempted (expected completion)
2. **Max stuck cycles** — `--max-stuck-cycles` consecutive stuck cycles on current claim
3. **Max cycles** — `--max-cycles` total cycles reached on current claim
4. **Max runtime** — `--max-total-runtime` elapsed
5. **Manual user stop** — user interrupts

## Structured Summary on Stop

When autoformalize stops, emit:

```
## Autoformalize Summary

**Reason stopped:** [queue-empty | max-stuck | max-cycles | max-runtime | user-stop]

| Metric | Value |
|--------|-------|
| Claims attempted | N/M |
| Sorries before | 0 |
| Sorries after | S |
| Cycles run | C |
| Stuck cycles | K |
| Deep invocations | D |
| Time elapsed | T |
| Drafts | F (R redrafted) |

**Handoff recommendations:**
- [If incomplete: "Run /lean4:formalize for guided work on remaining claims"]
- [If stuck: "Review stuck blockers: file:line, file:line"]
- [If clean: "All sorries filled. Run /lean4:checkpoint to save."]
- [If claims remaining: "N claims remaining in queue. Re-run with same --source and --out to continue."]
```

## Safety

- **Autonomous operation.** Never blocks waiting for interactive input.
- **Guardrailed git commands are blocked.** See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#safety) for the full list.
- **Header fence.** Proof engines (inner cycle) never modify declaration headers. Statement changes are handled by the synthesis outer loop's redraft path, not by deep mode.
- **All `guardrails.sh` rules apply.**

## See Also

- `/lean4:draft` — Skeleton-only drafting (standalone)
- `/lean4:formalize` — Interactive synthesis (human-in-the-loop)
- `/lean4:autoprove` — Autonomous proving (no drafting)
- [Cycle Engine — Synthesis Outer Loop](../skills/lean4/references/cycle-engine.md#synthesis-outer-loop)
- [Examples](../skills/lean4/references/command-examples.md#autoformalize)
