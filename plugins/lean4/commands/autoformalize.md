---
name: autoformalize
description: Autonomous end-to-end formalization from informal sources
user_invocable: true
argument-hint: '--source=PATH --claim-select=POLICY --out=PATH [--max-cycles=N] [--commit=auto|checkpoint]'
---

# Lean4 Autoformalize

Autonomous end-to-end formalization: extracts claims from a source, drafts Lean skeletons, and proves them — all unattended. Combines `/lean4:draft` and `/lean4:autoprove` in a single command.

## Usage

```
/lean4:autoformalize --source ./paper.pdf --claim-select=first --out=Paper.lean
/lean4:autoformalize --source ./paper.pdf --claim-select=regex:"Theorem.*" --out=Paper.lean --rigor=checked
/lean4:autoformalize --source ./notes.md --claim-select=named:"Main Lemma" --out=Lemma.lean
```

## Invocation Contract

Interpret this command's inputs per the
[Command Invocation Contract](../skills/lean4/references/command-invocation.md).

**Primary path (hook-validated):** If a `validated-invocation` block for this
command appears in context, treat it as the authoritative interpretation of
parser-decidable inputs and do **not** re-parse the raw invocation text for
those inputs. Start by reading all parser-decided fields from the block. Emit
the final **Resolved Inputs** summary from the block values.
See [Validated Invocation Block](../skills/lean4/references/command-invocation.md#validated-invocation-block-host-provided).

**Fallback path (other hosts):** If no `validated-invocation` block is present,
parse the raw invocation text against this command's input table before
extracting claims or drafting anything.

Startup requirements:

1. Emit a **Resolved Inputs** block with explicit values, defaults, coercions,
   ignored flags, and startup validation errors.
2. Refuse to start on startup validation errors.
3. Call `bash "$LEAN4_SCRIPTS/cycle_tracker.sh" init` with resolved numeric
   values for `--max-cycles`, `--max-stuck-cycles`, `--max-total-runtime`,
   and `--max-deep-per-cycle`.
   A failed init (exit 2) is a startup validation error — do not proceed.
4. The state file is the single source of truth for session counters.
   Read counters from `tick`/`status` output, not from conversational memory.
5. **Per-claim lifecycle:** `--max-cycles` and `--max-stuck-cycles` are per-claim;
   `--max-total-runtime` is per-session. Before each claim, call `start-claim`.
   After each claim completes or stops (before the next), call `reset-claim`.
   The final claim does not need `reset-claim` — totals are accumulated live.
   See [Claim Boundary Protocol](../skills/lean4/references/cycle-engine.md#claim-boundary-protocol-autoformalize).

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
| --max-cycles | no | 20 | Session stop budget: max total cycles per claim |
| --max-total-runtime | no | 120m | Best-effort wall-clock session budget |
| --max-stuck-cycles | no | 3 | Session stop budget: max consecutive stuck cycles per claim |
| --deep | no | stuck | `never`, `stuck`, or `always` |
| --deep-sorry-budget | no | 2 | Max sorries per deep invocation |
| --deep-time-budget | no | 20m | Advisory: scopes deep-mode subagent work. Not tracked or enforced by session tracker. |
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

Autoformalize checks stop budgets at cycle boundaries via `$LEAN4_SCRIPTS/cycle_tracker.sh tick --stuck=yes|no`.
Limits are checked at cycle boundaries only — a long-running tool call within a cycle
will not be interrupted.

Autoformalize stops when the **first** of these is satisfied:

1. **Queue empty** — all claims attempted (expected completion)
2. **Max stuck cycles** — `--max-stuck-cycles` consecutive stuck cycles on current claim. Session-enforced via `$LEAN4_SCRIPTS/cycle_tracker.sh`.
3. **Max cycles** — `--max-cycles` total cycles reached on current claim. Session-enforced via `$LEAN4_SCRIPTS/cycle_tracker.sh`.
4. **Max runtime** — best-effort wall-clock budget reached (`--max-total-runtime`). Checked at cycle boundaries and deep preflight.
5. **Manual user stop** — user interrupts

See [Session Tracking](../skills/lean4/references/cycle-engine.md#session-tracking) for the cycle boundary protocol and enforcement levels.

## Structured Summary on Stop

When autoformalize stops, emit:

```
## Autoformalize Summary

**Reason stopped:** [queue-empty | max-stuck | max-cycles | max-runtime | user-stop]

| Metric | Value | Source |
|--------|-------|--------|
| Claims attempted | N/M | `claims_attempted` from `status` (includes in-progress claim) |
| Sorries before | 0 | |
| Sorries after | S | |
| Cycles run | C | `cycles_total` from `status` (session total across all claims) |
| Stuck cycles | K | `stuck_cycles_total` from `status` (session total) |
| Deep invocations | D | `deep_total` from `status` (session total) |
| Time elapsed | T | `elapsed_display` from `status` |
| Drafts | F (R redrafted) | |

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
- **Line width.** Follow mathlib 100-char line width — do not wrap lines at 80 when they fit within 100.

## See Also

- `/lean4:draft` — Skeleton-only drafting (standalone)
- `/lean4:formalize` — Interactive synthesis (human-in-the-loop)
- `/lean4:autoprove` — Autonomous proving (no drafting)
- [Cycle Engine — Synthesis Outer Loop](../skills/lean4/references/cycle-engine.md#synthesis-outer-loop)
- [Examples](../skills/lean4/references/command-examples.md#autoformalize)
