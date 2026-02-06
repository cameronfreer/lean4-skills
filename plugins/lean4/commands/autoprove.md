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
| --deep | No | stuck | `never`, `stuck`, or `always` |
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

1. **Discover state** via LSP or fallback:
   ```
   lean_diagnostic_messages(file)    # errors/warnings
   lean_goal(file, line)             # at each sorry
   ```
2. If `--planning=on` (default): run planning phase — list sorries, set order, then start
3. If `--planning=off`: skip planning, start immediately. Stuck-triggered replan is still mandatory (see Stuck Definition).

## Actions

Each cycle has 6 phases (same engine as `/lean4:prove`):

### Phase 1: Plan

Discover current state, identify sorries, set order.

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
6. **Stage & Commit** — If `--commit=never`, skip staging and committing entirely. Otherwise, stage only files touched during this sorry (`git add <edited files>`), then commit:
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

| Mode | Behavior |
|------|----------|
| `never` | No deep escalation |
| `stuck` | Auto-escalate only when stuck (default) |
| `always` | Auto-escalate on any fast-path failure |

**Budget enforcement:**
- `--deep-sorry-budget` — max sorries per deep invocation (default: 2)
- `--deep-time-budget` — max time per deep invocation (default: 20m)
- `--max-deep-per-cycle` — max deep invocations per cycle (default: 1)
- `--max-consecutive-deep-cycles` — hard cap on consecutive cycles using deep mode (default: 2)

If deep budget is exhausted with no progress → stuck.

**Statement changes:** In autoprove, statement changes are logged but auto-skipped (no interactive approval). Use `/lean4:prove` for interactive approval of statement changes.

## Stuck Definition

A sorry or repair target is **stuck** when any of these hold:

1. Same sorry failed 2–3 times with no new approach
2. Same build error repeats after 2 repair attempts
3. No sorry count decrease for 10+ minutes
4. LSP search returns empty twice for same goal

**Same blocker** is computed as `(file, line, primary_error_code_or_text_hash)`. Two consecutive iterations producing the same blocker signature = same blocker.

**When stuck detected:**
1. Run `/lean4:review <file> --scope=sorry --line=N --mode=stuck`
2. Enter planner mode → revised plan
3. Next cycle executes the revised plan

**Important:** Stuck-triggered replan is mandatory even if `--planning=off`. It is a safety mechanism, not optional planning.

### Stuck → Counterexample / Salvage

When stuck and review includes a falsification flag:
1. Explicit witness search (small domain or concrete instantiation)
2. If found → create `T_counterexample` lemma
3. Create `T_salvaged` (weaker version that is provable)
4. Follow default falsification policy (counterexample + salvage only)

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

**Safety:** Avoid proving `¬ P` if a `theorem T : P := by sorry` exists.

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

- `/lean4:prove` - Guided cycle-by-cycle proving
- `/lean4:checkpoint` - Manual save point
- `/lean4:review` - Quality check (read-only)
- `/lean4:golf` - Optimize proofs
- [Examples](../skills/lean4/references/command-examples.md#autoprove)
