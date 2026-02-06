# Cycle Engine Reference

> Shared logic for `/lean4:prove` and `/lean4:autoprove`.

Both commands share a six-phase cycle engine. This reference documents the shared mechanics; command-specific behavior is noted inline.

## Six-Phase Cycle

```
Plan → Work → Checkpoint → Review → Replan → Continue/Stop
```

1. **Plan** — Discover state via LSP, identify sorries, set order
2. **Work** — Fill sorries using search + tactics (see [sorry-filling.md](sorry-filling.md))
3. **Checkpoint** — Stage and commit progress
4. **Review** — Quality check at configured intervals
5. **Replan** — Enter planner mode, produce/update action plan
6. **Continue/Stop** — prove: prompt user; autoprove: auto-continue or stop

## Review Phase

At configured intervals (`--review-every`), run review matching current scope:
- Working on single sorry → `--scope=sorry --line=N`
- Working on file → `--scope=file`
- Never trigger `--scope=project` automatically

Reviews act as gates: review → replan → approval → continue.

## Replan Phase

After review → enter planner mode → produce/update action plan. Work phase follows that plan next cycle.

## Stuck Definition

A sorry or repair target is **stuck** when any of these hold:

1. Same sorry failed 2-3 times with no new approach
2. Same build error repeats after 2 repair attempts
3. No sorry count decrease for 10+ minutes
4. LSP search returns empty twice for same goal

**Same blocker** is computed as `(file, line, primary_error_code_or_text_hash)`. Two consecutive iterations producing the same blocker signature = same blocker.

**When stuck detected:**

| Step | prove | autoprove |
|------|-------|-----------|
| 1. Review | `/lean4:review <file> --scope=sorry --line=N --mode=stuck` | Same |
| 2. Replan | Summarize findings, create fresh plan (3-6 steps) | Enter planner mode → revised plan |
| 3. Approval | Present for user approval: `[yes / no / skip]` | Auto-approve, next cycle executes plan |
| 4. On decline | Offer counterexample/salvage pass | N/A (autonomous) |

**Important:** Stuck-triggered replan is mandatory even if `--planning=off`. It is a safety mechanism, not optional planning.

### Stuck → Counterexample / Salvage

When stuck and user declines the plan (prove) or review flags falsification (autoprove):

1. Explicit witness search (small domain or concrete instantiation)
2. If found → create `T_counterexample` lemma (see [Falsification Artifacts](#falsification-artifacts))
3. Create `T_salvaged` (weaker version that is provable)
4. **prove:** Follow user's falsification policy for original statement
5. **autoprove:** Follow default falsification policy (counterexample + salvage only)

## Deep Mode

Bounded subroutine for stubborn sorries. Allows multi-file refactoring, helper extraction, and statement generalization.

**Budget enforcement:**
- `--deep-sorry-budget` — max sorries per deep invocation
- `--deep-time-budget` — max time per deep invocation
- `--max-deep-per-cycle` — max deep invocations per cycle (default: 1)

If deep budget is exhausted with no progress → stuck.

| Feature | prove | autoprove |
|---------|-------|-----------|
| `--deep=ask` | Prompt before each deep invocation | Not supported (coerced to `stuck`) |
| `--deep=stuck` | Auto-escalate when stuck | Auto-escalate when stuck (default) |
| `--deep=always` | Auto-escalate on any failure | Auto-escalate on any failure |
| `--deep=never` | No deep (default) | No deep |
| `--deep-sorry-budget` | 1 (default) | 2 (default) |
| `--deep-time-budget` | 10m (default) | 20m (default) |
| `--max-deep-per-cycle` | 1 | 1 |
| `--max-consecutive-deep-cycles` | N/A | 2 (autoprove-only) |
| Statement changes | Interactive approval prompt | Logged but auto-skipped |
| `--commit=ask` | Per-commit prompt (yes/yes-all/no/never) | Coerced to `auto` at startup |

## Checkpoint Logic

If `--commit=never`, skip the checkpoint commit entirely — changes remain in the working tree.

Otherwise, if `--checkpoint` is enabled and there is a non-empty diff:
- **prove:** Stage only files from **accepted** fills (exclude declined fills)
- **autoprove:** Stage all files modified during this cycle
- Commit: `git commit -m "checkpoint(lean4): [summary]"`

If no files changed during this cycle, emit:
> No changes this cycle — skipping checkpoint

Do NOT create an empty commit. Checkpoint requires a non-empty diff.

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

## Repair Mode

When build fails, shift to repair workflow:

| Error | Typical Fix |
|-------|-------------|
| `type mismatch` | Add coercion, `convert`, fix argument |
| `unknown identifier` | Search mathlib, add import |
| `failed to synthesize` | Add `haveI`/`letI` |
| `timeout` | Narrow `simp`, add explicit types |

For detailed fixes, see [compilation-errors.md](compilation-errors.md). For persistent issues, [capture a build log](compilation-errors.md#build-log-capture) for inspection.

## Safety

Blocked git commands (both prove and autoprove):
- `git push` (review first)
- `git commit --amend` (preserve history)
- `gh pr create` (review first)
- `git checkout --`/`git restore`/`git reset --hard`/`git clean` (use `git stash push -u` or revert commit)

## See Also

- [sorry-filling.md](sorry-filling.md) — Sorry elimination tactics
- [compilation-errors.md](compilation-errors.md) — Error-by-error repair guidance
- [command-examples.md](command-examples.md) — Usage examples
