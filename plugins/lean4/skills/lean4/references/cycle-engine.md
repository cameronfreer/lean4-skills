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

## LSP-First Protocol

LSP tools are the normative first-pass for all discovery, search, and validation. Script fallback is permitted only when LSP is unavailable or its budget is exhausted.

**Planning phase (per target sorry):**
1. `lean_goal(file, line)` — understand goal before ordering
2. Up to 3 LSP search tools (time-boxed ~30s total): `lean_local_search`, one of `lean_leanfinder`/`lean_leansearch`, and `lean_loogle`
3. Record top candidate lemmas and intended next attempts in the plan
4. **Trivial-goal shortcut:** If the goal is obviously solvable (`rfl`, `simp`, `exact` with a known lemma), skip extended search — proceed directly to work phase

**Work phase (per sorry):**
1. Refresh `lean_goal(file, line)` at start
2. Run up to 2 LSP search tools before any script fallback (skip if trivial goal or prior planning search was conclusive)
3. Generate 2-3 candidate proof snippets from search results
4. Test with `lean_multi_attempt(file, line, snippets=[...])`
5. Prefer shortest passing candidate; only then edit/commit

**Fallback gate:** Script fallback (`smart_search.sh`, `search_mathlib.sh`) and repair agents are permitted when:
- LSP search budget is exhausted (at least 2 searches returning empty/inconclusive), OR
- LSP server is confirmed unavailable, timing out, or rate-limited

**Validation:** Use `lean_diagnostic_messages(file)` for per-edit checks. Reserve `lake build` for checkpoint verification or explicit `/lean4:checkpoint`.

## Review Phase

At configured intervals (`--review-every`), run review matching current scope:
- Working on single sorry → `--scope=sorry --line=N`
- Working on file → `--scope=file`
- Never trigger `--scope=project` automatically

Reviews act as gates: review → replan → continue. In prove, replan requires user approval; in autoprove, replan auto-continues.

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

**Stuck handoff evidence:** When declaring a sorry stuck, include:
- LSP queries attempted (tool name + query text)
- Top candidate lemmas returned (if any)
- `lean_multi_attempt` outcomes (snippets tested, pass/fail for each)

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

Compiler-guided repair is an **escalation-only** workflow — not the default response to a first failure. Invoke only when compiler errors are the active blocker and LSP-first tactics cannot resolve them.

**Trigger conditions** (any one sufficient):
- Same blocker signature repeats 2 consecutive iterations
- Same build error repeats after 2 repair attempts
- 3 or more distinct compiler errors active in scope simultaneously

**Direct-fix-first rule:** For straightforward single errors (missing import, obvious coercion, local instance, simple typo), apply the fix directly. Escalate to the repair agent only if the direct fix fails or the error recurs.

**Budgets:**

| Parameter | prove | autoprove |
|-----------|-------|-----------|
| Max repair attempts per error signature per cycle | 2 | 2 |
| Max total repair attempts per cycle | 6 | 8 |

**Improvement definition:** Error count in scope decreases OR the current blocker signature disappears. A repair attempt that changes errors without reducing count is neutral (counts toward budget but does not reset it).

**No-improvement rule:** If 2 consecutive repair attempts on the same signature produce no improvement → target is **stuck**. Force review + replan (see [Stuck Definition](#stuck-definition)).

| Behavior | prove | autoprove |
|----------|-------|-----------|
| Interactive repair prompts | Ask user for guidance | Coerced to autonomous: auto-select next strategy |
| On stuck after repair | Present plan for approval | Auto-replan, next cycle executes |

**Error quick-reference:**

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
