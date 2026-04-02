# Cycle Engine Reference

> Shared logic for `/lean4:prove`, `/lean4:autoprove`, `/lean4:formalize`, and `/lean4:autoformalize`.

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
2. Up to 3 LSP search tools (time-boxed ~30s total): `lean_local_search`, preferably `lean_leanfinder` for semantic/goal-aware search (`lean_leansearch` for natural-language fallback, `lean_hammer_premise` for premise suggestions), and `lean_loogle` for type-pattern gaps
3. Record top candidate lemmas and intended next attempts in the plan
4. **Trivial-goal shortcut:** If the goal is obviously solvable (`rfl`, `simp`, `exact` with a known lemma), skip extended search — proceed directly to work phase

**Work phase (per sorry):**
1. Refresh `lean_goal(file, line)` at start
2. Run up to 2 LSP search tools before any script fallback (skip if trivial goal or prior planning search was conclusive)
3. Generate 2-3 candidate proof snippets from search results. When `lean_hammer_premise` returns premises, generate `simp only [p1, p2]` and `grind [p1, p2]` candidates.
4. Test with `lean_multi_attempt(file, line, snippets=[...])`
5. `lean_diagnostic_messages(file)` — verify; if "Try this" → `lean_code_actions(file, line)` → apply → `lean_diagnostic_messages(file)` to re-verify
6. Prefer shortest passing candidate; only then edit/commit

**Fallback gate:** Script fallback (`$LEAN4_SCRIPTS/smart_search.sh`, `$LEAN4_SCRIPTS/search_mathlib.sh`) and repair agents are permitted when:
- LSP search budget is exhausted (at least 2 searches returning empty/inconclusive), OR
- LSP server is confirmed unavailable, timing out, or rate-limited

For sorry discovery fallback, prefer one-pass structured output:
`${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/sorry_analyzer.py" <target> --format=json --report-only`.
Use default `text` for quick human review and `summary` only for counts.
Do not suppress script stderr via `/dev/null`; surfaced errors are part of the fallback signal.

**Validation:** Use `lean_diagnostic_messages(file)` for per-edit checks. Reserve `lake build` for checkpoint verification or explicit `/lean4:checkpoint`. See [Build Target Policy](#build-target-policy) for the full ladder.

## Build Target Policy

For fresh clones/worktrees or after `lake clean`, hydrate cache first and do an initial `lake build` only if needed to bootstrap LSP; the ladder below is the normal steady-state workflow after startup.

Three-tier verification ladder — use the lightest tool that answers the question:

| Tier | Tool | When | Speed |
|------|------|------|-------|
| Per-edit | `lean_diagnostic_messages(file)` | After every edit | Sub-second |
| File compile | `lake env lean <path/to/File.lean>` | File-level gate, import checks | Seconds |
| Project gate | `lake build` | Checkpoint, final gate, `/lean4:checkpoint` | Minutes |

Run `lake env lean` from the Lean project root; pass repo-relative file paths.

**Never use `lake build <file basename>`** — `lake build` does not accept file path arguments. Use `lake env lean <path/to/File.lean>` for single-file compilation.

**`lake build` progress counter:** Lake's `[N/M]` denominator grows as dependencies are discovered mid-build (e.g., 129 → 7808 in one observed run). The `[N/M]` counter and fraction are not reliable progress estimates. Set timeouts based on wall-clock experience for the current project, not step counts.

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

Bounded subroutine for stubborn sorries. Allows multi-file refactoring and helper extraction.

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
| `--deep-snapshot` | `stash` | `stash` | Pre-deep recovery (V1: `stash` only) |
| `--deep-rollback` | `on-regression` | `on-regression` | When to revert: `on-regression` / `on-no-improvement` / `always` / `never` |
| `--deep-scope` | `target` | `target` | Scope fence: `target` (sorry's file only) / `cross-file` |
| `--deep-max-files` | 1 | 2 | Max files deep may edit per invocation |
| `--deep-max-lines` | 120 | 200 | Max added+deleted lines per deep invocation |
| `--deep-regression-gate` | `strict` | `strict` | `strict`: auto-abort on regression; `off`: log only |
| Statement changes | Not permitted — rollback + stuck; hand off to `/lean4:formalize` | Not permitted — rollback + stuck; emit `next_action = redraft` when synthesis outer loop is active |
| `--commit=ask` | Per-commit prompt (yes/yes-all/no/never) | Coerced to `auto` at startup |

### Deep Safety Definitions

- **Regression**: sorry count increases, new diagnostic errors appear, or new blocker signatures introduced compared to pre-deep snapshot
- **No improvement**: sorry count unchanged AND no diagnostic improvement after deep completes
- **Rollback**: restore working tree to pre-deep snapshot via saved snapshot id/ref; mark sorry as stuck with reason (e.g., `"deep: regression — sorry count increased from 3 to 5"`)

### Deep Snapshot and Rollback

Before entering deep mode, the engine captures a **path-scoped** snapshot of all files in the deep scope (target file when `--deep-scope=target`; declared files when `--deep-scope=cross-file`). Only deep-managed paths are snapshotted — unrelated working-tree edits are not swept in.

The snapshot mechanism is implementation-defined; the contract is that rollback restores the snapshotted files to their exact pre-deep state without affecting other files.

Example (illustrative, not contractual):
```text
# Snapshot: <snapshot-create-command>(deep-managed-files, label="deep-snapshot: <sorry-id>") → <snapshot-id>
# Rollback: <snapshot-restore-command>(<snapshot-id>) → files restored, snapshot discarded
```

**Rollback triggers** (per `--deep-rollback`):

| `--deep-rollback` | Trigger |
|---|---|
| `on-regression` (default) | Regression detected |
| `on-no-improvement` | Regression OR no improvement |
| `always` | After every deep invocation (test-only) |
| `never` | Never rollback (prove only — coerced in autoprove) |

**On rollback:** restore snapshotted files to pre-deep state, mark sorry as stuck with reason `"deep: <trigger> — <detail>"`. If rollback itself fails (e.g., conflict), stop the current cycle immediately, mark sorry as stuck with `"deep: rollback failed"`, and skip checkpoint for this cycle. Stuck handoff must include the abort reason.

### Deep Scope Fence

`--deep-scope` controls which files deep may touch:

| `--deep-scope` | Behavior |
|---|---|
| `target` (default) | Only the file containing the target sorry |
| `cross-file` | Multi-file refactoring, helper extraction |

If deep edits exceed `--deep-max-files` or `--deep-max-lines`, the engine triggers immediate rollback and marks stuck with reason `"deep: scope exceeded — N files / M lines"`.

### Header Fence

Declaration headers (everything from `theorem`/`def`/`lemma` through `:= by`) are immutable during proof engine execution. The engine snapshots headers at deep entry and compares at each checkpoint.

| Context | On header change |
|---------|-----------------|
| `prove` (deep) | Immediate rollback, mark stuck: `"deep: header fence — declaration header modified"`. Suggest `/lean4:formalize`. |
| `autoprove` (deep) | Immediate rollback, mark stuck. When synthesis outer loop is active, emit `next_action = redraft`. |
| `formalize` / `autoformalize` | Statement changes are owned by the synthesis wrapper, not the proof engine. The wrapper invokes redraft when needed. |

The header fence resolves an earlier inconsistency where the inner cycle said "NO statement changes" but deep mode allowed statement generalization.

### Deep Regression Gate

When `--deep-regression-gate=strict` (default): after each deep phase, the engine compares diagnostics against the pre-deep baseline.

**File set (identical for baseline and comparison):** the target file when `--deep-scope=target`; all files declared in the deep plan when `--deep-scope=cross-file`. This is the same set used for the path-scoped snapshot.

**Baseline:** `lean_diagnostic_messages` output for all files in the set, captured immediately before the first deep edit.

**Comparison:** re-run `lean_diagnostic_messages` on the same file set and compare:

1. Sorry count increased → rollback + stuck (`"deep: regression — sorry count +N"`)
2. New diagnostic errors appeared (error not present in baseline) → rollback + stuck (`"deep: regression — new errors"`)
3. New blocker signatures introduced (see [Stuck Definition](#stuck-definition)) → rollback + stuck (`"deep: regression — new blockers"`)

When `off`: regressions are logged but do not trigger rollback. Only available in prove (coerced to `strict` in autoprove).

### Deep Safety Coercions (autoprove)

| Flag | Coerced from | Coerced to | Warning |
|---|---|---|---|
| `--deep-rollback` | `never` | `on-regression` | "deep-rollback=never disables safety rollback. Using on-regression for unattended operation." |
| `--deep-regression-gate` | `off` | `strict` | "deep-regression-gate=off allows regressions. Using strict for unattended operation." |

## Checkpoint Logic

If `--commit=never`, skip the checkpoint commit entirely — changes remain in the working tree.

Otherwise, if `--checkpoint` is enabled and there is a non-empty diff:
- **prove:** Stage only files from **accepted** fills (exclude declined fills)
- **autoprove:** Stage only files from successful, non-rolled-back work
- **Both:** Exclude files from rolled-back deep invocations — those files are restored to pre-deep state and must not be staged
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
- `git checkout --`/`git restore`/`git reset --hard`/`git clean` (commit or checkpoint first)

## Synthesis Outer Loop

Optional wrapper around the inner 6-phase cycle. Activated by `/lean4:formalize` (interactive), `/lean4:autoformalize` (autonomous), or deprecated `autoprove --formalize=restage|auto` flags.

### Algorithm

Two entry shapes depending on whether `--source` is provided:

```
# Source-backed (--formalize=auto with --source):
extract claim queue from --source (filtered by --claim-select) at startup
while queue non-empty AND no stop rule:
  1. Statement Acquisition:
       pop next claim → invoke draft → validate (lean_diagnostic_messages)
       if --commit != never: stage target, commit "draft: <summary>"
       add emitted declarations to provenance set
  2. Inner Cycle — run standard 6-phase cycle (unchanged)
  3. If inner cycle exited via stuck:
       Review Router — read next_action from stuck review
       3a. redraft → re-draft (check provenance + statement-policy); commit if allowed
       3b. Other next_action values → dispatch accordingly
     Else (sorry-free or stop rule):
       Advance to next claim

# Scope-backed (--formalize=restage, no --source):
  1. Inner Cycle — run standard 6-phase cycle on existing scope (unchanged)
  2. If inner cycle exited via stuck:
       Review Router — read next_action
       2a. redraft → re-draft stuck declaration (check provenance + statement-policy)
       2b. Other next_action values → dispatch accordingly
     Else: normal exit
```

### Draft Commit Boundary

Draft writes skeleton to a temp file (see [File Assembly Contract](#file-assembly-contract)); the outer loop appends to the target, validates with `lean_diagnostic_messages`, stages only target file, and commits with `draft:` prefix. Clean rollback boundary between statement-shaping and proof-filling.

If `--commit=never`, the outer loop skips staging and committing — the skeleton is still written to the target file (working tree only), but no `draft:` commit is created. Provenance tracking still works because it is in-memory, not git-based.

### Session-Generated Provenance

Tracks which statements were introduced by draft within the current synthesis session:

- **Representation**: in-memory set of `(file, declaration_name)` pairs, built during the session.
- **Population**: each draft call appends its emitted declarations to the set.
- **Scope**: lives for the duration of one synthesis session (`/lean4:formalize`, `/lean4:autoformalize`, or `/lean4:autoprove --formalize=*`). Not persisted to disk.
- **On restart/resume**: provenance is empty. All existing statements are treated as user-authored (`preserve`). Conservative by design.
- **On replan within same invocation**: provenance persists (in-memory state is not cleared).
- **Usage**: `--statement-policy=rewrite-generated-only` checks this set before allowing restage rewrites.

### Statement Safety

| `--statement-policy` | User-authored | Session-generated | On restage |
|---------------------|---------------|-------------------|------------|
| `preserve` | Never rewrite | Never rewrite | Error: manual intervention needed |
| `rewrite-generated-only` | Never rewrite | May rewrite | Rewrite if in provenance set; else create `T_salvaged` sibling |
| `adjacent-drafts` | Never rewrite | Never rewrite | Create `T_salvaged` sibling |

When `--formalize=restage|auto`, the effective default changes from `preserve` to `rewrite-generated-only` (with startup warning). This allows autonomous restage of session-generated statements. Explicit `--statement-policy=preserve` is respected but causes stuck restage to halt with an error rather than rewrite automatically.

### Claim Queue

- **Source**: single extraction pass from `--source` at synthesis-wrapper startup, filtered by `--claim-select`. Uses draft's ingestion logic (PDF → Read, URL → fetch, `.lean` → Read).
- **Order**: document order (position in source). Deterministic across re-runs of the same source.
- **Storage**: in-memory ordered list. Not persisted to disk.
- **On restart**: re-extraction from `--source` produces same queue; cursor resets to beginning. Already-formalized claims detected via declaration-head matching in the target file.
- **Iteration**: outer loop processes one claim at a time — pop next claim, pass it directly to draft as the topic, run inner cycle to completion, then advance. The `--claim-select` flag filters claims at queue-extraction time only; individual draft calls receive a single pre-selected claim. Queue management is outer-loop-internal — draft never sees `queue` as a selection policy.

### File Assembly Contract

- Draft emits declaration-only blocks (no imports/opens/section wrappers) to temp path when `--caller=autoformalize|formalize`. Declarations use fully-qualified names — no `open`/`open scoped` needed.
- Import dependencies expressed as `-- needs-import: <module>` comments at top of temp output. This is the only structured signal.
- Outer loop maintains target file preamble: deduplicates `-- needs-import:` lines, prepends new imports, appends declarations with `-- draft: <claim> (<timestamp>)` boundary markers.
- Declaration-name collision check before each append: match `theorem <name>`, `def <name>`, `lemma <name>`, etc. at line start in target file. If found, skip (already formalized in a prior run).

### Review Router

Stuck-mode review emits a `next_action` field. The outer loop dispatches:

| `next_action` | Outer loop response |
|---------------|---------------------|
| `continue` | Resume inner cycle with revised plan |
| `deep` | Escalate to deep mode |
| `repair` | Enter repair mode for compiler blockers |
| `redraft` | Re-draft the stuck declaration (check provenance + statement-policy) |
| `golf` | Run golf pass on sorry-free file |
| `stop` | Halt current claim, advance to next (or stop if queue empty) |

`next_action` is informational when the outer loop is inactive (`--formalize=never`). When active, it is the routing gate.

## Pre-flight Context for Subagent Dispatch

MCP tools may not be available in subagents (anthropics/claude-code#39962). Before dispatching any proof-editing agent, collect relevant MCP results and include them in the agent prompt as the agent's starting state. Pass a summarized subset — not raw dumps.

### Canonical block shape

Include this block (or the relevant subset) in the agent dispatch prompt:

```
## Pre-collected LSP context
(MCP tools may be unavailable — use this as your starting state.)
### Goal state (file:line)
<lean_goal output>
### Diagnostics
<lean_diagnostic_messages output, summarized>
### Search results
<tool + query>: <top results>
### Candidates tested
<lean_multi_attempt snippets + results, if any>
### Code actions (if collected)
<lean_code_actions output for relevant lines, if any>
### Owned files
<list of files this agent is authorized to edit>
### Allowed scratch location
/tmp (never repo root)
```

Omit sections with no data. The per-agent subsections below specify which parts to include.

**Exclusive file ownership:** If two candidate dispatches would edit any of the same files, serialize them or keep one in-thread. Never dispatch concurrent agents with overlapping owned-file sets.

### sorry-filler-deep

Include alongside file:line and failure reason:
- Goal state: `lean_goal(file, line)` output
- Diagnostics: `lean_diagnostic_messages(file)` summary
- Search results: tool + query + top results from prior planning phase
- Candidates tested: `lean_multi_attempt` snippets and outcomes

### proof-repair

Extend the existing structured error JSON with:
- `searchResults`: top results from any LSP searches already performed
- `multiAttemptResults`: snippets tested and their outcomes

### proof-golfer

Include alongside file path and search mode:
- Baseline diagnostics: `lean_diagnostic_messages(file)` summary
- Golfable patterns: `find_golfable.py` output if already run
- Candidate collapse targets: `find_exact_candidates.py` output if already run
- Pre-tested candidates: `lean_multi_attempt` results if any candidates were tested in the parent thread

### axiom-eliminator

Include alongside scope and axiom list:
- Diagnostics: `lean_diagnostic_messages(file)` on target files
- Axiom audit: `check_axioms_inline.sh` output

## See Also

- [sorry-filling.md](sorry-filling.md) — Sorry elimination tactics
- [compilation-errors.md](compilation-errors.md) — Error-by-error repair guidance
- [command-examples.md](command-examples.md) — Usage examples
