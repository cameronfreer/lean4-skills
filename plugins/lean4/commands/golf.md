---
name: golf
description: Optimize Lean proofs for brevity and clarity
user_invocable: true
---

# Lean4 Golf

Optimize Lean proofs that already compile. Reduce tactic count, shorten proofs, improve readability.

**Prerequisite:** Code must compile. Verify code compiles first (`lean_diagnostic_messages(file)` or `lake env lean <path/to/File.lean>` from project root; `lake build` for project-wide).

## Usage

```
/lean4:golf                     # Golf entire project
/lean4:golf File.lean           # Golf specific file
/lean4:golf File.lean:42        # Golf proof at specific line
/lean4:golf --dry-run           # Show opportunities without applying
/lean4:golf --search=full          # Include lemma replacement pass
/lean4:golf --max-delegates=3    # Override default 2 concurrent subagents
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or file:line to golf |
| --dry-run | No | Preview only, no changes |
| --search | No | `off`, `quick` (default), or `full` — LSP lemma replacement pass |
| --max-delegates | No | `2` — max concurrent golfer subagents (preflight must pass first) |

## Actions

1. **Verify Build** - Ensure code compiles before optimizing
2. **Find Patterns** - Detect golfable patterns:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/find_golfable.py" [file] --filter-false-positives
   ```
3. **Exact-Collapse Pass** (bounded) — For apply/exact chain anchors from `$LEAN4_SCRIPTS/find_golfable.py`:
   - **Mechanical** (≤30 anchors/file): Construct collapsed `exact` from tactic structure → `lean_multi_attempt` + `lean_diagnostic_messages` baseline check (no new diagnostics, no sorry increase). Accept if net decrease + readability not worse.
   - **Exploratory** (when `--search≠off`; consumes `--search` budget): On remaining single-goal anchors, build candidate `exact` terms from chain lemmas + local hypotheses + dot-notation rewrites → `lean_multi_attempt` + diagnostics check. Probe caps are phase-local: `quick` ≤5 probes/file; `full` ≤15 probes/file; ≤2 probes/anchor. Time budget is shared with lemma replacement (step 4): `quick` 30s total, `full` 60s total across both phases.
   - Skip: `calc`, `cases`/`induction`, multi-goal branches, blocks >7 lines, semicolon-heavy (>3), blocks with `have`/`refine`. `constructor` chains are handled by the existing instant-win rule, not this pass.
4. **Lemma Replacement** (if `--search=quick` or `full`):
   - Run LSP searches per candidate; test with `lean_multi_attempt`
   - `quick`: 1 search, ≤2 candidates; `full`: 2 searches, ≤3 candidates; ≤3 search calls; uses remaining shared time budget
   - Accept only shortest passing replacement with net size decrease
   - Hand off to axiom-eliminator if replacement needs statement changes or multi-file refactor
5. **Verify Safety** - Check usage before inlining:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/analyze_let_usage.py" [file] --line [line]
   ```
6. **Apply** - Make changes with `lean_diagnostic_messages` after each; `lake build` for final verification
7. **Report** - Show savings and saturation status

## Golfing Patterns

### Instant Wins (Always Apply)

| Before | After |
|--------|-------|
| `rw [h]; exact trivial` | `rwa [h]` |
| `ext x; rfl` | `rfl` |
| `simp; rfl` | `simp` |
| `constructor; exact h1; exact h2` | `exact ⟨h1, h2⟩` |
| `apply f; exact h` | `exact f h` |

### Safe with Verification

| Pattern | Condition |
|---------|-----------|
| Inline let | Used ≤2 times |
| Inline have | Used once, ≤1 line |

### Skip (False Positive Risk)

- Let bindings used 3+ times
- Complex have blocks
- Named hypotheses in error messages

## Output

```markdown
## Golf Results

**Optimizations applied:** 5
**Skipped:** 2 (safety)
**Total savings:** 8 lines (~12%)
**Build status:** ✓ passing

Optional next step: run `/lean4:refactor` on touched files for strategy-level simplification.
```

## Saturation

Stop when success rate < 20% or last 3 attempts failed.

## Safety

- Requires passing build to start
- Reverts immediately on build failure
- Does not create commits (use `/lean4:checkpoint`)
- `--search` replacements follow same revert-on-failure policy

### Bulk Rewrite Safety

sed/bulk rewrites activate automatically when ≥4 whitelisted syntax-only patterns are found at declaration RHS / term-wrapper positions in a file; never inside tactic blocks or calc blocks. The preview step (step 1 below) is the user confirmation gate. Default when <4 candidates: individual edits with per-edit verification.

**Whitelist:** `:= by exact t` → `:= t`, `by rfl` → `rfl`

**Skip rules:** Skip candidate when the replacement TERM introduces a nested tactic-mode boundary (a `by` at non-top-level position in the term). If context classification is uncertain, skip the rewrite — never force.

**Bulk workflow (effective per-run limit: min(10 replacements/file, 3 hunks × 60 lines); overflow recomputed on next invocation — no persistent queue):**
1. Preview — match count + 3-5 sample hunks; user confirms before applying
2. Batch apply — per-file, up to min(10, hunk/line cap) replacements
3. Validate — capture baseline diagnostics on touched files before batch; after batch run `lean_diagnostic_messages(file)` and compare: new diagnostics vs baseline + sorry-count delta
4. Auto-revert — if sorry count increases or new diagnostics appear relative to baseline, revert batch immediately
5. On permission denial — abort bulk mode, continue with individual edits

**Never bulk-rewrite:** semantic patterns, proof structure changes, let/have inlining, anything inside tactic blocks or calc blocks

### Delegation Execution Policy

When delegating to `lean4-proof-golfer` subagents:

1. **Preflight** — run one golfer task on a small target first
2. **Permission gate** — if preflight hits Edit/Bash permission prompt → stop delegation immediately, switch to direct mode in main agent; never launch additional agents after first permission denial
3. **Max `--max-delegates` concurrent** (default 2; only after preflight succeeds)
4. **Batch by value** — Batch 1: high-priority instant wins, then prompt user for checkpoint; Batch 2: medium-priority; ask before continuing
5. **After each batch** — diagnostics summary, changed files, `Continue? [yes/no]`
6. **One plan message** per batch — no repeated "launching more agents" narration
7. **Fallback contract** — if ANY subagent cannot obtain Edit/Bash permission → abort all delegation, continue direct; do NOT queue new delegates after a permission error

## See Also

- `/lean4:review` - See opportunities (read-only)
- `/lean4:refactor` - Strategy-level simplification (before golf)
- `/lean4:checkpoint` - Save after golfing
- [proof-golfing.md](../skills/lean4/references/proof-golfing.md)
- [Examples](../skills/lean4/references/command-examples.md#golf)
