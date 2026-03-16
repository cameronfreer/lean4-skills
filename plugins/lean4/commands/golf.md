---
name: golf
description: Improve Lean proofs for directness, clarity, performance, and brevity
user_invocable: true
---

# Lean4 Golf

Improve Lean proofs that already compile. Score candidates by: correctness → directness → clarity/inference burden → performance/determinism → length. Length is still a core goal, but a tiebreaker among acceptable proofs.

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
2. **Find Patterns** - Detect golfable patterns (in policy order: directness → structural → conditional):
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/find_golfable.py" [file] --filter-false-positives
   ```
   For direct-proof discovery when `--search` is enabled or syntactic pass stalls:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/find_exact_candidates.py" [file]
   ```
3. **Exact-Collapse Pass** (bounded) — For apply/exact chain anchors from `$LEAN4_SCRIPTS/find_golfable.py`:
   - **Mechanical** (≤30 anchors/file): Construct collapsed `exact` from tactic structure → `lean_multi_attempt` + `lean_diagnostic_messages` baseline check (no new diagnostics, no sorry increase). Accept if the replacement is more direct or clearer. Reject if it introduces heavier automation (simpa, rwa, broad simp) to replace an explicit proof, if term length exceeds ~80 chars, if dot-chain depth > 2, or if it removes meaningful intermediate names. A 1-line saving that raises inference burden is not a win.
   - **Exploratory** (when `--search≠off`; consumes `--search` budget): On remaining single-goal anchors, build candidate `exact` terms from chain lemmas + local hypotheses + dot-notation rewrites → `lean_multi_attempt` + diagnostics check. Probe caps are phase-local: `quick` ≤5 probes/file; `full` ≤15 probes/file; ≤2 probes/anchor. Time budget is shared with lemma replacement (step 4): `quick` 30s total, `full` 60s total across both phases.
   - Skip: `calc`, `cases`/`induction`, multi-goal branches, blocks >7 lines, semicolon-heavy (>3), blocks with `have`/`refine`. `constructor` chains are handled by the existing instant-win rule, not this pass.
4. **Lemma Replacement** (if `--search=quick` or `full`):
   - Run LSP searches per candidate; test with `lean_multi_attempt`
   - `quick`: 1 search, ≤2 candidates; `full`: 2 searches, ≤3 candidates; ≤3 search calls; uses remaining shared time budget
   - Accept the best passing replacement by the scoring order below
   - Hand off to axiom-eliminator if replacement needs statement changes or multi-file refactor
5. **Verify Safety** - Check usage before inlining:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/analyze_let_usage.py" [file] --line [line]
   ```
6. **Apply** - Make changes with `lean_diagnostic_messages` after each; `lake build` for final verification
7. **Report** - Show savings and saturation status

## Golfing Patterns

### Instant Wins (Always Apply)

| Before | After | Notes |
|--------|-------|-------|
| `ext x; rfl` | `rfl` | |
| `simp; rfl` | `simp` | |
| `constructor; exact h1; exact h2` | `exact ⟨h1, h2⟩` | |
| `apply f; exact h` | `exact f h` | |
| `by exact t` | `t` | At declaration RHS / term-wrapper positions only — not inside tactic blocks |

### Safe with Verification

| Pattern | Condition |
|---------|-----------|
| Inline let | Used ≤2 times |
| Inline have | Used once, ≤1 line |

### Skip (False Positive Risk)

- Let bindings used 3+ times
- Complex have blocks
- Named hypotheses in error messages

### Golfing Policy

**Semicolons:** Never introduce naked `;` as a golfing transform. `<;>` may be introduced only when applying a single identical tactic to literally identical goals (its intended purpose — e.g., `constructor <;> simp`); do not use it to compress non-identical branches. When counting line savings, each `;`-separated tactic counts as its own line — semicolons do not reduce line count. If existing code uses `;` or `<;>`, do not count those lines as savings and do not target rewrites that preserve or expand semicolon usage.

**Scoring order.** A candidate is a win iff correct and not rejected (see below). Among wins, prefer in this order: (1) more direct proof shape, (2) lower inference/search burden, (3) better performance/determinism, (4) shorter code. Length is still a core goal of golf — it is a tiebreaker among acceptable proofs, not a license to introduce heavier tactics. Inference burden and performance are judged heuristically by the tactic complexity ladder, not by measurement: `rfl`/`exact` < `rw`/`apply` < `simp only` < `simpa`/`rwa` < broad `simp`/`decide`/`omega`/`grind`.

**Hard reject if:** introduces naked `;` · introduces `<;>` on non-identical goals (per semicolon policy) · moves UP the complexity ladder for only a 1-line win · removes meaningful names · collapsed term > ~80 chars or dot-chain > 2 · replaces direct proof with terminal `simp only` without user opt-in · replaces `exact` with `simpa`/`rwa` unless `exact` fails.

**Terminal `simp only` caveat:** Narrowing non-terminal `simp` → `simp only` is always valid (the [FlexibleLinter](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linter/FlexibleLinter.html) flags non-`only` simp before rigid tactics). But terminal `simp` vs `simp only` is a style split — some projects prefer terminal `simp` for resilience to simp-set changes (the converse concern). Do not narrow terminal `simp` or introduce terminal `simp only` without user confirmation. In non-interactive/delegate mode, skip unless project style already uses it nearby.

**Minimum value filter:** 1-line savings only worth surfacing if (a) zero-risk syntax cleanup (e.g., `by exact` → `t`) or (b) also improve clarity or performance.

**`simpa`/`rwa` direction rule:**
- Never replace `exact t` with `simpa using t` unless `exact t` fails.
- Only replace `simpa using` with `exact` when the elaborated target is already literally the same type — do not guess.
- `simpa using` is only a win when it deletes surrounding boilerplate (an extra `rw`, `change`, or `simp` block).
- In coercion-heavy or subtype-heavy proofs, test `exact` first; only fall back to `simpa using` if transport is actually needed.
- Treat `calc` steps, subtype witnesses, and cast/transport goals as unsafe-by-default for wrapper removal (simpa→exact, rwa→rw+exact).
- Note: `simp using` is NOT a drop-in for `simpa using` in term positions — they have different semantics.

## Output

```markdown
## Golf Results

**Meaningful simplifications:** 3 (directness improvements)
**Performance cleanups:** 1 (simp narrowing)
**Syntax cleanups:** 1 (by exact → term)
**Skipped:** 2 (1 safety, 1 marginal compression)
**Build status:** ✓ passing
**Total savings:** 8 lines (~12%)

Optional next step: run `/lean4:checkpoint` to save progress.
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
