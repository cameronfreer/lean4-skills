---
name: golf
description: Optimize Lean proofs for brevity and clarity
user_invocable: true
---

# Lean4 Golf

Optimize Lean proofs that already compile. Reduce tactic count, shorten proofs, improve readability.

**Prerequisite:** Code must compile. Run `lake build` first.

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
   ${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/find_golfable.py [file] --filter-false-positives
   ```
3. **Lemma Replacement** (if `--search=quick` or `full`):
   - Run LSP searches per candidate; test with `lean_multi_attempt`
   - `quick`: 1 search, ≤2 candidates; `full`: 2 searches, ≤3 candidates; budget ≤3 search calls, ≤60s
   - Accept only shortest passing replacement with net size decrease
   - Hand off to axiom-eliminator if replacement needs statement changes or multi-file refactor
4. **Verify Safety** - Check usage before inlining:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/analyze_let_usage.py [file] --line [line]
   ```
5. **Apply** - Make changes with `lean_diagnostic_messages` after each; `lake build` for final verification
6. **Report** - Show savings and saturation status

## Golfing Patterns

### Instant Wins (Always Apply)

| Before | After |
|--------|-------|
| `rw [h]; exact trivial` | `rwa [h]` |
| `ext x; rfl` | `rfl` |
| `simp; rfl` | `simp` |
| `constructor; exact h1; exact h2` | `exact ⟨h1, h2⟩` |

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
```

## Saturation

Stop when success rate < 20% or last 3 attempts failed.

## Safety

- Requires passing build to start
- Reverts immediately on build failure
- Does not create commits (use `/lean4:checkpoint`)
- `--search` replacements follow same revert-on-failure policy

### Bulk Rewrite Safety

sed/bulk rewrites are **opt-in** for whitelisted syntax-only patterns at declaration RHS / term-wrapper positions only; never inside tactic blocks. Default: individual edits with per-edit verification.

**Whitelist:** `:= by exact t` → `:= t`, `by rfl` → `rfl`

**Bulk workflow (still obeys 3-hunk cap per agent run):**
1. Preview — match count + 3-5 sample hunks before applying
2. Batch apply — per-file, max 10 replacements per batch
3. Validate — capture baseline diagnostics on touched files before batch; after batch run `lean_diagnostic_messages(file)` and compare: new diagnostics vs baseline + sorry-count delta
4. Auto-revert — if sorry count increases or new diagnostics appear relative to baseline, revert batch immediately
5. On permission denial — abort bulk mode, continue with individual edits

**Never bulk-rewrite:** semantic patterns, proof structure changes, let/have inlining, anything inside tactic blocks

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
- `/lean4:checkpoint` - Save after golfing
- [proof-golfing.md](../skills/lean4/references/proof-golfing.md)
- [Examples](../skills/lean4/references/command-examples.md#golf)
