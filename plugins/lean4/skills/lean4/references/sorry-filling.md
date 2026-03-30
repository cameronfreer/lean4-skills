# Sorry Filling Reference

> **Primary reference** for sorry-filling tactics. The prove/autoprove work phase implements this workflow; see [command-examples.md](command-examples.md) for session transcripts.

Quick reference for filling Lean 4 sorries systematically.

## Core Workflow

1. **Understand Context** - `lean_goal(file, line)` first, then read surrounding code
2. **Search Mathlib FIRST** - Most proofs already exist
3. **Generate Candidates** - 2-3 proof approaches
4. **Test Before Applying** - Use `lean_multi_attempt` to test candidates, then `lean_diagnostic_messages(file)` to confirm no residual errors
5. **Apply Working Solution** - Shortest working proof wins

## LSP-First Requirement

**Always use LSP tools before scripts:**
1. `lean_goal(file, line)` — understand the goal
2. `lean_local_search("keyword")` — search mathlib
3. `lean_multi_attempt(file, line, snippets=[...])` — test candidates
4. `lean_diagnostic_messages(file)` — verify no residual errors; check for "Try this" suggestions
5. If diagnostics show "Try this" → `lean_code_actions(file, line)` to resolve to a concrete edit → `lean_diagnostic_messages(file)` to re-verify after applying
6. If initial searches/attempts are inconclusive: `lean_hammer_premise(file, line, col)` — premise suggestions for simp/aesop/grind (rate-limited 3/30s)

**File ownership:** One writer per owned file set. A subagent owns only the files it was dispatched to work on. Do not edit files outside the owned set without escalating to the caller. Never create scratch files in the repo root.

**Scratch-work preference order:**
- Use the live file + `lean_goal` / `lean_multi_attempt` / `lean_diagnostic_messages` when the question depends on the actual file context.
- If you need an isolated experiment, prefer `lean_run_code` over creating temporary `.lean` files.
- Use `/tmp` scratch files only when `lean_run_code` is unavailable or insufficient and the experiment should not touch the live file.

**Session-end reporting:** Report `files_touched` (files edited) and `scratch_files_created` (any `/tmp` files used for experiments). The caller uses this for staging and cleanup.

Only fall back to scripts (`$LEAN4_SCRIPTS/sorry_analyzer.py`, `$LEAN4_SCRIPTS/smart_search.sh`) if:
- LSP server unavailable
- LSP results inconclusive after 2-3 searches

When using `sorry_analyzer.py`:
- Default (`text`) already returns count + context in one call.
- Use `--format=json` for structured downstream parsing.
- Use `--format=summary` only when you need counts only.
- Keep stderr visible; do not redirect analyzer stderr to `/dev/null`.

Log which approach worked for each sorry.

## Todo-Based Workflow (For Multiple Sorries)

**Problem:** When there are 10+ sorries, it's easy to get lost trying to work on all of them at once.

**Solution:** Enumerate sorries, add each to a TODO list, and work on ONE at a time.

**Step 1: Enumerate**
```
List all sorry's in the project, then add each as a single item to the TODO list.
```

**Step 2: Focus on ONE**
```
Fill in Sorry #01. DO NOT MOVE ON TO OTHER SORRY'S BEFORE THIS ONE IS FILLED.
```

**Step 3: Verify compilation**
```bash
lake env lean path/to/File.lean   # run from project root
```

**Step 4: Repeat**
Continue with the next sorry in the TODO list.

## Search Strategies

**By name pattern:**
```bash
bash $LEAN4_SCRIPTS/search_mathlib.sh "continuous compact" name
```

**Multi-source smart search:**
```bash
bash $LEAN4_SCRIPTS/smart_search.sh "property description" --source=leansearch
```

**Get tactic suggestions:**
See [tactic-patterns.md](tactic-patterns.md) for goal-based tactic recommendations.

## Common Sorry Types

### Type 1: "Forgot to search mathlib" (most common)
**Solution:** Search thoroughly, apply existing lemma

### Type 2: "Just needs right tactic" (common)
**Solution:** Try `rfl`, `simp`, `ring`, or domain automation

### Type 3: "Missing intermediate step" (less common)
**Solution:** Add `have` with connecting lemma

### Type 4: "Complex structural proof" (rare)
**Solution:** Break into sub-sorries with clear strategy

### Type 5: "Actually needs new lemma" (very rare)
**Solution:** Extract as helper lemma, prove separately

## Proof Candidate Generation

**Always generate 2-3 approaches:**

**Candidate A - Direct:**
```lean
exact lemma_from_mathlib arg1 arg2
```

**Candidate B - Tactics:**
```lean
intro x
have h1 := lemma_1 x
simp [h1]
apply lemma_2
```

**Candidate C - Automation:**
```lean
simp [lemma_1, lemma_2, *]
```

**Candidate D - Premise-based (from `lean_hammer_premise`):**
```lean
simp only [premise_1, premise_2, premise_3]
-- or: grind [premise_1, premise_2]
-- or: aesop
```

## Tactic Suggestions by Goal Pattern

| Goal Pattern | Primary Tactic | Reason |
|--------------|----------------|---------|
| `⊢ a = b` | `rfl`, `simp`, `ring` | Equality |
| `⊢ ∀ x, P x` | `intro x` | Universal |
| `⊢ ∃ x, P x` | `use [term]` | Existential |
| `⊢ A → B` | `intro h` | Implication |
| `⊢ A ∧ B` | `constructor` | Conjunction |
| `⊢ A ∨ B` | `left`/`right` | Disjunction |
| `⊢ a ≤ b` | `linarith`, `omega` | Inequality |

## Testing Candidates

**With LSP server (preferred):**
```
lean_multi_attempt(
  file = "path/to/file.lean",
  line = line_number,
  snippets = [
    "candidate_A_code",
    "candidate_B_code",
    "candidate_C_code"
  ]
)
```

**Without LSP:**
- Apply candidate
- Run `lean_diagnostic_messages(file)` per-edit; `lake env lean path/to/File.lean` (from project root) for file gate
- If fails, try next candidate

## Common Errors

**Type mismatch:**
- Add coercion: `(x : ℝ)` or `↑x`
- Try different lemma form
- Check implicit arguments

**Tactic failure:**
- Add specific lemmas: `simp [lemma1, lemma2]`
- Try manual steps instead of automation
- Check hypothesis availability

**Import missing:**
- Add import detected from search results
- Use `#check LemmaName` to verify

## Best Practices

**⚠️ Critical: Verify compilation before moving on**
LSP tools can sometimes show success when problems remain. After a sequence of changes, before moving on to something else entirely, verify with:
- Per-edit: `lean_diagnostic_messages(file)`
- File gate: `lake env lean path/to/File.lean` (run from project root)
- Project gate: `lake build` (checkpoint/final only)

This catches issues that per-edit LSP may miss.

- Follow mathlib 100-char line width — do not wrap lines at 80 when they fit within 100

**💡 Cache after clean or in a fresh worktree**
If you run `lake clean`, or start from a fresh clone/worktree, hydrate the cache before the first full build:
```bash
lake cache get
# or, in projects that use the older mathlib cache executable:
lake exe cache get
```
Otherwise you may recompile large dependencies from scratch.

Do this in the current worktree. Do not symlink another worktree's `.lake/build`; separate worktrees may be on different commits and should keep separate local build directories.

✅ **Do:**
- Search mathlib exhaustively before proving
- Test all candidates if possible
- Use shortest working proof
- Verify: `lean_diagnostic_messages(file)` per-edit; `lake env lean <path/to/File.lean>` for file gate (from project root)
- Add necessary imports

❌ **Don't:**
- Skip mathlib search
- Apply without testing
- Use overly complex proofs when simple ones work
- Forget imports
- Leave sorries undocumented if you can't fill them

## When to Escalate

**Give up and escalate if:**
- All 3 candidates fail with same error
- Goal requires domain knowledge you don't have
- Needs multi-file refactoring
- Missing foundational lemmas
- Time spent > 15 minutes on single sorry

**Escalation options:**
- Break into smaller sub-sorries
- Extract as helper lemma
- Document as TODO with strategy
- Use `/lean4:prove --deep=stuck` for deep sorry-filling workflow

**If statement may be false:**
- Run preflight falsification (decide, small enumeration)
- If counterexample found, create `T_counterexample`
- Create `T_salvaged` with weaker/corrected statement
- See prove/autoprove stuck → salvage workflow

## Output Size Limits

**For fast path:**
- Max 3 candidates per sorry
- Each diff ≤80 lines
- If 0/3 compile, skip and continue (or escalate with `--deep`)
