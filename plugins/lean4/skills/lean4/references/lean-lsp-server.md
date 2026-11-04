# Lean LSP Server - Quick Reference

Use the selected backend through the [canonical semantic dispatch](../SKILL.md#canonical-semantic-tool-dispatch).
Preserve explicit MCP selection; otherwise prefer `cli_local` after a successful
`lean4-skills-lsp doctor --project ROOT --json`. Native inspection uses the
project's Lean server without MCP. [Install/build the CLI separately](../../../../../INSTALLATION.md#native-lean-lsp-cli-source-install).

Semantic calls below are workflow notation, not shell commands. Translate
supported local calls through the canonical table in `cli_local`. Unmapped
MCP tools (outline, widgets, completions, standalone code and profiling) and
remote search services have no native equivalent.
Skip unavailable tools rather than counting them against local search budgets.

### Native response and trial rules

- Check `ok`, `status`, `data`, and `error`; exit 1 may retain useful diagnostics
  or candidate observations. Exit 4 means timeout or stale input/dependency.
- Native trials are **sequential**, within one operation deadline. Supply an
  exact half-open range in 1-based Unicode codepoints, a nonempty JSON string
  array, and the original `sourceIdentity` as `--expect-source ID`.
- `closed_local_goals` is advisory, including for a `sorry` candidate. Inspect
  warnings and errors; null/no-goal or incomplete elaboration is not success.
  Keep dependency-aware compilation, no-sorry and standard-axiom/project gates.
- Code actions return edits without applying them. Revalidate source identity
  and disk snapshot before applying reviewed proof-body edits.
- Search with `data.complete: false` is incomplete, never proof of absence.

```bash
lean4-skills-lsp goal FILE --project ROOT --line 42 --column 3 --json
# candidates.json is a JSON array such as ["simp", "rfl"]. Retain the goal's ID.
lean4-skills-lsp attempt FILE --project ROOT --range 42:3-42:8 \
  --snippets-file candidates.json --expect-source ID --json
lean4-skills-lsp diagnostics FILE --project ROOT --json
```

`FILE`, `ROOT`, the range and `ID` are placeholders for the inspected project
and exact source snapshot. The CLI does not write candidates to disk.

---

## Prerequisites

**Before using LSP tools in a fresh clone or worktree:**

1. **Prime the cache in this worktree first.**
   Use the project's cache command:
   - `lake cache get` on newer Lake versions, or
   - `lake exe cache get` for projects that still use the mathlib cache executable.

   This avoids rebuilding dependencies from scratch after a fresh checkout or `lake clean`.

2. **Build only for demonstrated missing/stale imports.**
   Explicitly run dependency-aware `lake lean <path/to/File.lean>` or the
   appropriate `lake build` from the target root, then stop/requery the native
   session. Native disk/virtual opens use `dependencyBuildMode=never`.
   For a timeout alone, inspect status/error, check native status/doctor, allow
   at most one bounded retry, then fallback/report. Do not start a build solely
   because a query timed out. The default whole-operation deadline is 30s.

3. **After bootstrap, use LSP for normal iteration.**
   Day-to-day proof development should use LSP tools for discovery, search, and per-edit validation.
   Reserve `lake env lean <path/to/File.lean>` (run from project root) for fast file-local checks — it elaborates against the built `.olean`s of the file's imports and does not rebuild them, so after editing an imported module run `lake lean <path/to/File.lean>` first ([File Gate Scope](cycle-engine.md#file-gate-scope)) — and `lake build` for checkpoint/final verification.

**Worktrees:** prime cache separately per worktree. Do **not** symlink another worktree's `.lake/build`.

4. **For MCP/script search, install ripgrep when required by that backend.**
   Native indexed symbol search does not require ripgrep:
   - macOS: `brew install ripgrep`
   - Linux: `apt install ripgrep` or https://github.com/BurntSushi/ripgrep#installation
   - Windows: https://github.com/BurntSushi/ripgrep#installation
   - Verify: `rg --version` should work

Missing imports or a missing selected-backend dependency can prevent useful inspection; diagnose the specific failure before rebuilding.

---

## Version Notes

The following version notes describe **MCP only**, lean-lsp-mcp
**v0.20+/v0.21+** (February 2026), not the native JSON/flag contract.

- **v0.21.0**: Widget support, improved multiline in lean_goal/lean_multi_attempt.
- **v0.20.0**: `lean_hammer_premise` added (premise suggestions for simp/aesop/grind). `lean_profile_proof` switched to line-based identification.

Additional tools exist upstream (lean_term_goal, lean_completions, lean_declaration_file, lean_build, lean_get_widgets) — see [lean-lsp-mcp README](https://github.com/oOo0oOo/lean-lsp-mcp) for full list.

---

**Tip: Capture build output with `tee`** - Avoid building twice:
```bash
# Build once, capture AND view first 50 lines (or tail -50, or grep error)
lake build 2>&1 | tee /tmp/lean-build-$$.log | head -50

# Later: read from captured file - no rebuild needed
tail -100 /tmp/lean-build-$$.log
grep -i error /tmp/lean-build-$$.log
```
Without `tee`, piping to `head`/`grep` discards the rest. With `tee`, the full output is saved while you still see filtered results.

---

## Minimum Workflow (5 Steps)

1. `lean_goal(file, line)` - See what to prove
2. `lean_multi_attempt(file, line, snippets=["simp", "ring", "exact?"])` - Test tactics
3. `lean_diagnostic_messages(file)` - Verify no errors
4. If diagnostics show "Try this" → `lean_code_actions(file, line)` → apply edit → `lean_diagnostic_messages(file)` to re-verify
5. `lean_goal(file, line)` - Confirm no remaining goals

## Full Workflow Pattern

**For thorough proof development:**

```
1. lean_goal(file, line)                    # What to prove?
2. lean_local_search("keyword", limit=10)   # Does it exist?
3. lean_multi_attempt(file, line, snippets=[ # Test tactics
     "  simp", "  omega", "  apply lemma"
   ])
4. [Edit file with winner]
5. lean_diagnostic_messages(file)           # Verify — check for "Try this"
6. lean_code_actions(file, line)            # If "Try this" appeared, resolve it
7. lean_diagnostic_messages(file)           # Re-verify after applying code action
8. lean_goal(file, line)                    # Confirm no remaining goals
```

Latency depends on imports, indexing and the project. Reusing a session avoids
restarting Lean for every observation; no fixed speedup or latency is promised.

---

## Critical Rules

1. **NEVER edit without checking goal state first** (`lean_goal`)
2. **ALWAYS check diagnostics after edits** (don't wait for build)
3. **Search before guessing** - use `lean_local_search` first within the operating profile budget
4. **Check goals between tactics** - see intermediate progress
5. **Use `lean_multi_attempt` liberally** - test multiple tactics at once
6. **Respect budgets** - native operations have deadlines; selected MCP tools also have backend-specific API limits
7. **NEVER use `lean_file_contents` on large files** - wastes tokens, use `Read` tool instead (see warning below)

---

## Tool Summary

This is the MCP tool catalogue. In `cli_local`, only mapped local operations
are available; the native response contract above takes precedence.

**Local tools (no remote API quota):**
- Direct LSP queries against your project files
- Project-dependent latency, bounded by the operation deadline

**External tools (selected MCP only; rate limits vary per tool):**
- Remote API calls to leansearch.net, leanfinder, loogle.lean-lang.org
- `lean_loogle` is remote by default; local mode available (`--loogle-local` / `LEAN_LOOGLE_LOCAL`)
- Rate limits are per-tool (separate pools); managed by LSP server

**Best practice:** Always use local tools first (especially `lean_local_search`), then external tools only when local search doesn't find what you need.

| Tool | Type | Rate Limit | Speed | Use For |
|------|------|------------|-------|---------|
| `lean_goal` | **Local** | None | Project-dependent | See goals (always!) |
| `lean_local_search` | **Local** | None | Project-dependent | Find lemmas (use first!) |
| `lean_multi_attempt` | **Local** | None | Project-dependent | Compare tactic candidates |
| `lean_diagnostic_messages` | **Local** | None | Project-dependent | Check errors |
| `lean_code_actions` | **Local** | None | Project-dependent | Resolve "Try this" suggestions |
| `lean_hover_info` | **Local** | None | Project-dependent | Check syntax/types |
| `lean_file_outline` | **Local** | None | Fast | File structure overview |
| `lean_run_code` | **Local** | None | Fast | Run standalone snippets |
| `lean_file_contents` | **Local** | None | Fast | **DEPRECATED** — use Read tool |
| `lean_profile_proof` | **Local** | None | Slow | Profile proof performance |
| `lean_leanfinder` | **External** | 10/30s | Fast | Semantic search (best for goals!) |
| `lean_loogle` | **External** | Remote default; unlimited if local | Fast | Type patterns |
| `lean_leansearch` | **External** | 3/30s | Slower | Natural language fallback |
| `lean_state_search` | **External** | 3/30s | Fast | Proof state |
| `lean_hammer_premise` | **External** | 3/30s | Fast | Premise suggestions for simp/aesop/grind |

**See [lean-lsp-tools-api.md](lean-lsp-tools-api.md) for detailed API documentation.**

---

## ⚠️ `lean_file_contents` — DEPRECATED

**`lean_file_contents` is deprecated upstream.** Do not use it — use the `Read` tool instead.

It wastes tokens and will error if file exceeds 25000 tokens:

```
Error: MCP tool "lean_file_contents" response (36863 tokens) exceeds
maximum allowed tokens (25000). Please use pagination, filtering, or
limit parameters to reduce the response size.
```

**Instead, use:**
- **`Read` tool** (Claude Code built-in) - optimized for large files, supports offset/limit
- **`lean_goal`** - for specific line's proof state (< 1% of file size)
- **`lean_hover_info`** - for specific term's type
- **`lean_diagnostic_messages`** - for errors only
- **`lean_local_search`** - to find specific definitions without reading entire file

**Why:** `lean_file_contents` loads the entire file with annotations, consuming tokens proportional to file size. Most proof development tasks only need targeted information (goals, errors, specific definitions), not the whole file.

**Rule of thumb:** If you need to read a file, use `Read` or Grep rather than `lean_file_contents`.

---

## Common Usage Patterns

### When stuck on a proof

This remote-search ladder requires selected MCP. In `cli_local`, use local
symbol search and its bounded script fallback instead.
```
1. lean_goal(file, line)              # See exact state
2. lean_leanfinder("⊢ ... + hint")    # Semantic search (paste goal!)
3. lean_loogle("pattern")             # Type pattern search (unlimited if local mode)
4. lean_hammer_premise(file, l, col)  # Premise suggestions for simp/aesop/grind
5. lean_leansearch("description")     # Natural language search
6. lean_state_search(file, line, col) # Proof state search
```

### Emergency debugging
```
1. lean_diagnostic_messages(file)     # What errors?
2. lean_hover_info(file, line, col)   # What's the type?
3. lean_goal(file, line)              # What are goals?
```

### Testing multiple approaches
```
lean_multi_attempt(file, line, snippets=[
  "  simp [lemma1]",
  "  omega",
  "  apply lemma2"
])
```
See which works, pick the best one!

---

## Complete Example: End-to-End Proof

**Task:** Prove `n + m = m + n`

```lean
lemma test_add_comm (n m : ℕ) : n + m = m + n := by
  sorry
```

### Step 1: Check goal (ALWAYS FIRST!)
```
lean_goal(file, line=12)
→ Output:
After:
n m : ℕ
⊢ n + m = m + n
```
**Now you know exactly what to prove!**

### Step 2: Search for lemmas
```
lean_local_search("add_comm", limit=5)
→ [{"name": "add_comm", "kind": "theorem", ...}]
```
**Found it! But let's test multiple approaches...**

### Step 3: Compare tactic candidates
```
lean_multi_attempt(file, line=13, snippets=[
  "  simp [Nat.add_comm]",
  "  omega",
  "  apply Nat.add_comm"
])
→ All three show "no goals" — confirm with lean_diagnostic_messages before committing
```
**Pick simplest: `omega`**

### Step 4: Edit file
```lean
lemma test_add_comm (n m : ℕ) : n + m = m + n := by
  omega
```

### Step 5: Verify immediately
```
lean_diagnostic_messages(file)
→ []  ← No errors!
```

### Step 6: Confirm completion
```
lean_goal(file, line=13)
→ After:
no goals
```
Local goals are closed. Inspect all diagnostics, then run the required file,
no-sorry, axiom and project gates before claiming completion.

---

## Common Mistakes to Avoid

❌ **DON'T:**
- Edit → build → see error (too slow!)
- Guess lemma names without searching
- Apply tactics blind without checking goal
- Use rate-limited search when `lean_local_search` works
- Skip intermediate goal checks in multi-step proofs

✅ **DO:**
- Check goal → search (local first!) → test → apply → verify
- Use `lean_multi_attempt` to explore tactics
- Verify with `lean_diagnostic_messages` after every edit
- Check intermediate goals after each tactic
- Respect rate limits

---

## Troubleshooting

### "Unknown identifier" errors
**Problem:** `add_comm` not found

**Solutions:**
1. Try qualified name: `Nat.add_comm`
2. Use `lean_local_search` to find correct name
3. Try tactic instead: `omega` or `simp`

### "Function expected" with type classes
**Problem:** `StrictMono Nat.succ` fails

**Solution:** Add type annotation: `StrictMono (Nat.succ : ℕ → ℕ)`

### Search finds nothing
**Problem:** `lean_local_search` returns empty

**Solutions:**
1. Try partial matches: `"add"` instead of `"add_zero"`
2. If native search is incomplete, reformulate one query or use script search
3. Only with selected MCP: try loogle patterns or natural-language search

### Multi-attempt shows all failures
**Check:**
1. Proper indentation? Include leading spaces
2. Correct line number? Point to tactic line
3. Native: exact half-open range and source identity? Preserve multiline strings and indentation in the candidate JSON

### Empty diagnostics but proof incomplete
**Problem:** `[]` diagnostics but not done

**Solution:** Check `lean_goal` - if goals remain, need more tactics

**Key insight:** Empty diagnostics = no errors, but proof may be incomplete. Always verify goals.

---

## Why This Matters

A persistent LSP session supports a goal → search → trial → diagnostics loop.
It complements the file, no-sorry, axiom and project checks; it does not replace
proof certification. See [native validation](../../../../../INSTALLATION.md#native-validation-and-optional-mathlib-measurements)
for reproducible tests and fixture-specific measurements, not general speed or
memory guarantees.
