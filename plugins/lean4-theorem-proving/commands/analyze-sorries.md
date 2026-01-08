---
description: Analyze Lean 4 sorries in the current repo and summarize hotspots
allowed-tools: Bash(python3:*), Bash(ls:*)
---

# Sorry Analysis and Planning

Interactive analysis of incomplete proofs to plan systematic sorry-filling work.

## Default: Analyze Entire Project

Run analysis on the entire project:

!`python3 .claude/tools/lean4/sorry_analyzer.py . --format=text`

**Note:** By default, `.lake/` directories (dependencies like mathlib) are excluded. To include them, add `--include-deps`.

**Note:** If this fails, the SessionStart hook may not have staged the analyzer. Restart your session after reinstalling the plugin.

## Workflow

### 1. Determine Scope

**Ask user if analyzing specific scope:**
```
Analyze sorries in:
1. Specific file (provide path)
2. Specific directory (provide path)
3. Entire project (default above)
4. Interactive mode (TUI browser)

Which scope? (1/2/3/4)
```

### 2. Run Analysis for Specific Scope

Based on user's choice, construct and execute ONE of these commands:

**For specific file (replace with actual path):**
```bash
python3 .claude/tools/lean4/sorry_analyzer.py MyFile.lean --format=text
```

**For specific directory (replace with actual path):**
```bash
python3 .claude/tools/lean4/sorry_analyzer.py src/ --format=text
```

**For interactive TUI mode (replace with actual path):**
```bash
python3 .claude/tools/lean4/sorry_analyzer.py . --interactive
```

**IMPORTANT:** Never use placeholders like `PATH` or `<path>` in executed commands. Always use concrete file paths provided by the user.

**If the script is not available, use grep fallback:**
```bash
grep -n "sorry" . --include="*.lean" -r
```

### 3. Present Results

**If no sorries found:**
```
🎉 No sorries found in [scope]!

All proofs are complete. Excellent work!

Next steps:
- Run /check-axioms to verify no custom axioms
- Run /golf-proofs to optimize proof size
- Commit your complete proofs!
```

**If sorries found:**
```
📋 Sorry Analysis for [scope]

Total sorries: [N]
Files affected: [M]

By file:
  [file1]: [count] sorries
  [file2]: [count] sorries
  ...

Documented (with TODO): [X] sorries
Undocumented: [Y] sorries ⚠️

[If undocumented > 0]:
⚠️ [Y] sorries lack documentation!
These should have TODO comments explaining:
- What needs to be proven
- Required lemmas or techniques
- Why it's currently a sorry
```

### 4. Categorize and Prioritize

**Group sorries by estimated difficulty:**

a) **Scan documentation for keywords:**
- "straightforward", "simple", "obvious" → **Easy**
- "need to find lemma", "mathlib probably has" → **Medium**
- "complex", "not sure how", "research needed" → **Hard**
- No documentation → **Unknown** (document first!)

b) **Present prioritized list:**
```
Sorry Priority Analysis:

🟢 Easy (likely <30 min each): [N] sorries
  - [file]:[line] - [brief description from TODO]
  - [file]:[line] - [brief description from TODO]

🟡 Medium (30-60 min each): [M] sorries
  - [file]:[line] - [brief description from TODO]
  - [file]:[line] - [brief description from TODO]

🔴 Hard (>60 min each): [K] sorries
  - [file]:[line] - [brief description from TODO]

⚪ Undocumented: [U] sorries
  - [file]:[line] - (no strategy documented)

Recommendation: Start with Easy sorries for quick wins!
```

### 5. Suggest Next Action

**Based on results:**

**If many undocumented sorries:**
```
Recommendation: Document these sorries first!

For each sorry, add a comment above it:
-- TODO: [what needs to be proven]
-- Strategy: [approach to take]
-- Required: [lemmas or techniques needed]

Would you like me to help document these? (yes/no)
```

**If well-documented:**
```
Next recommended sorry to tackle:

[file]:[line] - [theorem_name]
Strategy: [TODO comment text]
Estimated difficulty: [Easy/Medium/Hard]
Priority: [reasoning]

Work on this sorry? Options:
1. Fill it manually (I'll assist with tactics and searches)
2. Dispatch sorry-filler subagent (if available)
3. Skip to next sorry
4. See full list again

Choose: (1/2/3/4)
```

### 6. Assist with Sorry Filling

**If user chooses to fill a sorry:**

a) **Read context:**
```
Reading proof context around line [N]...

Goal: [extract from file]
Available hypotheses: [list from context]
Type of proof needed: [induction/cases/direct/etc]
```

b) **Search for relevant lemmas:**
```
Searching mathlib for relevant lemmas...
```

Use the `/lean4-theorem-proving:search-mathlib` command to find relevant lemmas.

c) **Suggest approach:**
```
Based on the goal and available lemmas:

Approach: [tactic sequence]

Relevant lemmas found:
1. [lemma_name] - [description]
2. [lemma_name] - [description]

Try this approach? (yes/generate-alternatives/search-more)
```

d) **If lean4-sorry-filler subagent available:**
```
The sorry-filler subagent can:
- Generate 2-3 candidate proofs
- Test them with lean_multi_attempt (if MCP available)
- Pick the shortest that compiles

Dispatch subagent to fill this sorry? (yes/no)
```

### 7. Track Progress

**After each filled sorry:**
```
✅ Sorry filled at [file]:[line]!

Verified: Proof compiles ✓

Progress:
  Remaining sorries: [N]
  Completed this session: [M]
  Estimated time saved: [calculation based on difficulty]

Continue to next sorry? (yes/no/take-a-break)
```

## Interactive Mode Features

**When using --interactive flag:**

```
Interactive Sorry Navigator

TUI Commands:
  ↑/↓     - Navigate sorries
  Enter   - View sorry details
  o [n]   - Open file at sorry n in $EDITOR
  f       - Filter by file
  d       - Filter by documented/undocumented
  q       - Quit

Currently showing: [X] sorries in [scope]
```

## Common Workflows

### Workflow 1: First-Time Analysis

```
1. Run analyze-sorries on entire project
2. Document all undocumented sorries
3. Categorize by difficulty
4. Start with Easy sorries for momentum
5. Track progress daily
```

### Workflow 2: Daily Sorry-Filling Session

```
1. Run analyze-sorries to see current state
2. Pick top-priority sorry (usually Easy)
3. Fill sorry with /fill-sorry command
4. Verify with lake build
5. Commit
6. Repeat for 2-3 sorries per session
```

### Workflow 3: PR Preparation

```
1. Run analyze-sorries to get count
2. Document any new sorries added
3. Fill critical-path sorries (blocking features)
4. Leave non-critical sorries for later
5. Update PR description with sorry count and plan
```

## Integration with Other Tools

**With sorry-filler subagent:**
```
Batch-fill multiple similar sorries:
1. Identify pattern (e.g., all use same technique)
2. Dispatch subagent with batch instructions
3. Review results
4. Commit working proofs
```

**With lean-lsp-mcp:**
```
Real-time sorry filling:
1. Navigate to sorry in file
2. Use mcp__lean-lsp__lean_goal to see goal state
3. Use mcp__lean-lsp__lean_multi_attempt for candidates
4. Pick best candidate
```

## Error Handling

**If sorry_analyzer.py fails:**
```
❌ Sorry analysis failed

Error: [error message]

Common causes:
- Not in a Lean project directory
- SessionStart hook didn't stage analyzer (restart session)
- Python not installed (requires Python 3.6+)
- File encoding issues

Try: Ensure you're in project root with Python 3.6+
```

**If no $EDITOR set (interactive mode):**
```
⚠️ $EDITOR not set - cannot open files

Set your editor:
  export EDITOR=code  # for VS Code
  export EDITOR=vim   # for Vim
  export EDITOR=emacs # for Emacs

Then re-run in interactive mode.
```

## Best Practices

✅ **Do:**
- Document every sorry with TODO comment
- Include strategy and required lemmas
- Start with Easy sorries for momentum
- Verify each filled sorry compiles
- Commit filled sorries incrementally

❌ **Don't:**
- Leave sorries undocumented
- Try to fill all sorries at once
- Skip the "Easy" ones thinking they're not important
- Forget to update documentation when strategy changes
- Let sorry count grow unbounded
- Use placeholders in executed commands

## Related Commands

- `/fill-sorry` - Guided sorry filling with tactics and search
- `/search-mathlib` - Find lemmas to help prove sorries
- `/build-lean` - Verify proofs compile after filling sorries
- `/check-axioms` - Verify no axioms were introduced while filling sorries

## References

- [scripts/README.md](../scripts/README.md#sorry_analyzerpy) - Tool documentation
- [SKILL.md](../SKILL.md#phase-3-incremental-filling) - Sorry-filling workflow
- [tactics-reference.md](../references/tactics-reference.md) - Tactic catalog for filling sorries
