# Subagent Workflows for Lean 4 Development

This guide shows how to leverage subagents to automate mechanical tasks while keeping your main conversation focused on proof strategy.

**Host-neutral core.** The parent/worker contract these patterns implement is
[`run-contract/v1`](handoff-contract.md), which binds the **logical roles**, not
processes. On Claude Code the worker is a subagent; on a host without subagent
support the same dispatch and handoff records apply **inline** in the main thread
(see [cycle-engine.md § Run Contract — No-subagent fallback](cycle-engine.md#run-contract-run-contractv1)). The subagent-specific mechanics below are the Claude Code instantiation of that contract.

## Overview

**Core principle:** Delegate mechanical tasks to specialized subagents, keep proof development in main conversation.

**Benefits:**
- **6x token reduction** vs running scripts directly
- **Parallel execution** - subagent runs while you continue working
- **Cleaner conversation** - focus on proof strategy, not script output
- **Consistent patterns** - all scripts designed for subagent delegation

## Quick Reference

**Key takeaways:**

1. **Delegate mechanical tasks** - search, analysis, verification
2. **Keep strategic work** - proof development, design decisions
3. **Use Explore agents** - for most script execution (fast, cheap)
4. **Be specific** - tell agent exactly what to report
5. **Batch operations** - combine related tasks in one dispatch
6. **6x token savings** - measured benefit across typical session

**Remember:** The goal is to keep your main conversation focused on **proof strategy and tactics**, while automating everything else.

## When to Dispatch Subagents

### ✅ Dispatch Subagents For

**Search tasks:**
- Finding mathlib lemmas by keyword or pattern
- Discovering type class instances
- Locating similar proofs or patterns

**Analysis tasks:**
- Proof complexity metrics across files
- Dependency graph generation
- Sorry reports and statistics

**Verification tasks:**
- Checking axioms across multiple files
- Batch compilation verification
- Import consistency checks

**Exploratory tasks:**
- Understanding unfamiliar codebase structure
- Finding all usages of a definition
- Discovering available tactics or notation

### ❌ Keep in Main Conversation

**Proof development:**
- Writing tactics and structuring arguments
- Responding to type checker errors
- Making tactical decisions (which tactic to try next)

**Design decisions:**
- Choosing between proof approaches
- Breaking theorems into subgoals
- Architectural decisions

**Error debugging:**
- Interpreting "failed to synthesize instance" errors
- Understanding type mismatches
- Resolving compilation errors

**Strategic planning:**
- Planning proof outline
- Identifying helper lemmas needed
- Deciding which sorry to tackle next

---

## Agent Types

### Explore Agent (Fast, Lightweight)

**Use for:**
- Quick searches and file discovery
- Running single scripts with straightforward output
- Pattern matching and grepping

**Tools available:** Glob, Grep, Read, Bash

**Cost:** Low (lightweight model)

**When to use:**
- "Find all files using MeasurableSpace"
- "Run lean4-skills-sorry-analyzer and report count"
- "Search mathlib for continuous function lemmas"

### General-Purpose Agent (Thorough, Multi-Step)

**Use for:**
- Complex searches requiring judgment
- Multi-step analysis workflows
- Tasks that need interpretation

**Tools available:** Full toolset including Task

**Cost:** Moderate (full-featured model)

**When to use:**
- "Search mathlib, evaluate which lemmas apply, recommend best 3"
- "Analyze proof complexity and suggest refactoring priorities with reasoning"
- "Compare multiple proof approaches and explain tradeoffs"

### Specialized Workflows (Integrated)

The lean4 plugin includes internal workflows for complex tasks, orchestrated automatically by `/lean4:prove`, `/lean4:autoprove`, and `/lean4:golf`.

**What prove/autoprove may delegate:**
- Deep sorry-filling (when `--deep` enabled and fast path fails)
- Proof repair (compiler-guided fixes)
- Axiom elimination (when custom axioms detected)
- Proof golfing (optional cleanup for verbose proofs)

**What golf may delegate:**
- Proof optimization with safety checks

You do not invoke these directly. See [agent-workflows.md](agent-workflows.md) for workflow details.

**When to use commands vs general subagents:**
```
Task: "Optimize these 5 proofs"
✅ Use /lean4:golf (specialized workflow with safety checks)
❌ Dispatch general-purpose agent to run lean4-skills-find-golfable (misses false-positive filtering)

Task: "Find mathlib lemmas for this sorry"
✅ Dispatch Explore agent to run lean4-skills-smart-search (simple delegation)
✅ Use lean_local_search or lean_leanfinder LSP tools directly

Task: "Fill all 15 sorries in this file"
✅ Use /lean4:prove or /lean4:autoprove (batch processing with testing)
❌ Manual iteration in main conversation (inefficient)
```

## Automation Scripts + Subagents

### Pattern: Delegate Script Execution

**Instead of this (inefficient):**
```
You: Run lean4-skills-sorry-analyzer on the whole project

Claude (in main conversation):
[Executes script directly]
[Displays 100 lines of output]
[Consumes 500+ tokens explaining results]
```

**Do this (efficient):**
```
You: Dispatch an Explore agent to run lean4-skills-sorry-analyzer and report top 5 sorries

Claude (in main conversation):
"I'm dispatching an Explore agent to analyze sorries..."
[Uses Task tool with Explore agent]
[Agent reports back with summary]
"The agent found 47 sorries. Top 5 to tackle:
 1. convergence_proof (line 245) - needs monotone convergence theorem
 2. helper_bound (line 189) - straightforward inequality
 ..."
```

## Example Workflows

### Finding Mathlib Lemmas

**Task:** "I need lemmas about continuous functions on compact spaces"

**Efficient approach:**
```
Claude: "I'm dispatching an Explore agent to search for relevant lemmas..."

[Dispatches with prompt]:
"Run lean4-skills-smart-search 'continuous functions compact spaces' --source=leansearch
 and report the top 3 most relevant results with their import paths"

[Agent reports back]:
1. Continuous.isCompact_range - Mathlib.Topology.Compactness.Compact
2. IsCompact.image_of_continuous - Mathlib.Topology.Compactness.Basic
3. compact_space_image - Mathlib.Topology.Compactness.Compact

Claude: "Perfect! Let's use Continuous.isCompact_range. Let me add the import..."
```

**Token savings:** ~600 tokens (script output + explanation) → ~100 tokens (dispatch + summary)

### Analyzing Proof Complexity

**Task:** "Which proofs should I refactor first?"

**Efficient approach:**
```
Claude: "Let me dispatch an Explore agent to analyze proof complexity..."

[Dispatches with prompt]:
"Analyze proof complexity in src/ by reading files. Report:
 1. Top 10 most complex proofs by line count
 2. How many proofs are >100 lines (huge category)
 3. Any proofs with sorries that are also large"

[Agent reports back]:
Top 10:
1. main_convergence_theorem (245 lines, 2 sorries)
2. helper_l2_bound (180 lines, 0 sorries)
...

Summary: 3 proofs >100 lines, 2 have sorries

Claude: "Let's refactor main_convergence_theorem first. It's large AND has sorries.
Looking at the structure, I can see 3 natural subgoals we can extract..."
```

### Pre-Commit Verification

**Task:** "Ready to commit - verify everything is clean"

**Efficient batch approach:**
```
Claude: "I'm dispatching an Explore agent to run verification checks..."

[Dispatches with prompt]:
"Run the following verification tasks and report summary:
 1. lean4-skills-sorry-analyzer src/ --format=json (count sorries)
 2. lean4-skills-check-axioms-inline 'src/**/*.lean' (check for non-standard axioms)
 3. Report: Total sorries, any axiom issues, ready to commit?"

[Agent reports back]:
- Sorries: 3 total (all documented with TODO comments)
- Axioms: Best-effort top-level scan found no non-standard axioms in scanned declarations
- Ready: Yes, all checks passed

Claude: "Excellent! All verification checks passed. Let's commit with message:
'feat: Complete convergence proof - 3 documented sorries remain'"
```

### Interactive Sorry Selection

**Task:** "What should I work on next?"

**Hybrid approach (user-interactive):**
```
Claude: "Let's use the interactive sorry navigator. This runs on your terminal
so you can browse and select which sorry to tackle."

You (in terminal):
$ lean4-skills-sorry-analyzer . --interactive

[TUI shows]:
Files with sorries:
  [1] src/Convergence.lean (5 sorries)
  [2] src/Helpers.lean (2 sorries)

[You select file 1, then sorry 3]:
Line 245 - theorem convergence_main
  TODO: Need monotone convergence theorem from mathlib

[You press 'o 3' to open in $EDITOR]

You (returning to conversation): "I'm working on the convergence proof at line 245"

Claude: "Great choice! That sorry needs monotone convergence. Let me dispatch an agent
to find the right mathlib lemma..."
```

## Subagent Dispatch Patterns

### Pattern 1: Simple Delegation

**When:** Single script, straightforward task

**Example:**
```
"Dispatch Explore agent to run $LEAN4_SCRIPTS/find_instances.sh MeasurableSpace
 and report how many instances were found"
```

**Template:**
```
"Dispatch Explore agent to run $LEAN4_SCRIPTS/[SCRIPT] [ARGS] and report [WHAT_YOU_NEED]"
```

### Pattern 2: Batch Operations

**When:** Multiple related scripts, combine results

**Example:**
```
"Dispatch Explore agent to:
 1. Run lean4-skills-sorry-analyzer src/ and report total count
 2. Run lean4-skills-check-axioms-inline 'src/**/*.lean' and report any issues
 3. Analyze proofs in src/ and report 5 largest proofs with sorries
 4. Summarize: What's the state of the codebase?"
```

**Template:**
```
"Dispatch Explore agent to:
 1. [TASK 1]
 2. [TASK 2]
 3. [TASK 3]
 4. Summarize: [SYNTHESIS_QUESTION]"
```

### Pattern 3: Iterative Search

**When:** Multi-step search requiring judgment

**Example:**
```
"Dispatch general-purpose agent to:
 1. Search mathlib for continuous function lemmas using lean4-skills-smart-search
 2. Filter results to those mentioning compact spaces
 3. For top 3 results, check their type signatures
 4. Recommend which lemma best fits our use case: proving f(K) is compact when K is compact
 5. Report: Recommended lemma, import path, why it's the best fit"
```

**Template:**
```
"Dispatch general-purpose agent to:
 1. [SEARCH]
 2. [FILTER/EVALUATE]
 3. [DEEPER_ANALYSIS]
 4. [RECOMMEND]
 5. Report: [SPECIFIC_DELIVERABLE]"
```

### Pattern 4: Exploratory Investigation

**When:** Understanding unfamiliar code or patterns

**Example:**
```
"Dispatch Explore agent to investigate how conditional expectation is used in this project:
 1. Run lean4-skills-search-mathlib 'condExp' name in project files (not mathlib)
 2. Read the top 3 files that use it most
 3. Report: What patterns do you see? How is it typically combined with other operations?"
```

**Template:**
```
"Dispatch Explore agent to investigate [TOPIC]:
 1. [FIND_RELEVANT_FILES]
 2. [READ/ANALYZE]
 3. Report: [PATTERNS_OR_INSIGHTS]"
```

## Cost-Benefit Analysis

### Token Economics

**Scenario:** Running lean4-skills-sorry-analyzer on a medium project

**Without subagent (direct execution):**
- Script output: ~500 tokens (100 lines @ 5 tokens/line)
- Claude explanation: ~200 tokens
- **Total: ~700 tokens**
- Uses main conversation tokens (expensive)

**With subagent delegation:**
- Dispatch prompt: ~50 tokens
- Agent summary: ~50 tokens
- Claude response: ~50 tokens
- **Total: ~150 tokens in main conversation**
- Agent uses fast/lightweight model (cheap)
- **Savings: 700 → 150 = 78% reduction**

**Multiplied across a session:** 10 searches = 7000 tokens → 1500 tokens = **5500 tokens saved**

### When NOT to Use Subagents

**Single-file operations:**
```
❌ "Dispatch agent to grep for 'sorry' in MyFile.lean"
✅ Just use Grep tool directly
```

**Immediate tactical decisions:**
```
❌ "Dispatch agent to look at this type error and suggest a tactic"
✅ Interpret error yourself in main conversation
```

**Already have the information:**
```
❌ "Dispatch agent to check if file compiles" (you just saw it compile)
✅ Proceed with next step
```

**Small proofs (<20 lines):**
```
❌ "Dispatch agent to analyze complexity of this 15-line proof"
✅ Just read it directly
```

## Integration with LSP Backends

**Main thread:** Use the [canonical semantic dispatch](../SKILL.md#canonical-semantic-tool-dispatch).
Preserve explicit MCP selection; otherwise prefer `cli_local` after a successful
native doctor. Scripts are the bounded fallback, not the automatic consequence
of MCP absence. Native commands run through Bash; MCP tool names never do.

**Specialized proof workers:** Start from the parent's pre-collected LSP context
([cycle-engine pre-flight](cycle-engine.md#pre-flight-context-for-subagent-dispatch)).
Try the selected backend's canary before reducing capabilities. A usable native
CLI retains goal/diagnostic/trial access even without inherited MCP tools.
Use [operating profiles](../SKILL.md#operating-profiles) for budgets and recovery.
In `cli_local`, skip unavailable remote searches; trials need exact ranges,
candidate JSON and the original source identity, and run sequentially.

**Hierarchy:**
1. **Main thread + selected LSP backend** — direct live inspection.
2. **Worker + selected LSP backend + pre-collected context** — native via Bash
   or explicitly selected MCP; reuse parent context as the starting state.
3. **Worker with no usable live backend** — proof-repair returns no diff;
   sorry-filler-deep/axiom-eliminator use scripts and required file/project gates;
   proof-golfer limits itself to its documented syntactic fallback.
4. **Inline controller** — execute the same workflow when delegation is absent.

**Pre-collected context dispatch pattern:**
```
# Parent uses semantic calls through its selected backend before dispatch.
lean_goal(file, line)                 # Capture goal state
lean_diagnostic_messages(file)        # Capture diagnostics
lean_local_search("keyword")          # Capture local search observations

# Worker receives the results and the selected backend/project instructions.
"Dispatch sorry-filler-deep on Foo.lean:42 with pre-collected context:
 Goal: ⊢ n + m = m + n
 Diagnostics: sorry at line 42
 Search: Nat.add_comm
 Backend: cli_local; project root: /repo; use canonical command dispatch"
```

Keep the existing `run-contract/v1` schema: pass backend/project guidance in the
worker prompt alongside the record; do not add undeclared record fields.
Pre-collected context can become stale, so refresh live observations/source
identity and retain file-baseline guards before editing.

### Known Limitation: MCP in Plugin Subagents

Plugin-defined subagents may fail to inherit MCP connections from their parent
(upstream: anthropics/claude-code#39962). This is an MCP transport limitation;
it does not establish that native LSP is unavailable. Test the native CLI when
appropriate before entering the no-LSP fallback. A worker without Bash cannot
invoke it: return to the caller rather than inventing a usable capability.

**Mitigations:**
- Collect selected-backend LSP context before dispatch and summarize results.
- Keep canaries backend-aware; do not shell-probe or shell-invoke MCP tools.
- For explicitly selected MCP, user-scoped server registration may help tool
  inheritance; if live MCP is essential, keep that work in the main thread.
- Use Read/Grep for source inspection. Scratch compilation, dependency-aware
  file checks and final axiom/project gates remain separate from LSP access.

## Multi-Branch Workflows

When working across multiple branches (e.g., benchmark variants, parallel experiments),
set up **one worktree per branch** at the start:

```bash
git worktree add ../project-branch-a branch-a
git worktree add ../project-branch-b branch-b
```

Each worktree is a full working directory on its own branch. Agents can operate in
different worktrees without interfering.

**Rules:**
- Keep each agent pinned to one worktree
- **Do not use `git stash` to shuttle agent work across branches** — stash/pop cycles
  create merge conflicts, cross-branch contamination, and silent data loss (#66)
- **Checkpoint or commit before cleanup** — never delete a worktree until results are
  committed on the target branch
- **Before any branch switch** in the main checkout: run `/lean4:checkpoint` or
  `git commit` to persist all pending work

**Worktree handoff:** When an agent produces results in a worktree, import them by:
- Committing on that worktree's branch, then merging/cherry-picking
- Extracting a patch (`git diff > patch`) and applying it
- Explicit file copy to the target branch

Never by stashing in one worktree and popping in another.

**Worktree cache:** Each worktree needs its own `.lake` cache — see
[Cold start / fresh worktree](../SKILL.md) for setup.

> **Claude Code note:** `isolation: "worktree"` runs an agent in a temporary git
> worktree automatically. The worktree persists if the agent makes changes — commit
> or import results before cleanup.

When using `run_in_background: true` for agents that edit files, prefer `isolation: "worktree"` to prevent branch-switch or concurrent-edit conflicts.

## Same-File Parallel Dispatch

Never dispatch multiple proof-editing agents that edit the same file in parallel. The Edit tool uses string replacement — if two agents read the same file at dispatch time and edit different regions, the last agent to write silently overwrites the first agent's changes.

**Safe patterns:**
- One agent per file (agent owns all sorrys in that file)
- Sequential dispatch with commits between agents
- `isolation: "worktree"` for agents on different branches

**Unsafe:**
- Two sorry-filler agents targeting different sorrys in the same file
- `git checkout` while a background agent is editing files (destroys work silently — use `isolation: "worktree"` for background agents that edit files)

## Best Practices

### Do

✅ **Dispatch early and often** - Don't wait until script output overwhelms conversation

✅ **Be specific about what you need** - "report top 3 results" not "run and show me everything"

✅ **Use Explore agents for scripts** - They're designed for tool execution

✅ **Batch related tasks** - Combine multiple scripts in one dispatch

✅ **Request summaries** - Ask agent to synthesize, not just dump output

### Don't

❌ **Don't dispatch for trivial tasks** - Use tools directly when simpler

❌ **Don't dispatch for proof tactics** - Keep proof development in main conversation

❌ **Don't forget to specify output** - Agent needs to know what to report back

❌ **Don't dispatch when you have the answer** - Only delegate actual work

❌ **Don't use general-purpose for simple scripts** - Explore agent is faster

## V4 Commands

The lean4 plugin provides these main commands:

| Command | Purpose |
|---------|---------|
| `/lean4:draft` | Skeleton drafting from informal claims |
| `/lean4:formalize` | Interactive synthesis (draft + guided prove) |
| `/lean4:autoformalize` | Autonomous synthesis (draft → prove loop with claim queue) |
| `/lean4:prove` | Guided cycle-by-cycle proving |
| `/lean4:autoprove` | Autonomous multi-cycle proving |
| `/lean4:disprove` | Guided counterexample search with certified refutation |
| `/lean4:checkpoint` | Save point (per-file + project build, best-effort axiom scan, commit) |
| `/lean4:review` | Read-only quality review |
| `/lean4:refactor` | Strategy-level proof simplification |
| `/lean4:golf` | Optimize proofs |
| `/lean4:learn` | Interactive teaching and mathlib exploration |
| `/lean4:diagnose` | Diagnostics and migration |

**Note:** Individual operations like "search mathlib" or "analyze sorries" are now internal workflows within `/lean4:prove` (or `/lean4:autoprove`) rather than separate commands. This simplifies the UX while preserving all functionality.

### Using LSP Tools Directly

For quick operations, use Lean LSP MCP tools directly:

```
lean_leanfinder("continuous function compact")  # Semantic, goal-aware search
lean_loogle("Continuous _ → IsCompact _")       # Type pattern search
lean_goal(file, line)                           # Get goal at position
lean_multi_attempt(file, line, snippets=["simp", "ring"]) # Test tactics
```

### Example: Finding Lemmas

**Scenario:** Need to find lemmas about continuous functions on compact spaces

**Direct approach (preferred):**
```
lean_leanfinder("continuous image of compact set is compact")
→ Returns: Continuous.isCompact_image

lean_loogle("Continuous _ → IsCompact _ → IsCompact _")
→ Returns matching type signatures

Alternatives:
- ContinuousOn.isCompact_image (if only continuous on subset)
- IsCompact.image (more general form)
- lean_leansearch("continuous image of compact set is compact")  # Natural-language fallback
"
```

### Pattern: Script vs Slash Command Decision

**Use script directly (faster, simpler):**
```
"Dispatch Explore agent to:
Run lean4-skills-sorry-analyzer . --format=text
and report total sorry count"
```

**Use prove planning phase (richer workflow):**
```
"Run /lean4:prove which will analyze sorries in the planning phase
and show a prioritized list before asking how to proceed"
```

**Key difference:** The proving commands provide interpretation and planning, scripts provide raw data.

## Troubleshooting

### "Agent didn't find what I expected"

**Problem:** Search came back empty or wrong results

**Solutions:**
- Check script arguments - did you pass the right pattern?
- Try different search mode (name vs content vs type)
- Dispatch with more specific instructions
- Use the selected native or explicit MCP backend when available; treat incomplete native search as incomplete coverage

### "Agent output was too verbose"

**Problem:** Got 50 lines when you needed 5

**Solutions:**
- Be more specific: "report top 3" not "report all"
- Ask for summary: "summarize findings" not "show full output"
- Use filtering: "only report sorries with no TODO comments"

### "Not sure which agent type to use"

**Decision tree:**
```
Is it running a single script?
└─> Yes: Explore agent

Does it require judgment/reasoning?
└─> Yes: General-purpose agent

Is it multi-step with decisions?
└─> Yes: General-purpose agent

Otherwise:
└─> Explore agent (default choice)
```

See `$LEAN4_SCRIPTS/README.md` for complete script documentation.
