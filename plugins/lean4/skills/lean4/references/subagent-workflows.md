# Subagent Workflows for Lean 4 Development

**For Claude Code users:** This guide shows how to leverage subagents to automate mechanical tasks while keeping your main conversation focused on proof strategy.

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

## Agent Types

### Explore Agent (Fast, Lightweight)

**Use for:**
- Quick searches and file discovery
- Running single scripts with straightforward output
- Pattern matching and grepping

**Tools available:** Glob, Grep, Read, Bash

**Cost:** ~Haiku-level tokens

**When to use:**
- "Find all files using MeasurableSpace"
- "Run sorry_analyzer.py and report count"
- "Search mathlib for continuous function lemmas"

### General-Purpose Agent (Thorough, Multi-Step)

**Use for:**
- Complex searches requiring judgment
- Multi-step analysis workflows
- Tasks that need interpretation

**Tools available:** Full toolset including Task

**Cost:** ~Sonnet-level tokens

**When to use:**
- "Search mathlib, evaluate which lemmas apply, recommend best 3"
- "Analyze proof complexity and suggest refactoring priorities with reasoning"
- "Compare multiple proof approaches and explain tradeoffs"

### Specialized Workflows (Integrated)

The lean4 plugin includes internal workflows for complex tasks, orchestrated automatically by `/lean4:autoprover` and `/lean4:golf`.

**What autoprover may delegate:**
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
❌ Dispatch general-purpose agent to run find_golfable.py (misses false-positive filtering)

Task: "Find mathlib lemmas for this sorry"
✅ Dispatch Explore agent to run smart_search.sh (simple delegation)
✅ Use lean_local_search or lean_leansearch LSP tools directly

Task: "Fill all 15 sorries in this file"
✅ Use /lean4:autoprover (batch processing with testing)
❌ Manual iteration in main conversation (inefficient)
```

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

## Automation Scripts + Subagents

### Pattern: Delegate Script Execution

**Instead of this (inefficient):**
```
You: Run $LEAN4_SCRIPTS/sorry_analyzer.py on the whole project

Claude (in main conversation):
[Executes script directly]
[Displays 100 lines of output]
[Consumes 500+ tokens explaining results]
```

**Do this (efficient):**
```
You: Dispatch an Explore agent to run $LEAN4_SCRIPTS/sorry_analyzer.py and report top 5 sorries

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
"Run $LEAN4_SCRIPTS/smart_search.sh 'continuous functions compact spaces' --source=leansearch
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
 1. $LEAN4_SCRIPTS/sorry_analyzer.py src/ --format=json (count sorries)
 2. $LEAN4_SCRIPTS/check_axioms_inline.sh 'src/**/*.lean' (check for non-standard axioms)
 3. Report: Total sorries, any axiom issues, ready to commit?"

[Agent reports back]:
- Sorries: 3 total (all documented with TODO comments)
- Axioms: All 150 declarations use only standard axioms
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
$ $LEAN4_SCRIPTS/sorry_analyzer.py . --interactive

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
 1. Run $LEAN4_SCRIPTS/sorry_analyzer.py src/ and report total count
 2. Run $LEAN4_SCRIPTS/check_axioms_inline.sh 'src/**/*.lean' and report any issues
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
 1. Search mathlib for continuous function lemmas using $LEAN4_SCRIPTS/smart_search.sh
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
 1. Run $LEAN4_SCRIPTS/search_mathlib.sh 'condExp' name in project files (not mathlib)
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

**Scenario:** Running sorry_analyzer.py on a medium project

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
- Agent uses Haiku/fast model (cheap)
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

## Integration with MCP Server

**If Lean MCP server is available:** Prefer MCP tools over scripts.

**Hierarchy:**
1. **MCP server** (best) - Direct integration, no script overhead
2. **Subagent + scripts** (good) - Efficient delegation, batch operations
3. **Direct script execution** (fallback) - When not using Claude Code

**MCP + Subagents workflow:**
```
# Use MCP for interactive proof development
lean_goal(file, line, column)  # See proof state
lean_diagnostic_messages(file)  # Check errors

# Delegate batch operations to subagents
"Dispatch Explore agent to run $LEAN4_SCRIPTS/check_axioms_inline.sh on all changed files"
```

**Why this combination?**
- MCP: Real-time feedback during proof development
- Subagents: Batch verification and analysis tasks
- Best of both: Interactive + Automated

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
| `/lean4:autoprover` | Main workflow - planning, filling, repair |
| `/lean4:checkpoint` | Verified commit with axiom check |
| `/lean4:review` | Read-only quality review |
| `/lean4:golf` | Optimize proofs |
| `/lean4:doctor` | Diagnostics and migration |

**Note:** Individual operations like "search mathlib" or "analyze sorries" are now internal workflows within `/lean4:autoprover` rather than separate commands. This simplifies the UX while preserving all functionality.

### Using LSP Tools Directly

For quick operations, use Lean LSP MCP tools directly:

```
lean_leansearch("continuous function compact")  # Natural language search
lean_loogle("Continuous _ → IsCompact _")       # Type pattern search
lean_goal(file, line)                           # Get goal at position
lean_multi_attempt(file, line, ["simp", "ring"]) # Test tactics
```

### Example: Finding Lemmas

**Scenario:** Need to find lemmas about continuous functions on compact spaces

**Direct approach (preferred):**
```
lean_leansearch("continuous image of compact set is compact")
→ Returns: Continuous.isCompact_image

lean_loogle("Continuous _ → IsCompact _ → IsCompact _")
→ Returns matching type signatures

Alternatives:
- ContinuousOn.isCompact_image (if only continuous on subset)
- IsCompact.image (more general form)
"
```

### Pattern: Script vs Slash Command Decision

**Use script directly (faster, simpler):**
```
"Dispatch Explore agent to:
Run $LEAN4_SCRIPTS/sorry_analyzer.py . --format=text
and report total sorry count"
```

**Use autoprover planning phase (richer workflow):**
```
"Run /lean4:autoprover which will analyze sorries in the planning phase
and show a prioritized list before asking how to proceed"
```

**Key difference:** The autoprover provides interpretation and planning, scripts provide raw data.

## Troubleshooting

### "Agent didn't find what I expected"

**Problem:** Search came back empty or wrong results

**Solutions:**
- Check script arguments - did you pass the right pattern?
- Try different search mode (name vs content vs type)
- Dispatch with more specific instructions
- Fall back to MCP server tools if available

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
