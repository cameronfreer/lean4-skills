# Slash Commands Guide

Quick reference for all interactive slash commands in the lean4-theorem-proving plugin.

## What Are Slash Commands?

Slash commands are interactive workflows you can invoke by typing `/` in Claude Code. They combine multiple scripts and provide guided, step-by-step assistance for common Lean 4 development tasks.

**How to use:**
1. Type `/lean` in Claude Code (autocomplete will show options)
2. Select the command you want
3. Add any required arguments (file paths, search queries)
4. Follow the interactive prompts

## Available Commands

### `/lean4-theorem-proving:search-mathlib [query]`

**Purpose:** Find relevant lemmas in mathlib before proving

**What it does:**
- Searches by name, type pattern, or natural language description
- Tries multiple search strategies automatically (local search, leansearch API, loogle API)
- Evaluates and ranks results
- Provides import paths and type signatures

**Example:**
```
/lean4-theorem-proving:search-mathlib continuity compactness
```

**When to use:**
- Before proving anything (mathlib probably has it!)
- When you know roughly what you need but not the exact lemma name
- To discover related lemmas you didn't know existed

---

### `/lean4-theorem-proving:analyze-sorries`

**Purpose:** Scan project for incomplete proofs and plan systematic filling work

**What it does:**
- Finds all `sorry` statements in your project
- Categorizes by difficulty (easy/medium/hard) based on TODO comments
- Highlights undocumented sorries
- Suggests which ones to tackle first
- Provides statistics by file

**Example:**
```
/lean4-theorem-proving:analyze-sorries
```

**When to use:**
- Starting a sorry-filling session
- Planning proof development work
- Getting overview of project completion status
- Before PR or commit to see remaining work

---

### `/lean4-theorem-proving:fill-sorry [file:line]`

**Purpose:** Get interactive help filling a specific sorry

**What it does:**
- Analyzes the goal and context around the sorry
- Searches mathlib for relevant lemmas
- Suggests tactics based on goal structure
- Generates 2-3 proof approaches
- Tests candidates if MCP is available
- Helps you choose and apply the best approach

**Example:**
```
/lean4-theorem-proving:fill-sorry MyTheorems.lean:142
```

**When to use:**
- Stuck on a specific sorry
- Want multiple proof approaches to choose from
- Need lemma suggestions for a proof
- Want tactic recommendations for a goal

---

### `/lean4-theorem-proving:check-axioms [file]`

**Purpose:** Verify proofs use only standard axioms

**What it does:**
- Checks all declarations in file(s) for axiom usage
- Reports any custom axioms (non-standard)
- Identifies which theorems use problematic axioms
- Suggests elimination strategies
- Standard axioms: `propext`, `quot.sound`, `Classical.choice`

**Example:**
```
/lean4-theorem-proving:check-axioms MyTheorems.lean
```

**When to use:**
- Before committing or creating PR
- After filling sorries (to ensure no axioms introduced)
- When cleaning up proofs for mathlib contribution
- Pre-commit quality check

---

### `/lean4-theorem-proving:build-lean`

**Purpose:** Build project with formatted error analysis

**What it does:**
- Runs `lake build` on project or specific files
- Categorizes errors by type (type mismatch, instance synthesis, etc.)
- Provides actionable debugging hints for each error
- Reports build time and file counts
- Highlights warnings separately

**Example:**
```
/lean4-theorem-proving:build-lean
```

**When to use:**
- After making changes (compile early, compile often!)
- When you get compilation errors and want help debugging
- To verify build before commit
- To see categorized error overview

---

### `/lean4-theorem-proving:golf-proofs [file]`

**Purpose:** Interactively optimize proofs after compilation

**What it does:**
- Finds optimization patterns (let+have+exact, ext chains, simp simplifications)
- Filters false positives (validates let binding usage)
- Shows before/after for each optimization
- Tests each change with `lake build`
- Achieves 30-40% size reduction typically

**Example:**
```
/lean4-theorem-proving:golf-proofs MyFile.lean
```

**When to use:**
- After proofs compile successfully
- When cleaning up code for readability
- Before submitting to mathlib
- To reduce proof length/tokens

**Important:** Only run on stable, compiled files!

---

### `/lean4-theorem-proving:clean-warnings`

**Purpose:** Systematically clean up linter warnings

**What it does:**
- Categorizes warnings by type (unused variables, simp args, deprecated, etc.)
- Fixes by category with priority (safest first)
- Verifies each fix with incremental build
- Reverts on failure
- Tracks progress across categories

**Example:**
```
/lean4-theorem-proving:clean-warnings
```

**When to use:**
- After build succeeds with warnings
- Before committing clean code
- Post-development cleanup
- Pre-PR quality check

**Important:** Only run after project compiles successfully!

---

### `/lean4-theorem-proving:refactor-have [file]`

**Purpose:** Extract long have-blocks into separate helper lemmas

**What it does:**
- Scans file for `have` statements with proofs > 30 lines
- Presents candidates with line numbers and goal types
- Helps determine needed parameters
- Generates helper lemma and updates main proof
- Verifies extraction compiles

**Example:**
```
/lean4-theorem-proving:refactor-have MyTheorems.lean
```

**When to use:**
- Proofs have monolithic have-blocks (30+ lines)
- Want to improve proof readability
- Need to reuse intermediate results
- Main proof structure is obscured by inline proofs

**Note:** This is the inverse of proof golfing's "inline" patterns. Use `/golf-proofs` to inline short have-blocks; use `/refactor-have` to extract long ones.

---

## Command Comparison

| Command | Speed | Interactivity | Best For |
|---------|-------|---------------|----------|
| `search-mathlib` | Fast | Low | Quick lemma lookup |
| `analyze-sorries` | Fast | Low | Project overview |
| `fill-sorry` | Medium | High | Interactive proof development |
| `check-axioms` | Fast | Low | Quality verification |
| `build-lean` | Medium | Low | Compilation + error analysis |
| `golf-proofs` | Slow | High | Proof optimization (batch) |
| `clean-warnings` | Slow | High | Warning cleanup (batch) |
| `refactor-have` | Medium | High | Extract long have-blocks |

## Typical Workflows

### Development Workflow
```
1. /analyze-sorries           # See what needs to be done
2. /fill-sorry [file:line]    # Fill one sorry at a time
3. /build-lean                # Verify it compiles
4. /check-axioms              # Ensure no axioms introduced
5. Commit and repeat
```

### Pre-Commit Quality Check
```
1. /build-lean                # Ensure compilation
2. /refactor-have             # Extract long have-blocks (optional)
3. /clean-warnings            # Clean up warnings
4. /check-axioms              # Verify axiom hygiene
5. /golf-proofs               # Optimize proof size (optional)
6. Commit clean code
```

### Stuck on a Proof
```
1. /search-mathlib [topic]    # Find relevant lemmas
2. /fill-sorry [file:line]    # Get tactic suggestions
3. /build-lean                # Test your changes
4. Iterate until it works
```

## Tips

**Autocomplete:** Just type `/lean` and select from the dropdown - no need to type the full `lean4-theorem-proving:` prefix

**Slash Commands vs Scripts:**
- Slash commands: Interactive, guided workflows with interpretation
- Scripts: Raw data, single operations, when you need full control
- Use slash commands when learning or want guidance
- Use scripts directly when you know exactly what you need

**Combining with Subagents:**
- You can dispatch subagents to run slash commands
- Example: "Dispatch agent to use /search-mathlib and recommend best 3 results"
- See [subagent-workflows.md](skills/lean4-theorem-proving/references/subagent-workflows.md)

## See Also

- [scripts/README.md](scripts/README.md) - Direct script usage
- [SKILL.md](skills/lean4-theorem-proving/SKILL.md) - Core workflow
- [subagent-workflows.md](skills/lean4-theorem-proving/references/subagent-workflows.md) - Delegation patterns
