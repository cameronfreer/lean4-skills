# Future Features for lean4-theorem-proving

Creative extensions and enhancements to explore. Organized by category with implementation sketches.

---

## ✅ Recently Implemented

### Compiler-Guided Proof Repair (APOLLO-inspired)

**Status:** ✅ **Implemented** (v3.3.0, 2025-10-28)

**What we built:**
- **lean4-proof-repair agent** - Two-stage repair (Haiku → Sonnet escalation)
- **3 slash commands** - `/repair-file`, `/repair-goal`, `/repair-interactive`
- **Solver cascade** - Automated proof search (rfl → simp → ring → ... → aesop)
- **Error routing** - 10 error patterns → specific repair strategies
- **Structured logging** - NDJSON attempt logs for learning patterns

**Core innovation:** Use compiler feedback to drive targeted fixes with low sampling budgets (K=1), not blind best-of-N resampling.

**Workflow:**
1. Compile → parse structured error (type, location, goal, context)
2. Try solver cascade first (many simple cases, zero LLM cost)
3. If fail → agent repair (Stage 1: Haiku fast, Stage 2: Sonnet precise)
4. Apply minimal patch (1-5 lines), recompile, repeat (max 24 attempts)

**Benefits:**
- Success improves over time with structured logging
- Low sampling budget (K=1) with compiler feedback
- Much more cost-effective than blind best-of-N sampling

**Inspired by:** APOLLO (https://arxiv.org/abs/2505.05758)

**Files:**
- Agent: `plugins/lean4-subagents/agents/lean4-proof-repair.md`
- Commands: `commands/repair-{file,goal,interactive}.md`
- Scripts: `scripts/{parseLeanErrors,solverCascade,repairLoop}.py`
- Config: `config/errorStrategies.yaml`
- Reference: `references/compiler-guided-repair.md`

**Key learnings:**
1. Solver cascade is incredibly effective for simple cases
2. Low-K sampling + compiler feedback beats high-K blind sampling
3. Multi-stage escalation optimizes cost/quality
4. Error-specific routing essential (not one-size-fits-all)
5. Structured logging enables future pattern learning

**Future enhancements:**
- Integration with lean4-memories (learn successful patterns)
- Attempt log analysis tools (discover what works)
- Domain-specific repair strategies (probability, algebra, analysis)

---

## 🎯 High-Impact Extensions

### 1. lean4-proof-archaeologist (Subagent)

**What:** Analyze git history to discover proof evolution patterns and learn successful strategies from project history.

**Use cases:**
- "This sorry was filled 3 different ways before converging on the current proof"
- "Pattern X frequently succeeds for goals of type Y in this codebase"
- "These 5 theorems had similar proof trajectories - extract common lemma?"
- Mine successful proof strategies from project history
- Identify which mathlib lemmas are most effective in practice

**Implementation sketch:**
```markdown
New subagent: plugins/lean4-subagents/agents/lean4-proof-archaeologist.md
- Tools: Bash (git), Read, Grep, Glob, WebFetch
- Model: sonnet-4.5 (pattern recognition requires strategic thinking)
- Thinking: on

Workflow:
1. git log --follow FILE.lean to track file evolution
2. git show COMMIT:FILE.lean for historical snapshots
3. Extract proof diffs for specific theorems
4. Analyze: what strategies were tried? what worked?
5. Build pattern library: goal type → successful tactics/lemmas
6. Report findings with confidence scores

New slash command: /lean4-theorem-proving:proof-archaeology FILE.lean
```

**Priority:** ⭐⭐⭐⭐ (Novel, high learning potential)

---

### 2. lean4-lemma-suggester (Subagent)

**What:** Proactively discover opportunities for helper lemmas by analyzing repeated proof patterns.

**Use cases:**
- "I notice you prove `f (g x) = h x` three times - extract a lemma?"
- Detects repeated proof patterns that should be factored out
- Finds lemmas that would bridge gaps between existing theorems
- Suggests generalizations of existing lemmas

**Implementation sketch:**
```markdown
New subagent: plugins/lean4-subagents/agents/lean4-lemma-suggester.md
- Tools: Read, Grep, Glob, Bash, Edit
- Model: sonnet-4.5 (strategic analysis)
- Thinking: on

Workflow:
1. Parse all theorems in target files
2. Extract proof structure (which lemmas used, proof length)
3. Detect repeated patterns:
   - Same lemma sequence used multiple times
   - Similar goals with different parameters
   - Composition patterns that appear >2 times
4. Generate helper lemma suggestions with:
   - Proposed signature
   - Where it would be used (3+ locations = strong signal)
   - Estimated impact (lines saved, clarity gain)

New slash command: /lean4-theorem-proving:suggest-lemmas [FILE.lean]
- If no file: analyze entire project
- If file: analyze that file + its dependents
```

**Priority:** ⭐⭐⭐⭐⭐ (Addresses real pain point)

---

### 3. lean4-proof-explainer (Subagent)

**What:** Convert formal proofs to natural language explanations at different verbosity levels.

**Use cases:**
- Generate documentation for complex proofs
- Teaching materials from formal code
- Code review assistance (explain what proof does)
- Different audiences: ELI5, undergraduate, expert mathematician

**Implementation sketch:**
```markdown
New subagent: plugins/lean4-subagents/agents/lean4-proof-explainer.md
- Tools: Read, Grep, Glob, WebFetch (for mathlib docs)
- Model: sonnet-4.5 (requires understanding)
- Thinking: on

Workflow:
1. Parse proof structure
2. Classify each step: mechanical vs insight
3. Identify key lemmas and their roles
4. Generate explanation:
   - High-level strategy (2-3 sentences)
   - Step-by-step breakdown
   - Highlight non-obvious moves
5. Adjust verbosity based on flag

New slash command: /lean4-theorem-proving:explain-proof FILE.lean THEOREM_NAME [--level=expert|undergrad|eli5]

Integration point: Add --explain flag to build-lean
  lake build --explain => generates explanations for all new theorems
```

**Priority:** ⭐⭐⭐⭐ (Great for teaching and documentation)

---

## 🔧 Quality-of-Life Tools

### 4. lean4-proof-stylist (Subagent)

**What:** Automated style normalization like rustfmt/prettier for Lean proofs.

**Features:**
- Consistent tactic formatting (semicolon chains vs newlines)
- Project-specific idioms enforcement
- Import organization (alphabetical, grouped by namespace)
- Comment placement standards
- Blank line conventions

**Implementation sketch:**
```markdown
New subagent: plugins/lean4-subagents/agents/lean4-proof-stylist.md
- Tools: Read, Edit, Bash
- Model: haiku-4.5 (mechanical transformations)
- Thinking: off

Config file: .lean-style.toml (project root)
[formatting]
tactic_separator = "newline"  # or "semicolon"
max_line_length = 100
import_style = "grouped"  # or "alphabetical"
blank_lines_between_theorems = 2

[naming]
theorem_prefix = "theorem"  # or "lemma"
private_prefix = "private"

Workflow:
1. Read config or use defaults
2. Parse file structure
3. Apply mechanical transformations:
   - Reformat tactic blocks
   - Organize imports
   - Normalize whitespace
   - Check naming conventions
4. Apply changes (minimal diff)

New slash command: /lean4-theorem-proving:normalize-style FILE.lean [--check-only]
```

**Priority:** ⭐⭐⭐ (Nice to have, especially for teams)

---

### 5. Proof Quality Metrics Dashboard

**What:** Rich quality report integrated into build-lean output.

**Metrics:**
- **Readability score:** variable naming, proof structure clarity
- **Complexity:** nesting depth, number of subgoals
- **Performance:** compilation time, tactic execution time
- **Mathlib usage:** % of proof from mathlib vs custom
- **Comment coverage:** % of complex steps with explanations
- **Axiom hygiene:** any unexpected axioms

**Implementation sketch:**
```markdown
New reference doc: references/quality-metrics.md
  - Defines scoring rubrics
  - Threshold recommendations
  - Improvement suggestions

Enhancement to /lean4-theorem-proving:build-lean:
  After compilation, run analysis:

  📊 Proof Quality Report for MyTheorem.lean

  ✓ Readability: 8.5/10
    - Clear variable names (9/10)
    - Good proof structure (8/10)

  ⚠ Complexity: 6/10
    - 3 nested subgoals (consider helper lemmas)
    - Longest proof: 45 lines (threshold: 30)

  ✓ Performance: 9/10
    - Total compile: 0.8s (good)
    - Slowest tactic: simp [*] (120ms)

  ✓ Mathlib usage: 95%
    - 18 mathlib lemmas, 2 custom lemmas

  ⚠ Comment coverage: 40%
    - 6/15 complex steps need explanation
    - Suggested locations: lines 42, 58, 91...

  ✓ Axiom hygiene: Clean
    - Only standard mathlib axioms

New script: scripts/analyze_proof_quality.py FILE.lean
```

**Priority:** ⭐⭐⭐⭐ (Makes improvement concrete)

---

### 6. Smart Proof Repair on Mathlib Updates

**What:** Automatically detect and suggest fixes when mathlib updates break proofs.

**Features:**
- Detect API changes (renamed lemmas, reordered arguments)
- Suggest mechanical fixes
- Identify semantic changes requiring human review
- Generate migration report

**Implementation sketch:**
```markdown
New hook: hooks/post-lake-update.sh
  Triggered after: lake update

  Workflow:
  1. lake build 2>&1 | tee /tmp/build_errors.txt
  2. If errors contain "unknown identifier":
     - Parse error messages
     - Extract old identifiers
     - Search mathlib changelog for renames
     - Suggest: "FooBar was renamed to Foo.bar"
  3. If errors contain "type mismatch":
     - Check if argument order changed
     - Suggest reordering
  4. Generate migration.md report:

     ## Mathlib Update Migration (2025-10-27)

     **Breaking changes detected:** 12

     ### Mechanical fixes (can auto-apply):
     - Line 42: `continuous_of_foo` → `Continuous.of_foo`
     - Line 58: `measurable_bar` → `Measurable.bar`

     ### Semantic changes (need review):
     - Line 91: `integral_congr` now requires `AEStronglyMeasurable`
       Previous: only needed `AEMeasurable`
       Action: Add stronger hypothesis or prove measurability

     Apply mechanical fixes? [y/N]

New slash command: /lean4-theorem-proving:repair-after-update [--auto-fix]
```

**Priority:** ⭐⭐⭐⭐⭐ (Constant pain point)

---

## 🧪 Advanced Proof Development

### 7. lean4-proof-sketcher (Workflow)

**What:** Write high-level proof outlines in natural language, compile to structured sorries with dependency tracking.

**Syntax:**
```lean
theorem big_result : ComplexProperty := by
  sketch
    "First establish auxiliary property P1 using lemma_a and continuity"
    "Then derive P2 from P1 combined with lemma_b"
    "Show P3 follows by induction on the structure"
    "Finally combine P1, P2, P3 via theorem_c to get the result"
  -- Generates:
  -- have P1 : AuxProp1 := by sorry
  -- have P2 : AuxProp2 := by sorry
  -- have P3 : AuxProp3 := by sorry
  -- exact combine P1 P2 P3 theorem_c
```

**Implementation sketch:**
```markdown
Two-phase implementation:

Phase 1: External tool (Python script)
  scripts/proof_sketcher.py FILE.lean THEOREM_NAME

  Input: Natural language sketch in comments
  Output: Structured sorry scaffolding

  Workflow:
  1. Parse sketch comments
  2. Use LLM to infer types for intermediate goals
  3. Generate have/sorry structure
  4. Track dependencies between steps
  5. Insert into file

Phase 2: Lean 4 syntax extension (if feasible)
  Custom tactic or macro that processes sketch blocks
  Requires: elab, macro, or tactic metaprogramming

New slash command: /lean4-theorem-proving:sketch-proof THEOREM_NAME
  Interactive: asks user for each step description
  Generates scaffolding incrementally
```

**Priority:** ⭐⭐⭐⭐⭐ (Novel, bridges informal/formal beautifully)

---

### 8. Collaborative Multi-Agent Proof Sessions

**What:** Dispatch multiple agents to work on independent subgoals in parallel, then merge results.

**Use case:**
```
You have 5 independent sorries in different theorems:
  - theorem_a (sorry at line 42) - type: algebra
  - theorem_b (sorry at line 58) - type: continuity
  - theorem_c (sorry at line 91) - type: measurability
  - theorem_d (sorry at line 103) - type: equality
  - theorem_e (sorry at line 127) - type: induction

Dispatching 5 lean4-sorry-filler agents in parallel...
Agent 1: ✓ Filled theorem_a using ring
Agent 2: ✓ Filled theorem_b using continuous_of_compose
Agent 3: ✗ Failed theorem_c (escalating to deep)
Agent 4: ✓ Filled theorem_d using rfl
Agent 5: ✓ Filled theorem_e using Nat.rec

Merging results... Done.
4/5 filled. 1 requires deep pass.
```

**Implementation sketch:**
```markdown
Enhancement to /lean4-theorem-proving:fill-sorry:

  New flag: --parallel

  Workflow:
  1. Analyze file: find all sorries
  2. Check independence:
     - Do theorems depend on each other?
     - Build dependency graph
     - Identify independent clusters
  3. Dispatch agents in parallel (one per sorry)
  4. Collect results as they complete
  5. Merge non-conflicting edits
  6. If conflicts: prioritize by success rate
  7. Report summary

Conflict resolution:
  - If two agents edit same theorem: pick successful one
  - If both succeed: pick shorter proof
  - If both fail: escalate to deep pass

Track effectiveness:
  - Which agent types work best for which goal types
  - Learn from success patterns
```

**Priority:** ⭐⭐⭐⭐ (Significant speedup for batch work)

---

### 9. Domain-Specialized Proof Agents

**What:** Create subagent variants deeply tuned for specific mathematical domains.

**Variants:**

#### lean4-probability-specialist
- References: measure-theory.md, probability-patterns.md (new)
- Knows: measure theory type class patterns, martingale tactics, conditioning lemmas
- Preferred tactics: measurability, ae_strongly_measurable, integrable
- Mathlib hotspots: MeasureTheory.*, ProbabilityTheory.*

#### lean4-algebra-specialist
- References: algebra-patterns.md (new), ring-theory.md (new)
- Knows: group theory automation, ring homomorphisms, ideal operations
- Preferred tactics: group, ring, noncomm_ring, abel
- Mathlib hotspots: Algebra.*, GroupTheory.*, RingTheory.*

#### lean4-analysis-specialist
- References: analysis-patterns.md (new), topology-patterns.md (new)
- Knows: limit proofs, convergence, continuity, differentiability
- Preferred tactics: continuity, measurability, tendsto_*, Filter.*
- Mathlib hotspots: Topology.*, Analysis.*, MeasureTheory.Measure.*

**Implementation sketch:**
```markdown
For each domain:

1. New reference doc: references/{domain}-patterns.md
   - Common theorem patterns in this domain
   - Domain-specific tactics
   - Frequently used lemmas
   - Type class considerations
   - Common pitfalls

2. New subagent: plugins/lean4-subagents/agents/lean4-{domain}-specialist.md
   - Same structure as lean4-sorry-filler-deep
   - Model: sonnet-4.5, thinking: on
   - Enhanced with domain reference docs
   - Tuned search queries for domain

3. Router logic in fill-sorry command:
   Analyze goal type → dispatch appropriate specialist

   If goal mentions: Measure, Probability → probability-specialist
   If goal mentions: Group, Ring, Ideal → algebra-specialist
   If goal mentions: Continuous, Limit, Filter → analysis-specialist
   Else: general sorry-filler

Incremental rollout:
- Start with probability-specialist (we have measure-theory.md)
- Add algebra-specialist next (common in mathlib)
- Analysis-specialist third
- Expand to: number theory, combinatorics, category theory...
```

**Priority:** ⭐⭐⭐ (Powerful but requires domain expertise to build)

---

## 📊 Analytics and Learning

### 10. Proof Pattern Mining Across Projects

**What:** Analyze multiple Lean codebases to discover universal proof patterns and underutilized lemmas.

**Data sources:**
- mathlib itself (canonical patterns)
- User's projects (project-specific idioms)
- Public Lean repositories (emerging techniques)

**Outputs:**
- "95% of `Continuous` proofs in mathlib use this 3-step pattern"
- "These 10 powerful lemmas are underutilized (appeared <5 times in 1000+ opportunities)"
- "Pattern X is emerging in recent commits (appeared 15 times in last month)"

**Implementation sketch:**
```markdown
New tool: scripts/mine_proof_patterns.py

Input: List of git repositories
Config: .proof-mining.toml
  [sources]
  mathlib = "~/mathlib4"
  project = "."
  examples = ["~/lean-projects/example1", "~/lean-projects/example2"]

  [analysis]
  min_occurrences = 3
  min_repos = 2

Workflow:
1. Clone/pull all source repos
2. Parse all .lean files in each
3. Extract proof structure:
   - Goal type → tactic sequence
   - Lemmas used → context where used
   - Common compositions (lemma chains)
4. Build pattern database:
   ```json
   {
     "pattern_id": "continuous_compose_pattern_1",
     "goal_type": "Continuous (f ∘ g)",
     "tactic_sequence": ["apply Continuous.comp", "exact hf", "exact hg"],
     "occurrences": 247,
     "repos": ["mathlib", "project_x", "project_y"],
     "success_rate": 0.98,
     "avg_proof_length": 3
   }
   ```
5. Generate reports:
   - Top 50 patterns by frequency
   - Underutilized powerful lemmas
   - Emerging patterns (trending up)

Output: references/mined-patterns.md (auto-generated reference)

Integration: fill-sorry reads mined-patterns.md for suggestions

New slash command: /lean4-theorem-proving:mine-patterns [--update]
```

**Priority:** ⭐⭐⭐⭐ (Genuinely novel, could discover hidden gems)

---

### 11. Interactive Proof Tutor

**What:** Socratic agent that teaches proof techniques through interactive dialogue.

**Example session:**
```
User: /lean4-theorem-proving:tutor-mode

Tutor: Welcome! I'll help you learn Lean proof techniques.
       Let's start with a simple goal. What are you trying to prove?

User: theorem example : ∀ n : ℕ, n + 0 = n

Tutor: Great! Let's break this down. What type of statement is this?
       (Hint: Look at the outermost structure)

User: It's a for-all statement?

Tutor: Exactly right! When you see `∀ x, P x`, what's typically the first
       tactic you use?

User: intro?

Tutor: Perfect! Try adding `intro n` and tell me what goal remains.

User: It becomes `n + 0 = n`

Tutor: Good. Now we have an equality goal. Lean has powerful automation
       for natural number arithmetic. Do you know a tactic that can
       handle simple arithmetic equations?

User: simp?

Tutor: That would work! But there's an even more direct tactic for
       definitional equalities. Try typing `rfl` and see what happens.

User: It worked!

Tutor: Excellent! You just learned that `n + 0 = n` is true by definition
       in Lean. The key insight: always try `rfl` for equations that
       "should be obviously true".

       Ready for a slightly harder example?
```

**Implementation sketch:**
```markdown
New subagent: plugins/lean4-subagents/agents/lean4-proof-tutor.md
- Tools: Read, Grep, WebFetch, mcp__lean-lsp__* (for live goals)
- Model: sonnet-4.5 (requires pedagogical skill)
- Thinking: on (needs to plan teaching strategy)

New reference: references/teaching-strategies.md
  - Socratic method principles
  - Common beginner mistakes and how to address
  - Progression of difficulty levels
  - When to give hints vs full answers

Curriculum structure:
  Level 1: Basic tactics (intro, exact, rfl, apply)
  Level 2: Equality reasoning (rw, simp, ring)
  Level 3: Case analysis (cases, induction, by_cases)
  Level 4: Advanced tactics (conv, calc, have chains)
  Level 5: Domain-specific automation

State tracking:
  - Which tactics student has mastered
  - Which patterns still cause confusion
  - Difficulty level
  - Progress through curriculum

New slash command: /lean4-theorem-proving:tutor-mode [--level=beginner|intermediate|advanced]

Integration with memory MCP:
  - Store student progress across sessions
  - "Welcome back! Last time we worked on induction. Ready to practice more?"
```

**Priority:** ⭐⭐⭐⭐⭐ (Huge value for learning, novel application)

---

### 12. Tactic Tree Visualization

**What:** Generate visual diagrams of proof structure with interactive features.

**Output formats:**
- SVG (for web/papers)
- PDF (for LaTeX documents)
- Interactive HTML (click nodes to see intermediate goals)

**Visual features:**
- Tree structure showing tactic branching
- Color coding:
  - Green: automation (simp, ring, etc.)
  - Blue: mathlib lemmas
  - Yellow: custom lemmas
  - Red: sorries
- Size of nodes: complexity/time
- Annotations: intermediate goals at each node

**Example:**
```
theorem_main
├─ intro x
│  ├─ cases x
│  │  ├─ case zero: [simp] ✓
│  │  └─ case succ:
│  │     ├─ have h1: [custom_lemma] ✓
│  │     └─ rw [h1]; [ring] ✓
└─ done
```

**Implementation sketch:**
```markdown
New script: scripts/visualize_proof_tree.py FILE.lean THEOREM_NAME

Dependencies:
  - graphviz (for layout)
  - pygments (for syntax highlighting)
  - lean-lsp-client (for goal extraction)

Workflow:
1. Parse proof tactic block
2. Build tree structure:
   - Each tactic = node
   - Branching tactics (cases, induction) = multiple children
   - Terminal nodes = complete goals
3. Annotate nodes:
   - Extract intermediate goal at each step (via LSP)
   - Classify tactic type (automation/lemma/manual)
   - Measure complexity (proof state size)
4. Generate output:

   SVG mode:
     graphviz with custom styling

   Interactive HTML mode:
     D3.js tree layout
     Click node → show full goal state
     Hover → show tactic documentation

   PDF mode:
     LaTeX/TikZ for publication quality

New slash command: /lean4-theorem-proving:visualize-proof FILE.lean THEOREM [--format=svg|html|pdf]

Advanced features:
  - Compare two proofs side-by-side
  - Animate proof execution
  - Show performance hotspots (slow tactics highlighted)
```

**Priority:** ⭐⭐⭐ (Great for presentations and understanding)

---

## 🚀 Meta-Level Tools

### 13. Proof Performance Profiler

**What:** Beyond compilation time - analyze runtime characteristics and suggest optimizations.

**Metrics:**
- Tactic execution time (which tactics are slow?)
- Memory usage (large proof states)
- Kernel checks (expensive verification)
- Type class synthesis time
- Automation overhead (`decide`, `norm_num`, heavy `simp`)

**Suggestions:**
- "This `decide` proof takes 5s - consider using `native_decide` or manual proof"
- "Heavy `simp` at line 42 with 150 lemmas - narrow scope or use explicit lemmas"
- "Type class search timeout - add instance hints with `haveI`"

**Implementation sketch:**
```markdown
Enhancement to build-lean with --profile flag

New script: scripts/profile_proofs.sh FILE.lean

Workflow:
1. Run lake build with profiler:
   lake build --profile 2>&1 | tee profile.log

2. Parse profiler output:
   Extract timing data for each declaration

3. Identify hotspots:
   - Tactics taking >1s
   - Type class synthesis failures/retries
   - Large proof states (>10k tokens)

4. Analyze slow tactics:
   For each slow step:
   - What tactic was used?
   - How many simp lemmas active?
   - What's the proof state size?
   - Can it be optimized?

5. Generate report:

   ⚡ Performance Profile for MyProof.lean

   Total compile: 12.3s

   🔥 Hotspots:

   1. Line 42: `decide` (5.2s)
      Problem: Evaluating large decision procedure
      Suggestion: Use `native_decide` or prove manually

   2. Line 58: `simp [*]` (3.1s)
      Problem: 243 active simp lemmas, large context
      Suggestion: Narrow to `simp [lemma1, lemma2, lemma3]`

   3. Line 91: Type class synthesis (2.8s)
      Problem: Searching for `MeasurableSpace (α → β)`
      Suggestion: Add `haveI : MeasurableSpace (α → β) := ...`

   💡 Optimization potential: ~8s (65% reduction)

New slash command: /lean4-theorem-proving:profile-performance FILE.lean
```

**Priority:** ⭐⭐⭐⭐ (Slow builds are frustrating)

---

### 14. Mathlib Contribution Assistant

**What:** Guide users through contributing theorems to mathlib with automated checks and formatting.

**Features:**
- Detect potentially mathlib-worthy theorems
- Check if similar theorem already exists
- Format to mathlib style standards
- Generate proper documentation
- Run mathlib CI checks locally
- Create PR with all requirements

**Implementation sketch:**
```markdown
New subagent: plugins/lean4-subagents/agents/lean4-mathlib-contributor.md
- Tools: Bash, Read, Edit, Grep, WebFetch
- Model: sonnet-4.5 (strategic process)
- Thinking: on

New reference: references/mathlib-contribution-guide.md
  - Naming conventions
  - Documentation requirements (every def, every theorem ≥10 lines)
  - Import organization
  - PR process
  - Common review feedback

Workflow:
1. Analyze theorem for mathlib-worthiness:
   Criteria:
   - General enough (not too specific to one project)
   - Non-trivial (not immediate from existing lemmas)
   - Well-named (follows mathlib conventions)
   - Properly documented
   - In appropriate namespace

2. Search mathlib for duplicates:
   Use smart_search, leansearch, Loogle
   "Is this already in mathlib under a different name?"

3. Format to mathlib standards:
   - Check naming: snake_case, descriptive
   - Add docstring if missing
   - Organize imports (minimal, alphabetical)
   - Run mathlib linters locally

4. Prepare PR:
   - Create branch: mathlib-contrib/theorem_name
   - Copy theorem to appropriate mathlib file
   - Generate commit message (mathlib style)
   - Run CI locally: lake build, lake test
   - Create PR description

5. Pre-submission checklist:
   ✓ Follows naming conventions
   ✓ Has complete documentation
   ✓ No duplicate in mathlib
   ✓ Passes local CI
   ✓ Minimal imports
   ✓ Proper namespace
   ✓ Tests added (if applicable)

New slash command: /lean4-theorem-proving:prepare-mathlib-pr THEOREM_NAME

Interactive prompts:
  - Which mathlib file should this go in?
  - What's the high-level description for the PR?
  - Are there related theorems to mention?
```

**Priority:** ⭐⭐⭐⭐ (Encourages contribution, reduces friction)

---

### 15. Proof Diff Tool

**What:** Compare two proofs of the same theorem to identify best approach or hybrid strategies.

**Use cases:**
- "I proved this two ways - which is better?"
- "Someone else proved the same thing - what's different?"
- "Can I combine the best parts of both proofs?"

**Metrics:**
- Length (lines, characters)
- Readability (variable names, structure)
- Performance (compile time)
- Dependency count (mathlib lemmas used)
- Automation level (% tactic vs manual)

**Implementation sketch:**

New script: `scripts/proof_diff.py PROOF1.lean PROOF2.lean THEOREM_NAME`

**Workflow:**
1. Extract both proofs for the same theorem
2. Parse structure of each
3. Compare metrics:

   📊 Proof Comparison: theorem_example

   |                | Proof A (intro-based) | Proof B (direct)  | Winner |
   |----------------|----------------------|-------------------|--------|
   | Length         | 12 lines             | 5 lines           | B ✓    |
   | Readability    | 8/10                 | 6/10              | A ✓    |
   | Compile time   | 0.3s                 | 0.1s              | B ✓    |
   | Mathlib lemmas | 5                    | 2                 | B ✓    |
   | Automation     | 40%                  | 80%               | B ✓    |

   **Overall:** Proof B is shorter and faster
   **But:** Proof A is more readable and educational

   **Common structure:**
   - Both use continuous_of_compose
   - Both establish measurability first

   **Unique to A:**
   - Explicit have statements (clearer logic flow)
   - Named intermediate results

   **Unique to B:**
   - Uses refine for direct construction
   - More automation with simp

   **Recommended hybrid:**
   ```lean
   theorem example : Result := by
     -- Use B's automation for measurability (faster)
     have meas : Measurable f := by simp [...]
     -- Use A's explicit flow for main proof (clearer)
     have h1 : IntermediateResult := continuous_of_compose ...
     exact combine meas h1
   ```

**New slash command:** `/lean4-theorem-proving:proof-diff FILE1.lean FILE2.lean THEOREM_NAME [--suggest-hybrid]`

**Advanced:** Visual side-by-side diff showing both proof trees with differences highlighted

**Priority:** ⭐⭐⭐ (Useful for learning and optimization)

---

## 🎨 Implementation Priority Ranking

### Tier 1: Maximum Impact, Ready to Build
1. **lean4-lemma-suggester** (⭐⭐⭐⭐⭐) - addresses real pain point
2. **Smart proof repair** (⭐⭐⭐⭐⭐) - constant problem
3. **Proof quality metrics** (⭐⭐⭐⭐) - makes improvement concrete
4. **lean4-proof-sketcher** (⭐⭐⭐⭐⭐) - novel, bridges informal/formal

### Tier 2: High Value, Moderate Effort
5. **Interactive proof tutor** (⭐⭐⭐⭐⭐) - huge for learning
6. **lean4-proof-archaeologist** (⭐⭐⭐⭐) - novel insights
7. **Collaborative multi-agent** (⭐⭐⭐⭐) - significant speedup
8. **Proof performance profiler** (⭐⭐⭐⭐) - slow builds frustrate

### Tier 3: Valuable, Lower Priority
9. **lean4-proof-explainer** (⭐⭐⭐⭐) - great for docs/teaching
10. **Mathlib contribution assistant** (⭐⭐⭐⭐) - reduces friction
11. **Proof pattern mining** (⭐⭐⭐⭐) - genuinely novel
12. **Domain specialists** (⭐⭐⭐) - powerful but needs domain expertise

### Tier 4: Nice to Have
13. **Tactic tree visualization** (⭐⭐⭐) - great for presentations
14. **Proof diff tool** (⭐⭐⭐) - useful for learning
15. **lean4-proof-stylist** (⭐⭐⭐) - quality of life

---

## 🔮 Speculative / Research Ideas

### 16. Machine Learning Integration
- Train models on project's proof patterns
- Suggest next tactic based on goal state
- Predict proof difficulty before attempting

### 17. Proof Synthesis from Examples
- "Here are 3 examples where property holds - generate the general theorem"
- QuickCheck-style testing → proof generation

### 18. Natural Language → Formal Pipeline
- Full theorem statements in English
- Auto-formalize to Lean with uncertainty markers
- Interactive refinement loop

### 19. Proof Repair from Counter-Examples
- When proof fails, generate counter-examples
- Use counter-examples to suggest fixes
- "Your proof breaks when x = 0. Add hypothesis x ≠ 0?"

### 20. Cross-Project Proof Reuse
- "This theorem in project A looks similar to your goal"
- Suggest adaptations
- Build library of transferable proof patterns

---

## 📝 Notes on Implementation

**General principles:**
- Start with standalone scripts (Python/Bash) before subagents
- Use existing infrastructure (bootstrap hooks, LSP, search tools)
- Build reference docs first, then agents that use them
- Incremental rollout: prototype → test → refine → integrate

**Resource requirements:**
- Tier 1 features: Primarily tooling, minimal model cost
- Tier 2 features: More model usage, still reasonable
- Tier 3 features: Heavier model usage or complex infrastructure
- Research ideas: Experimental, may need external resources

**Maintenance considerations:**
- Features that depend on mathlib structure need update monitoring
- LSP integrations need versioning awareness
- Generated docs need clear "auto-generated" markers
- Learned patterns need periodic refresh

---

## 🤝 Contribution Welcome

These ideas are sketches, not specifications. Contributions of:
- Prototype implementations
- Alternative approaches
- Additional creative features
- Real-world usage feedback

...are all welcome!

---

*Generated: 2025-10-27*
*Plugin version: lean4-theorem-proving 3.2.0*
