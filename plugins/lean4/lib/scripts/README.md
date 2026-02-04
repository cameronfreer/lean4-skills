# Lean 4 Theorem Proving Scripts

Automated tools for common Lean 4 workflows. These scripts implement the workflows described in SKILL.md with deterministic reliability.

**All scripts validated on real Lean 4 formalization project (1000+ commits).** See `TESTING.md` for complete test results.

## Scripts Overview

| Script | Purpose | When to Use | Status |
|--------|---------|-------------|--------|
| `search_mathlib.sh` | Find lemmas in mathlib | Before proving something that might exist | ✅ Production |
| `smart_search.sh` | Multi-source search (APIs + local) | Advanced searches, natural language queries | ✅ Production |
| `find_instances.sh` | Find type class instances | Need instance patterns or examples | ✅ Production |
| `find_usages.sh` | Find uses of theorem/lemma | Before refactoring or removing declarations | ✅ Production |
| `suggest_tactics.sh` | Suggest tactics for goal | Stuck on a proof, learning tactics | ✅ Production |
| `minimize_imports.py` | Remove unused imports | Cleanup imports, reduce dependencies | ✅ Production |
| `proof_templates.sh` | Generate proof skeletons | Starting new proofs, learning patterns | ✅ Production |
| `unused_declarations.sh` | Find unused theorems/defs | Code cleanup, identifying dead code | ✅ Production |
| `build_profile.sh` | Profile build performance | Slow builds, optimization needed | ✅ Production |
| `simp_lemma_tester.sh` | Test simp lemma hygiene | Before adding @[simp], debugging loops | ✅ Production |
| `pre_commit_hook.sh` | Pre-commit quality gates | Before every commit, CI/CD integration | ✅ Production |
| `check_axioms_inline.sh` | Verify axiom usage (all declarations) | Before committing, during PR review | ✅ Production |
| `check_axioms.sh` | Verify axiom usage (public API only) | Library files with flat structure | ⚠️ Limited |
| `sorry_analyzer.py` | Extract and report sorries | Planning work, tracking progress | ✅ Production |
| `proof_complexity.sh` | Analyze proof metrics | Refactoring, identifying complex proofs | ✅ Production |
| `dependency_graph.sh` | Visualize theorem dependencies | Understanding proof structure | ✅ Production |
| `find_golfable.py` | Find proof-golfing opportunities | After proofs compile, before final commit | ✅ Production |
| `analyze_let_usage.py` | Detect false-positive optimizations | Before inlining let bindings | ✅ Production |
| `count_tokens.py` | Count tokens in code | Comparing optimization candidates | ✅ Production |

## search_mathlib.sh

**Purpose:** Find existing lemmas, theorems, and definitions in mathlib to avoid reproving standard results.

**Usage:**
```bash
./search_mathlib.sh <query> [search-type]
```

**Search Types:**
- `name` (default) - Search declaration names
- `type` - Search type signatures
- `content` - Full content search (slower but comprehensive)

**Examples:**
```bash
# Find continuous functions and compactness lemmas
./search_mathlib.sh "continuous.*compact" name

# Search for integrability lemmas
./search_mathlib.sh "integrable" content

# Find measurable space instances
./search_mathlib.sh "MeasurableSpace" type
```

**Configuration:**
Set `MATHLIB_PATH` environment variable to override default `.lake/packages/mathlib`

**Output:**
- Matching files with line numbers
- Declaration snippets
- Import suggestions

**Workflow:**
1. Run search before proving anything
2. Check results for existing lemmas
3. Import and use `#check` to verify
4. Save hours by not reproving standard results

---

## check_axioms_inline.sh ✅ **Recommended**

**Purpose:** Verify that theorems use only standard mathlib axioms, identifying any custom axioms that need elimination plans. Works for ALL declarations including namespaces, sections, and private declarations. **Now supports batch mode for multiple files!**

**Usage:**
```bash
./check_axioms_inline.sh <file-or-pattern> [--verbose]
```

**How it works:**
1. Detects namespace from file(s)
2. Temporarily appends `#print axioms` commands
3. Runs Lean and captures output
4. Restores file automatically (safe even if interrupted)
5. Filters out standard axioms
6. Generates summary across all files

**Standard Axioms (Acceptable):**
- `propext` - Propositional extensionality
- `quot.sound` / `Quot.sound` - Quotient soundness
- `Classical.choice` - Axiom of choice

**Examples:**
```bash
# Check single file
./check_axioms_inline.sh MyFile.lean

# Check multiple files (batch mode)
./check_axioms_inline.sh File1.lean File2.lean

# Check all files in directory with glob pattern
./check_axioms_inline.sh "src/**/*.lean"

# Verbose mode (shows all axioms, including standard ones)
./check_axioms_inline.sh MyFile.lean --verbose
```

**Batch Mode Features:**
- Process multiple files in one command
- Summary statistics (total files, declarations, custom axioms)
- Continues on errors, reports all issues at end
- Exit code 1 if any custom axioms or errors found

**Output:**
```
✓ All declarations use only standard axioms

# Or if non-standard axioms found:
⚠ my_theorem uses non-standard axiom: my_custom_axiom
```

**Workflow:**
1. Run before committing new theorems
2. Add elimination plans for any custom axioms
3. Use during PR review to verify axiom hygiene

**Note:** Requires project to build successfully (`lake build`).

---

## check_axioms.sh ⚠️ **Limited - Public API Only**

**⚠️ LIMITATION:** This script only works for declarations that are part of the module's public API. Declarations in namespaces, sections, or marked `private` cannot be checked via external import.

**Recommendation:** Use `check_axioms_inline.sh` instead for regular development files.

**Usage:**
```bash
./check_axioms.sh <file-or-directory> [--verbose]
```

**When to use:**
- Library files with flat (non-namespaced) structure
- Checking public API of published libraries

## sorry_analyzer.py

**Purpose:** Extract all `sorry` statements with context and documentation to track incomplete proofs.

**Usage:**
```bash
./sorry_analyzer.py <file-or-directory> [--format=text|json|markdown] [--interactive] [--include-deps]
```

**Modes:**
- Default: Generate reports in various formats
- `--interactive`: Interactive TUI to browse and navigate sorries
- `--include-deps`: Include `.lake/` directories (dependencies like mathlib). By default, `.lake/` is excluded to avoid reporting 650+ sorries from mathlib.

**Output Formats:**
- `text` (default) - Human-readable terminal output
- `markdown` - Formatted report for documentation
- `json` - Machine-readable for tooling integration

**Examples:**
```bash
# Analyze single file
./sorry_analyzer.py src/DeFinetti/ViaKoopman.lean

# Interactive mode - browse and open sorries
./sorry_analyzer.py . --interactive

# Generate markdown report for entire project
./sorry_analyzer.py src/ --format=markdown > SORRIES.md

# JSON output for CI/CD
./sorry_analyzer.py . --format=json > sorries.json
```

**Interactive Mode Features:**
- Browse sorries grouped by file
- View detailed context for each sorry
- Open files directly in $EDITOR at sorry location
- Navigate between files and sorries

**Extracted Information:**
- Location (file and line number)
- Containing declaration (theorem/lemma/def)
- Documentation (TODO/NOTE comments)
- Context (surrounding code)

**Workflow:**
1. Run after structuring proof (Phase 1)
2. Use `--interactive` to pick next sorry to tackle
3. Monitor progress on sorry elimination
4. Generate reports for project status
5. Use in CI to track completion metrics

**Exit Code:**
- `0` - No sorries found (all proofs complete!)
- `1` - Sorries found (work remaining)

---

## smart_search.sh

**Purpose:** Multi-source theorem search combining local mathlib search with online APIs (LeanSearch, Loogle).

**Usage:**
```bash
./smart_search.sh <query> [--source=leansearch|loogle|mathlib|all]
```

**Sources:**
- `mathlib` (default) - Local ripgrep/grep search, no rate limits
- `leansearch` - Natural language semantic search via leansearch.net (~3 req/30s)
- `loogle` - Type-based search via loogle.lean-lang.org (~3 req/30s)
- `all` - Try all sources (respects rate limits)

**Examples:**
```bash
# Natural language search using LeanSearch API
./smart_search.sh "continuous functions on compact spaces" --source=leansearch

# Type pattern search using Loogle API
./smart_search.sh "(?a -> ?b) -> List ?a -> List ?b" --source=loogle

# Fast local search (no rate limits)
./smart_search.sh "continuous.*compact" --source=mathlib

# Try all sources
./smart_search.sh "Cauchy Schwarz" --source=all
```

**Query Patterns:**
- Natural language: "If there exist injective maps..."
- Type patterns: `(?a -> ?b) -> List ?a -> List ?b`
- Identifiers: "List.sum", "continuous"
- Mixed: "natural numbers. from: n < m, to: n + 1 < m + 1"

**Dependencies:**
- `curl` (for API sources)
- `jq` (optional, for formatted API output)

---

## find_instances.sh

**Purpose:** Find type class instances in mathlib to understand instance patterns and examples.

**Usage:**
```bash
./find_instances.sh <type-class-name> [--verbose]
```

**Searches For:**
- Instance declarations (`instance : TypeClass`)
- Deriving instances (`deriving TypeClass`)
- Implicit instance arguments (in `--verbose` mode)

**Examples:**
```bash
# Find MeasurableSpace instances
./find_instances.sh MeasurableSpace

# Find probability measure instances with verbose output
./find_instances.sh IsProbabilityMeasure --verbose

# Find Fintype instances
./find_instances.sh Fintype
```

**Use Cases:**
- Understanding how to instantiate type classes
- Finding patterns for writing your own instances
- Discovering available instances for a type

---

## proof_complexity.sh

**Purpose:** Analyze proof length and complexity metrics to identify complex proofs for refactoring.

**Usage:**
```bash
./proof_complexity.sh <file-or-directory> [--sort-by=lines|tokens|sorries]
```

**Metrics:**
- Lines per proof
- Estimated token count
- Tactics count
- Presence of sorries

**Examples:**
```bash
# Analyze single file
./proof_complexity.sh MyFile.lean

# Find most complex proofs by line count
./proof_complexity.sh src/ --sort-by=lines

# Find proofs with most sorries
./proof_complexity.sh . --sort-by=sorries
```

**Output:**
- Top 20 most complex proofs
- Summary statistics (averages)
- Size distribution (small/medium/large/huge)
- Sorry count warnings

**Proof Size Categories:**
- Small: ≤10 lines
- Medium: 11-50 lines
- Large: 51-100 lines
- Huge: >100 lines

---

## dependency_graph.sh

**Purpose:** Visualize theorem dependencies within a file to understand proof structure.

**Usage:**
```bash
./dependency_graph.sh <file> [--format=dot|text]
```

**Output Formats:**
- `dot` - GraphViz DOT format for visualization
- `text` (default) - Dependency tree with counts

**Examples:**
```bash
# Text dependency tree
./dependency_graph.sh MyFile.lean

# Generate PNG visualization with graphviz
./dependency_graph.sh MyFile.lean --format=dot | dot -Tpng > deps.png

# View in browser with dot
./dependency_graph.sh MyFile.lean --format=dot | dot -Tsvg > deps.svg
```

**Features:**
- Identifies leaf theorems (no internal dependencies)
- Shows dependency counts per theorem
- Highlights highly coupled theorems
- Helps identify refactoring opportunities

---

## find_usages.sh

**Purpose:** Find all uses of a theorem, lemma, or definition in your Lean project to understand impact before refactoring.

**Usage:**
```bash
./find_usages.sh <identifier> [directory]
```

**Examples:**
```bash
# Find all uses of a theorem
./find_usages.sh exchangeable_iff_contractable

# Search in specific directory
./find_usages.sh measure_eq_of_fin_marginals_eq src/

# Search entire project
./find_usages.sh prefixCylinder .
```

**Features:**
- Auto-detects ripgrep for performance
- Shows context lines before/after usage
- Excludes definition line (shows only actual usages)
- Excludes usages in comments
- Provides summary statistics

**Output:**
- File locations with line numbers
- Context showing how identifier is used
- Total usage count across files

**Use Cases:**
- Before refactoring a theorem
- Understanding theorem dependencies
- Identifying unused definitions
- Impact analysis before API changes

---

## suggest_tactics.sh

**Purpose:** Analyze a proof goal and suggest relevant Lean 4 tactics to try.

**Usage:**
```bash
./suggest_tactics.sh --goal "<goal-text>"
./suggest_tactics.sh <file> <line> [column]
```

**Examples:**
```bash
# Analyze a goal directly
./suggest_tactics.sh --goal "⊢ ∀ n : ℕ, n + 0 = n"

# Analyze goal from file (requires LSP integration)
./suggest_tactics.sh MyFile.lean 42
```

**Pattern Detection:**
- **Equality** (a = b) → suggests `rfl`, `simp`, `ring`, `ext`
- **Universal quantifier** (∀) → suggests `intro`, `intros`
- **Existential quantifier** (∃) → suggests `use`, `refine ⟨x, ?_⟩`
- **Implication** (→) → suggests `intro h`
- **Conjunction** (∧) → suggests `constructor`, `refine ⟨?_, ?_⟩`
- **Disjunction** (∨) → suggests `left`, `right`, `by_cases`
- **Inequality** (<, ≤) → suggests `linarith`, `omega`, `positivity`

**Domain-Specific Suggestions:**
- **Measure theory** → `measurability`, `filter_upwards`, `ae_of_all`
- **Probability** → `haveI : IsProbabilityMeasure`, `condExp_unique`
- **Topology/Analysis** → `continuity`, `fun_prop`
- **Algebra** → `ring`, `field_simp`, `group`, `abel`

**Use Cases:**
- Learning which tactics to try
- Stuck on a proof
- Understanding goal structure
- Quick reference for domain-specific tactics

---

## minimize_imports.py

**Purpose:** Remove unused imports from Lean files to reduce dependencies and improve compilation times.

**Usage:**
```bash
./minimize_imports.py <file> [--dry-run] [--verbose]
```

**Examples:**
```bash
# Analyze and remove unused imports
./minimize_imports.py MyFile.lean

# See what would be removed without changing file
./minimize_imports.py src/Main.lean --dry-run

# Show detailed compilation output
./minimize_imports.py Core.lean --verbose
```

**How It Works:**
1. Extracts all imports from the file
2. Temporarily removes each import one at a time
3. Checks if file still compiles with `lake env lean`
4. Removes imports that don't cause compilation errors
5. Creates backup (.minimize_backup) before modifying

**Safety Features:**
- Creates backup before any modifications
- Restores original on errors
- Verifies minimized file compiles
- Safe even if interrupted (cleanup handled)

**Output:**
```
Analyzing imports in MyFile.lean
Found 12 import(s)

Testing each import (this may take a while)...
  [1/12] Testing: import Mathlib.Data.List.Basic
    → Required ✓
  [2/12] Testing: import Mathlib.Data.Set.Basic
    → Appears UNUSED ✗
  ...

Removed 3 unused import(s)
Backup saved to: MyFile.lean.minimize_backup
```

**Notes:**
- May take several minutes for files with many imports
- Requires project to compile successfully
- Creates `.minimize_backup` file for safety

---

## build_profile.sh

**Purpose:** Profile Lean 4 build times and identify performance bottlenecks in compilation.

**Usage:**
```bash
./build_profile.sh [--clean] [--output=<file>]
```

**Options:**
- `--clean` - Run `lake clean` before building (full rebuild)
- `--output=<file>` - Save profile data to file

**Examples:**
```bash
# Profile current build
./build_profile.sh

# Full clean rebuild with profiling
./build_profile.sh --clean

# Save profile data for later analysis
./build_profile.sh --output=profile_data.txt
```

**Metrics Collected:**
- Total build time
- Per-file compilation time estimates
- Import chain analysis
- Bottleneck identification
- Build performance trends

**Output:**
```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
BUILD PROFILE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Total build time: 125.3s
Files compiled: 42
Average time per file: 2.98s

Top 5 slowest files:
  1. DeFinetti/ViaL2.lean (estimated 12.5s)
  2. Core.lean (estimated 8.3s)
  ...

Recommendations:
  • Consider splitting large files (>500 lines)
  • Review import chains for bottlenecks
```

**Use Cases:**
- Optimizing slow builds
- Identifying which files take longest to compile
- Planning refactoring to improve build times
- Tracking build performance over time

---

## proof_templates.sh

**Purpose:** Generate structured proof skeletons with `sorry` placeholders for common proof patterns.

**Usage:**
```bash
./proof_templates.sh --<type> "<statement>"
```

**Template Types:**
- `--theorem` - General theorem template with structured steps
- `--induction` - Mathematical induction skeleton
- `--cases` - Case analysis template
- `--calc` - Calculation chain template
- `--exists` - Existential proof template

**Examples:**
```bash
# General theorem
./proof_templates.sh --theorem "my_theorem (n : ℕ) : n + 0 = n"

# Induction proof
./proof_templates.sh --induction "∀ n : ℕ, P n"

# Case analysis
./proof_templates.sh --cases "a ∨ b → c"

# Calculation chain
./proof_templates.sh --calc "a = d"

# Existential proof
./proof_templates.sh --exists "∃ x, P x ∧ Q x"
```

**Generated Template Features:**
- Structured `sorry` placeholders with TODO comments
- Strategy hints for each proof step
- Proper indentation and formatting
- Inductive hypothesis tracking (for induction)
- Case labels (for case analysis)

**Example Output (Induction):**
```lean
theorem ∀ n : ℕ, P n := by
  intro n
  induction n with
  | zero =>
    -- Base case: n = 0
    sorry
    -- TODO: Prove base case

  | succ n ih =>
    -- Inductive step: assume P(n), prove P(n+1)
    -- Inductive hypothesis: ih : P(n)
    sorry
    -- TODO: Use ih to prove P(n+1)
    -- Strategy: [Describe how to use ih]
```

**Use Cases:**
- Starting new proofs with proper structure
- Learning proof patterns (induction, cases, etc.)
- Teaching Lean 4 proof techniques
- Quickly scaffolding complex proofs

---

## unused_declarations.sh

**Purpose:** Find unused theorems, lemmas, and definitions in your Lean project to identify dead code.

**Usage:**
```bash
./unused_declarations.sh [directory]
```

**Examples:**
```bash
# Analyze current directory
./unused_declarations.sh

# Analyze specific directory
./unused_declarations.sh src/

# Analyze entire project
./unused_declarations.sh .
```

**Detection Strategy:**
1. Extracts all `theorem`, `lemma`, `def`, `abbrev`, `instance` declarations
2. Counts usages of each declaration across the project
3. Reports declarations with ≤1 usage (definition only, no actual uses)
4. Filters out common false positives (constructors, instances)

**Output:**
```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
RESULTS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Found 3 potentially unused declaration(s):

  ✗ helper_lemma_v1
    Location: src/Utils.lean:42

  ✗ old_approach
    Location: src/Deprecated.lean:15

RECOMMENDATIONS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

For each unused declaration, consider:

1. Remove it - If truly not needed
   ⚠ But check if it's part of public API first!

2. Mark as private - If it's an implementation detail
   private theorem helper_lemma_v1 ...

3. Add to public API - If it should be exported
   Document it properly and mark it as part of the interface

4. Use it - If you forgot to apply it somewhere
```

**Important Notes:**
- May have false positives for exported API and type class instances
- Library files often have many "unused" declarations (expected for public API)
- Always verify before removing declarations
- Use `find_usages.sh <decl>` to double-check specific declarations

**Use Cases:**
- Code cleanup and maintenance
- Identifying dead code before refactoring
- Discovering forgotten helper lemmas
- Cleaning up after major refactoring

---

## simp_lemma_tester.sh

**Purpose:** Test `@[simp]` lemmas for common issues: infinite loops, non-normal LHS, redundancy.

**Usage:**
```bash
./simp_lemma_tester.sh [file-or-directory]
```

**Examples:**
```bash
# Test simp lemmas in single file
./simp_lemma_tester.sh MyFile.lean

# Test all simp lemmas in directory
./simp_lemma_tester.sh src/

# Test entire project
./simp_lemma_tester.sh .
```

**Checks Performed:**

**1. LHS Normalization**
- Detects when LHS has form `f (g x)` (may not be in simp normal form)
- Warns about nested function applications that might not normalize

**2. Infinite Loop Detection**
- Basic pattern detection for loops (simplified check)
- Recommends testing with `simp only [lemma_name]`

**3. Redundancy Detection**
- Looks for simp lemmas with similar LHS patterns
- Suggests manual review for potential conflicts

**Output:**
```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
SIMP LEMMA TESTER
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Found 12 @[simp] lemmas

Check 1: LHS Normalization
  ⚠ my_simp_lemma: LHS may not be in normal form
      theorem my_simp_lemma : f (g x) = ...

Check 2: Potential Infinite Loops
  ✓ No obvious infinite loop patterns detected
  Note: This is a basic check. Test with: simp only [lemma_name]

Check 3: Redundant Lemmas
  ✓ No obvious redundant lemmas detected

RECOMMENDATIONS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Best practices for simp lemmas:

1. LHS in normal form
   • LHS should be irreducible by other simp lemmas
   • Prefer (a + b) + c over a + (b + c)

2. Avoid infinite loops
   • RHS should be simpler than LHS
   • Test with: simp only [your_lemma]

3. Direction matters
   • Simplify towards canonical forms
   • Example: Expand abbreviations → definitions

4. Testing
   • Always test: example : LHS = RHS := by simp [your_lemma]
   • Check it doesn't loop
```

**Limitations:**
- Detection is heuristic-based (not complete semantic analysis)
- Cannot catch all loop conditions
- Manual testing still recommended

**Use Cases:**
- Before adding `@[simp]` attribute to new lemmas
- Debugging simp loops that cause compilation hangs
- Learning best practices for simp lemma design
- Code review for simp hygiene

---

## pre_commit_hook.sh

**Purpose:** Comprehensive pre-commit quality checks to catch issues before committing.

**Usage:**
```bash
./pre_commit_hook.sh [--quick] [--strict]
```

**Options:**
- `--quick` - Skip slow checks (build, import minimization)
- `--strict` - Fail on warnings (not just errors)

**Examples:**
```bash
# Full pre-commit checks
./pre_commit_hook.sh

# Quick mode (skip slow checks)
./pre_commit_hook.sh --quick

# Strict mode (warnings block commit)
./pre_commit_hook.sh --strict
```

**Git Hook Installation:**
```bash
# Install as git pre-commit hook
ln -s "$LEAN4_SCRIPTS/pre_commit_hook.sh" .git/hooks/pre-commit

# Now runs automatically on every commit
git commit -m "..."  # Hook runs automatically
```

**Checks Performed:**

**1. Build Verification** (skipped in quick mode)
- Runs `lake build` to verify project compiles
- Displays compilation errors if build fails

**2. Axiom Usage**
- Runs `check_axioms_inline.sh` on changed `.lean` files
- Verifies only standard axioms are used
- Fails if non-standard axioms detected

**3. Sorry Count**
- Counts `sorry` placeholders in changed files
- Warns if >3 sorries (suggests breaking into smaller commits)
- Reminds to document sorries with TODO comments

**4. Import Cleanup** (skipped in quick mode)
- Checks for unused imports using `minimize_imports.py --dry-run`
- Suggests running cleanup if unused imports found

**5. Simp Lemma Hygiene**
- Runs `simp_lemma_tester.sh` on files with `@[simp]`
- Warns about potential simp issues

**Output:**
```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
PRE-COMMIT QUALITY CHECKS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

[1/5] Building project...
✓ Build successful

[2/5] Checking axiom usage...
✓ All axioms are standard

[3/5] Counting sorries...
⚠ 2 sorry/sorries found
  Make sure they're documented with TODO comments

[4/5] Checking for unused imports...
✓ No unused imports detected

[5/5] Checking simp lemmas...
✓ Simp lemmas look good

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
SUMMARY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

✓ All checks passed!
⚠ 1 warning(s) found

Warnings detected but not blocking commit
Consider fixing them before committing

Proceeding with commit...
```

**Exit Codes:**
- `0` - All checks passed (or warnings in non-strict mode)
- `1` - Errors found or warnings in strict mode (commit blocked)

**Use Cases:**
- Automated quality gates before every commit
- CI/CD integration for pull requests
- Preventing broken commits in shared branches
- Enforcing code quality standards across team

---

## find_golfable.py

**Purpose:** Identify proof optimization opportunities by detecting common patterns that can be simplified (proof golfing).

**⚠️ IMPORTANT:** 93% of detected patterns can be false positives! Use `--filter-false-positives` to reduce noise.

**Usage:**
```bash
./find_golfable.py <file-or-directory> [--patterns <types>] [--verbose] [--recursive] [--filter-false-positives]
```

**Pattern Types:**
- `let-have-exact` - let + have + exact pattern (60-80% reduction, HIGH priority)
- `by-exact` - by-exact wrapper pattern (50% reduction, MEDIUM priority)
- `calc` - Long calc chains (30-50% reduction, MEDIUM priority)
- `constructor` - Constructor branches (25-50% reduction, LOW priority)
- `multiple-haves` - 5+ consecutive haves (10-30% reduction, LOW priority)
- `all` (default) - All patterns

**Examples:**
```bash
# Find all patterns in a file
./find_golfable.py MyFile.lean

# Recommended: Filter out false positives (reduces noise by ~93%)
./find_golfable.py MyFile.lean --filter-false-positives

# Find specific pattern types with filtering
./find_golfable.py src/ --patterns let-have-exact --filter --recursive

# Show code snippets
./find_golfable.py MyFile.lean --verbose

# Analyze all .lean files in directory
./find_golfable.py src/ --recursive
```

**Output:**
```
======================================================================
Found 3 optimization opportunities
======================================================================

1. LET + HAVE + EXACT [HIGH PRIORITY]
   File: MyFile.lean:42
   Lines: 4 | Est. reduction: 60-80%

2. BY EXACT WRAPPER [MEDIUM PRIORITY]
   File: MyFile.lean:78
   Lines: 2 | Est. reduction: 50%

Summary: 1 HIGH, 1 MEDIUM, 1 LOW priority
Expected total reduction: 30-40% with systematic optimization
```

**Pattern Detection:**

**1. let + have + exact (HIGH value)**
```lean
-- ❌ BEFORE (verbose, ~15 tokens)
let x := definition
have h : Property x := by
  intro i
  exact proof
exact result x h

-- ✅ AFTER (direct, ~3 tokens, 80% reduction)
exact result definition proof
```

**2. by exact wrapper (MEDIUM value)**
```lean
-- ❌ BEFORE
theorem foo : P := by
  exact term

-- ✅ AFTER (50% reduction)
theorem foo : P := term
```

**3. Long calc chains (MEDIUM value)**
- Detects calc chains with 4+ steps
- Suggests combining with simp or using direct lemmas
- 30-50% reduction potential

**4. Constructor branches (LOW value)**
- Detects constructor proofs with 6+ branch lines
- Suggests extracting helper lemmas
- 25-50% reduction potential

**5. Multiple haves (LOW value)**
- Detects 5+ consecutive have statements
- Suggests calc chains or direct composition
- 10-30% reduction potential

**Use Cases:**
- After proofs compile, before final commit
- Identifying optimization opportunities in mature code
- Learning which patterns to avoid in new proofs
- Preparing proofs for mathlib contribution (shorter = better)

**Integration with count_tokens.py:**
```bash
# Find opportunities
./find_golfable.py MyFile.lean

# Compare before/after for specific proof
./count_tokens.py --before-file MyFile.lean:42-47 \
                  --after "exact result definition proof"
```

**False Positive Filtering (NEW!):**

The `--filter-false-positives` flag filters out let bindings used ≥3 times, which would actually INCREASE token count if inlined.

**Without filtering (raw patterns):**
- Finds 47 "opportunities" in typical codebase
- 93% are false positives (shouldn't be optimized)
- Wastes time investigating bad candidates

**With filtering (smart filtering):**
- Filters out let bindings used ≥3 times
- Reduces results to ~3-5 high-value targets
- Saves ~73% time by avoiding false positives

**Empirical data:**
- Let bindings used 1-2 times: 100% worth optimizing
- Let bindings used 3-4 times: 40% worth optimizing
- Let bindings used 5+ times: 0% worth optimizing (NEVER inline!)

**Recommendation:** Always use `--filter-false-positives` for let-have-exact pattern search.

**Workflow:**
1. Run after all proofs compile successfully
2. **Use `--filter-false-positives` to reduce noise by 93%**
3. Focus on HIGH priority patterns first (best ROI)
4. Use analyze_let_usage.py for marginal cases
5. Use count_tokens.py to validate reduction estimates
6. Test each optimization to ensure correctness
7. Commit optimizations separately from functional changes

**Inspired by:** ProofOptimizer research (https://proof-optimizer.github.io/)

---

## analyze_let_usage.py

**Purpose:** Analyze let binding usage to detect false-positive optimization candidates and avoid making code LONGER.

**Critical insight:** Inlining a let binding used ≥3 times actually INCREASES token count instead of reducing it.

**Usage:**
```bash
# Analyze all let bindings in file
./analyze_let_usage.py MyFile.lean

# Analyze specific let binding at line
./analyze_let_usage.py MyFile.lean --line 42

# Verbose output with definitions
./analyze_let_usage.py MyFile.lean --verbose

# Analyze directory recursively
./analyze_let_usage.py src/ --recursive
```

**Examples:**
```bash
# Check if let bindings are safe to inline
./analyze_let_usage.py MyFile.lean

# Focus on specific binding
./analyze_let_usage.py CommonEnding.lean --line 531

# Full codebase scan
./analyze_let_usage.py src/ --recursive
```

**Output:**
```
======================================================================
Let Binding Usage Analysis: MyFile.lean
======================================================================

⚠️  HIGH-RISK FALSE POSITIVES (2):
──────────────────────────────────────────────────────────────────────

  μ_map (line 4)
    Used: 4 times (lines: 6, 8, 10, 11)
    Definition: ~17 tokens
    Impact: Would INCREASE by ~43 tokens
    → ⚠️ DON'T INLINE - Multiple uses

✅ SAFE TO OPTIMIZE (1):
──────────────────────────────────────────────────────────────────────

  simple (line 14)
    Used: 1 time(s)
    Impact: Saves ~3 tokens

======================================================================
SUMMARY
======================================================================
  Total let bindings: 4
  ⚠️  Don't inline (used ≥3 times): 2
  ✅ Safe to inline (used ≤1 time): 1
  ⚡ Marginal (used 2 times): 0
  🗑️  Unused: 1

⚠️  WARNING: 2 bindings would INCREASE tokens if inlined!
   These are FALSE POSITIVES for let+have+exact pattern.
```

**Decision Rules:**

**Safe to inline (✅):**
- Let binding used ≤1 time
- Token impact analysis shows savings
- Simple definitions (<10 tokens ideal)

**Don't inline (⚠️):**
- Let binding used ≥3 times
- Would increase token count
- Complex definitions that aid readability

**Marginal cases (⚡):**
- Let binding used exactly 2 times
- Breaking even or small savings
- Requires readability judgment

**Token Impact Calculation:**
```
Current tokens = definition_tokens + (uses × 2)
Inlined tokens = definition_tokens × uses
Savings = current_tokens - inlined_tokens
```

**Example calculation:**
```
let μ_map := Measure.map ... (17 tokens)
Used 4 times

Current: 17 + (4 × 2) = 25 tokens
Inlined: 17 × 4 = 68 tokens
Impact: Would INCREASE by 43 tokens → DON'T INLINE!
```

**Use Cases:**
- Before applying let+have+exact pattern
- Validating find_golfable.py suggestions
- Avoiding the #1 optimization pitfall (93% false positive rate!)
- Understanding why some patterns shouldn't be optimized

**Integration with find_golfable.py:**
```bash
# 1. Find patterns (may include false positives)
./find_golfable.py MyFile.lean --patterns let-have-exact

# 2. Check specific let binding usage
./analyze_let_usage.py MyFile.lean --line 42

# 3. Or use built-in filtering
./find_golfable.py MyFile.lean --filter-false-positives
```

**Key Statistics (from real codebase scan):**
- 93% of detected patterns were false positives
- Let bindings used 5+ times: NEVER worth inlining
- Let bindings used 3-4 times: 60% false positives
- Let bindings used 1-2 times: 100% safe to inline

**Why this matters:**
The #1 optimization mistake is inlining let bindings that are used multiple times. This tool prevents that by analyzing actual usage patterns before you waste time on optimizations that make code worse.

---

## count_tokens.py

**Purpose:** Count tokens in Lean 4 code to compare optimization candidates and measure reduction.

**Usage:**
```bash
# Single code snippet
./count_tokens.py "<code>"

# File range
./count_tokens.py MyFile.lean:10-15

# Compare before/after
./count_tokens.py --before "<code1>" --after "<code2>"

# Compare file ranges
./count_tokens.py --before-file MyFile.lean:10-15 \
                  --after-file MyFile.lean:20-22
```

**Examples:**
```bash
# Count tokens in code snippet
./count_tokens.py "lemma foo := by exact bar"

# Count tokens in file range
./count_tokens.py MyFile.lean:42-47

# Compare before/after optimization
./count_tokens.py \
  --before "let x := def; have h := proof; exact result x h" \
  --after "exact result def proof"

# Compare file ranges
./count_tokens.py \
  --before-file MyFile.lean:42-47 \
  --after-file MyFile.lean:50-50
```

**Output (single count):**
```
Token Count
========================================
Lines:  5
Tokens: 32 (estimated)
Avg:    6.4 tokens/line
```

**Output (comparison):**
```
============================================================
Optimization Comparison
============================================================

BEFORE:
  Lines:  5
  Tokens: 32 (estimated)

AFTER:
  Lines:  1
  Tokens: 6 (estimated)

REDUCTION:
  Lines:  -4 (80.0%)
  Tokens: -26 (81.2%)

✅ Excellent optimization! (>81% reduction)
```

**Token Estimation:**
- Keyword weights (let, have, exact, by, etc.)
- Operator weights (∀, ∃, →, ←, ≤, etc.)
- Identifier counting (words, function names)
- Structure overhead (parentheses, colons)
- Rough approximation for comparison purposes

**Reduction Quality:**
- **Excellent** (>50%): Major simplification, high-value optimization
- **Good** (30-50%): Significant improvement, worth doing
- **Moderate** (10-30%): Minor improvement, lower priority
- **Minimal** (<10%): Possibly not worth the effort

**Use Cases:**
- Validating optimization candidates from find_golfable.py
- Measuring proof simplification impact
- Comparing multiple optimization approaches
- Prioritizing which proofs to optimize (biggest reductions first)
- Learning which patterns save the most tokens

**Workflow with find_golfable.py:**
```bash
# 1. Find optimization opportunities
./find_golfable.py MyFile.lean

# 2. For each opportunity, count tokens before/after
./count_tokens.py --before-file MyFile.lean:42-47 \
                  --after "candidate_optimization"

# 3. Try multiple candidates, compare reductions
./count_tokens.py --before-file MyFile.lean:42-47 \
                  --after "candidate_1"  # 70% reduction

./count_tokens.py --before-file MyFile.lean:42-47 \
                  --after "candidate_2"  # 85% reduction ← better!

# 4. Use best candidate
```

**Limitations:**
- Token counts are rough estimates (not exact Lean tokenization)
- Use for relative comparison, not absolute measurement
- Context-dependent optimizations may not be captured

**Note:** Inspired by ProofOptimizer paper's token-based optimization approach.

---

## Installation

All scripts are executable and self-contained:

```bash
# Make executable (if needed)
chmod +x $LEAN4_SCRIPTS/*.sh $LEAN4_SCRIPTS/*.py

# Run from skill directory or add to PATH
export PATH="$PATH:$LEAN4_SCRIPTS"
```

## Requirements

- **Bash 4.0+** (for shell scripts)
- **Python 3.6+** (for Python scripts: sorry_analyzer.py, minimize_imports.py)
- **Lean 4 project** with `lake` (for check_axioms*.sh, minimize_imports.py)
- **mathlib** in `.lake/packages/mathlib` (for search_mathlib.sh)
- **ripgrep** (optional, recommended for 10-100x performance improvement)

## Integration with Workflows

These scripts implement the systematic approaches from SKILL.md:

**Phase 1: Structure Before Solving**
→ Use `proof_templates.sh` to generate structured proof scaffolding
→ Use `sorry_analyzer.py` to track structured sorries
→ Use `suggest_tactics.sh` to learn which tactics to try

**Phase 2: Helper Lemmas First**
→ Use `search_mathlib.sh` or `smart_search.sh` to find existing helpers
→ Use `find_instances.sh` to discover type class patterns

**Phase 3: Incremental Filling**
→ Use `sorry_analyzer.py --interactive` to pick next sorry
→ Use `suggest_tactics.sh` when stuck on a proof

**Phase 4: Managing Type Class Issues**
→ Use `find_instances.sh` to find instance patterns
→ Use `search_mathlib.sh` to find relevant lemmas

**Before Commit:**
→ Use `pre_commit_hook.sh` for comprehensive quality checks (recommended)
→ Or run individual checks:
  - `check_axioms_inline.sh` to verify axiom hygiene
  - `minimize_imports.py` to clean up unused imports
  - `simp_lemma_tester.sh` to verify simp lemmas
  - `sorry_analyzer.py` to check for undocumented sorries

**After Proofs Compile (Proof Golfing):**
→ Use `find_golfable.py --filter-false-positives` to identify real opportunities (not false positives!)
→ Use `analyze_let_usage.py` to verify let bindings are safe to inline
→ Use `count_tokens.py` to compare optimization candidates
→ Focus on HIGH priority patterns first (60-80% reduction)
→ Test optimizations to ensure correctness
→ Commit optimizations separately from functional changes
→ **STOP when optimization rate drops below 20%** (diminishing returns)

**Before Refactoring:**
→ Use `find_usages.sh` to understand impact
→ Use `dependency_graph.sh` to visualize dependencies
→ Use `proof_complexity.sh` to identify refactoring priorities
→ Use `unused_declarations.sh` to find dead code

**Performance Optimization:**
→ Use `build_profile.sh` to identify build bottlenecks
→ Use `minimize_imports.py` to reduce dependencies

## Contributing

Found a bug or have an enhancement idea?
- Report issues: https://github.com/cameronfreer/lean4-skills/issues
- Submit improvements via PR
- Share your own automation scripts

## License

MIT License - same as parent skill
