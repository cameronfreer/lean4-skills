# Lean 4 Theorem Proving Scripts

Hard-primitive scripts for Lean 4 workflows. These implement functionality that's difficult to replicate inline.

## Scripts Overview

| Script | Purpose | When to Use |
|--------|---------|-------------|
| `sorry_analyzer.py` | Extract and report sorries | Planning work, tracking progress |
| `check_axioms_inline.sh` | Verify axiom usage (all declarations) | Before committing, during PR review |
| `search_mathlib.sh` | Find lemmas in mathlib | Before proving something that might exist |
| `smart_search.sh` | Multi-source search (APIs + local) | Advanced searches, natural language queries |
| `parseLeanErrors.py` | Parse and structure Lean errors | Automated repair loops |
| `solverCascade.py` | Automated tactic cascade | Trying multiple tactics automatically |
| `minimize_imports.py` | Remove unused imports | Cleanup imports, reduce dependencies |
| `find_usages.sh` | Find uses of theorem/lemma | Before refactoring or removing declarations |
| `find_instances.sh` | Find type class instances | Need instance patterns or examples |
| `unused_declarations.sh` | Find unused theorems/defs | Code cleanup, identifying dead code |
| `find_golfable.py` | Find proof-golfing opportunities | After proofs compile, before final commit |
| `analyze_let_usage.py` | Detect false-positive optimizations | Before inlining let bindings |

## Core Scripts

### sorry_analyzer.py

Extract all `sorry` statements with context and documentation.

```bash
# Analyze single file
./sorry_analyzer.py src/File.lean

# Interactive mode - browse and open sorries
./sorry_analyzer.py . --interactive

# JSON output for tooling
./sorry_analyzer.py . --format=json
```

### check_axioms_inline.sh

Verify theorems use only standard mathlib axioms.

```bash
# Check single file
./check_axioms_inline.sh MyFile.lean

# Check multiple files (batch mode)
./check_axioms_inline.sh "src/**/*.lean"
```

**Standard axioms (acceptable):** `propext`, `Quot.sound`, `Classical.choice`

### search_mathlib.sh

Find existing lemmas in mathlib.

```bash
# Search declaration names
./search_mathlib.sh "continuous.*compact" name

# Search type signatures
./search_mathlib.sh "MeasurableSpace" type

# Search content
./search_mathlib.sh "integrable" content
```

### smart_search.sh

Multi-source search combining local search with online APIs.

```bash
# Natural language via LeanSearch
./smart_search.sh "continuous functions on compact spaces" --source=leansearch

# Type pattern via Loogle
./smart_search.sh "(?a -> ?b) -> List ?a -> List ?b" --source=loogle

# Try all sources
./smart_search.sh "Cauchy Schwarz" --source=all
```

### parseLeanErrors.py

Parse Lean compiler errors into structured JSON for repair loops.

```bash
./parseLeanErrors.py error_output.txt
```

### solverCascade.py

Try automated solvers in sequence on a goal (handles 40-60% of simple cases).

```bash
./solverCascade.py context.json File.lean
```

The `context.json` should contain goal info (line, column, goal text).

### minimize_imports.py

Remove unused imports from Lean files.

```bash
# Analyze and remove unused imports
./minimize_imports.py MyFile.lean

# See what would be removed
./minimize_imports.py MyFile.lean --dry-run
```

### find_usages.sh

Find all uses of a declaration.

```bash
./find_usages.sh theorem_name
./find_usages.sh theorem_name src/
```

### find_instances.sh

Find type class instances in mathlib.

```bash
./find_instances.sh MeasurableSpace
./find_instances.sh IsProbabilityMeasure --verbose
```

### unused_declarations.sh

Find unused theorems, lemmas, and definitions.

```bash
./unused_declarations.sh src/
```

### find_golfable.py

Identify proof optimization opportunities.

```bash
# Recommended: filter out false positives
./find_golfable.py MyFile.lean --filter-false-positives
```

### analyze_let_usage.py

Analyze let binding usage to avoid bad optimizations.

```bash
./analyze_let_usage.py MyFile.lean
./analyze_let_usage.py MyFile.lean --line 42
```

## Requirements

- **Bash 4.0+** (for shell scripts)
- **Python 3.6+** (for Python scripts)
- **Lean 4 project** with `lake`
- **mathlib** in `.lake/packages/mathlib` (for search)
- **ripgrep** (optional, 10-100x faster)

## Reference Documentation

For tactic suggestions, proof templates, and simp hygiene best practices, see:
- [tactic-patterns.md](../../skills/lean4/references/tactic-patterns.md)
- [proof-templates.md](../../skills/lean4/references/proof-templates.md)
- [simp-hygiene.md](../../skills/lean4/references/simp-hygiene.md)
