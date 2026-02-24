# Script Testing & Validation

Test results and validation status for Lean 4 scripts.

## Script Status

| Script | Status | Notes |
|--------|--------|-------|
| `sorry_analyzer.py` | ✅ Production Ready | Multi-format output, interactive mode |
| `check_axioms_inline.sh` | ✅ Production Ready | Batch mode, namespace-aware |
| `search_mathlib.sh` | ✅ Production Ready | Pattern search with ripgrep |
| `smart_search.sh` | ✅ Production Ready | Multi-source (LeanSearch, Loogle) |
| `parse_lean_errors.py` | ✅ Production Ready | Structured error output |
| `solver_cascade.py` | ✅ Production Ready | Automated tactic testing |
| `minimize_imports.py` | ✅ Production Ready | Safe with backups |
| `find_usages.sh` | ✅ Production Ready | Ripgrep integration |
| `find_instances.sh` | ✅ Production Ready | Type class search |
| `unused_declarations.sh` | ✅ Production Ready | Dead code detection |
| `find_golfable.py` | ✅ Production Ready | False-positive filtering |
| `analyze_let_usage.py` | ✅ Production Ready | Usage count analysis |
| `find_exact_candidates.py` | ✅ Production Ready | Static exact? candidate finder (pure Python, no Lean) |
| `try_exact_at_step.py` | ⚠️ Experimental | exact? probe via Lean invocation (slow, temp-copy safe) |

## Quick Validation

```bash
# Check all scripts are executable
ls -la $LEAN4_SCRIPTS/*.{sh,py}

# Basic functionality tests (in a Lean project directory)
$LEAN4_SCRIPTS/sorry_analyzer.py . --format=summary
$LEAN4_SCRIPTS/check_axioms_inline.sh src/File.lean
$LEAN4_SCRIPTS/search_mathlib.sh "continuous" name
```

## find_golfable.py Detector Fixtures

Validates `find_apply_exact_chains()` against known positive/negative cases.
Run from the repo root:

```bash
python3 plugins/lean4/lib/scripts/test_apply_exact_chains.py
```

## Reference Documentation

Scripts for tactic suggestions, proof templates, and simp hygiene have been converted to reference documentation:

- [tactic-patterns.md](../../skills/lean4/references/tactic-patterns.md) - Goal-based tactic recommendations
- [proof-templates.md](../../skills/lean4/references/proof-templates.md) - Proof skeleton patterns
- [simp-hygiene.md](../../skills/lean4/references/simp-hygiene.md) - Best practices for `@[simp]` lemmas
