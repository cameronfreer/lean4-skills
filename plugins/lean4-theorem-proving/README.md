# lean4-theorem-proving

Systematic workflows for Lean 4 proof development.

## What You Get

- **Lean LSP integration** - Sub-second feedback vs 30s builds
- **8 slash commands** - Build, fill sorries, repair proofs, golf, check axioms, refactor
- **16 automation scripts** - Search, analysis, verification, refactoring
- **Reference guides** - Tactics, mathlib patterns, domain-specific workflows

## Installation

```bash
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4-theorem-proving
```

See [INSTALLATION.md](../../INSTALLATION.md) for manual installation and LSP setup.

## Commands

| Command | Purpose |
|---------|---------|
| `/build-lean` | Build with formatted error analysis |
| `/fill-sorry [file:line]` | Fill a sorry interactively |
| `/repair-file [file]` | Compiler-guided repair of entire file |
| `/repair-interactive` | Interactive step-by-step proof repair |
| `/golf-proofs [file]` | Optimize proofs (30-40% reduction) |
| `/check-axioms [file]` | Verify axiom hygiene |
| `/analyze-sorries` | Scan project for incomplete proofs |
| `/search-mathlib [query]` | Find mathlib lemmas |
| `/refactor-have [file]` | Inline or extract have-blocks |
| `/clean-warnings` | Clean linter warnings by category |

## Automation Scripts

**Search:** `search_mathlib.sh`, `smart_search.sh`, `find_instances.sh`, `find_usages.sh`

**Analysis:** `proof_complexity.sh`, `dependency_graph.sh`, `build_profile.sh`, `suggest_tactics.sh`

**Verification:** `sorry_analyzer.py`, `check_axioms.sh`, `check_axioms_inline.sh`, `simp_lemma_tester.sh`

**Quality:** `pre_commit_hook.sh`, `unused_declarations.sh`, `minimize_imports.py`, `proof_templates.sh`

See [scripts/README.md](scripts/README.md) for documentation.

## Reference Guides

| Guide | Content |
|-------|---------|
| [lean-phrasebook.md](skills/lean4-theorem-proving/references/lean-phrasebook.md) | Math English to Lean |
| [mathlib-guide.md](skills/lean4-theorem-proving/references/mathlib-guide.md) | Search, imports, naming |
| [tactics-reference.md](skills/lean4-theorem-proving/references/tactics-reference.md) | Comprehensive tactics |
| [domain-patterns.md](skills/lean4-theorem-proving/references/domain-patterns.md) | Analysis, algebra, topology |
| [measure-theory.md](skills/lean4-theorem-proving/references/measure-theory.md) | Conditional expectation |
| [compiler-guided-repair.md](skills/lean4-theorem-proving/references/compiler-guided-repair.md) | APOLLO-inspired repair |
| [proof-golfing.md](skills/lean4-theorem-proving/references/proof-golfing.md) | Proof optimization |
| [proof-refactoring.md](skills/lean4-theorem-proving/references/proof-refactoring.md) | Extract helpers |

## Key Principles

- **Always compile before commit** - `lake build` is your test suite
- **Document every sorry** with strategy and dependencies
- **Search mathlib first** before reproving standard results
- **One change at a time** - fill one sorry, compile, commit

## Optional Add-ons

- **[lean4-subagents](../lean4-subagents/)** - Specialized agents for batch proof optimization
- **[lean4-memories](../lean4-memories/)** - Persistent learning across sessions (requires MCP)

## Bootstrap Hook

On startup, the plugin copies tool scripts to `.claude/tools/lean4/` in your workspace. This is read-only and sandboxed.

## License

MIT License - see [LICENSE](../../LICENSE)

---

Part of [lean4-skills](../../README.md)
