# lean4-theorem-proving

Systematic workflows for Lean 4 proof development.

## Overview

This skill teaches Claude how to develop formal proofs in Lean 4 using battle-tested workflows from real formalization projects. It provides systematic approaches, automation tools, and domain-specific patterns for measure theory, probability, and algebra.

## What You Get

### Battle-Tested Proof Development System

**4-Phase Workflow:**
- Structure before solving, helper lemmas first, incremental filling, type class management

**7 Interactive Slash Commands:**
- Search mathlib, analyze sorries, fill proofs, check axioms, build with error analysis, optimize proofs, clean warnings

**16 Automation Scripts:**
- Search, analysis, verification, and refactoring tools (see [detailed list](#automation-scripts))

**Comprehensive Reference Guides:**
- Lean phrasebook, mathlib guide, tactics reference, domain patterns, proof golfing, and more

**Optional Add-ons:**
- **lean4-memories plugin** - Persistent project-specific learning across sessions (experimental)
- **lean4-subagents plugin** - Autonomous agents for batch proof optimization and sorry-filling (experimental)


## Installation

See [INSTALLATION.md](../../INSTALLATION.md) for installation instructions.

## Usage

### Automatic Activation

Claude automatically uses this skill when you:
- Work on `.lean` files
- Mention Lean 4, theorem proving, or formal verification
- Prove theorems or manage sorries/axioms
- Ask about mathlib or type class issues

No manual invocation needed!

### Key Principles

- ✅ **Always compile before commit** (`lake build` is your test suite)
- ✅ **Document every sorry** with strategy and dependencies
- ✅ **Search mathlib first** before reproving standard results
- ✅ **Eliminate axioms systematically** with documented plans
- ✅ **One change at a time** - fill one sorry, compile, commit

### Slash Commands

Interactive workflows you can invoke by typing `/lean` in Claude Code (autocomplete will show available commands).

| Command | Purpose |
|---------|---------|
| `/lean4-theorem-proving:search-mathlib [query]` | Find mathlib lemmas before proving |
| `/lean4-theorem-proving:analyze-sorries` | Scan project for incomplete proofs |
| `/lean4-theorem-proving:fill-sorry [file:line]` | Get interactive help filling a sorry |
| `/lean4-theorem-proving:check-axioms [file]` | Verify axiom hygiene |
| `/lean4-theorem-proving:build-lean` | Build with formatted error analysis |
| `/lean4-theorem-proving:golf-proofs [file]` | Optimize proofs (30-40% reduction) |
| `/lean4-theorem-proving:clean-warnings` | Clean linter warnings by category |

➡️ **[Full Commands Guide](COMMANDS.md)** - Detailed documentation with examples and workflows

## Automation Scripts

The plugin includes 16 automation scripts organized by category:

**Search (4 scripts):**
- `search_mathlib.sh` - Find lemmas in mathlib by name, type, or content
- `smart_search.sh` - Multi-source search (mathlib + APIs)
- `find_instances.sh` - Locate type class instances
- `find_usages.sh` - Track theorem usage across project

**Analysis (4 scripts):**
- `proof_complexity.sh` - Analyze proof metrics (lines, tactics, tokens)
- `dependency_graph.sh` - Visualize theorem dependencies
- `build_profile.sh` - Profile build performance and bottlenecks
- `suggest_tactics.sh` - Get tactic suggestions for goals

**Verification (4 scripts):**
- `sorry_analyzer.py` - Extract and track sorries with context
- `check_axioms.sh` - Verify axiom usage (external import method)
- `check_axioms_inline.sh` - Verify axiom usage (inline method)
- `simp_lemma_tester.sh` - Test `@[simp]` lemmas for issues

**Quality & Refactoring (4 scripts):**
- `pre_commit_hook.sh` - Comprehensive quality gates
- `unused_declarations.sh` - Find dead code
- `minimize_imports.py` - Remove unused imports
- `proof_templates.sh` - Generate proof skeletons

➡️ **[Scripts Documentation](scripts/README.md)** | **[Testing Report](scripts/TESTING.md)**

## Reference Guides

**Core Workflow:**
- [SKILL.md](skills/lean4-theorem-proving/SKILL.md) - Main skill document (loaded automatically)

**Comprehensive References:**
- [lean-phrasebook.md](skills/lean4-theorem-proving/references/lean-phrasebook.md) - Mathematical English to Lean translations
- [mathlib-guide.md](skills/lean4-theorem-proving/references/mathlib-guide.md) - Search strategies, imports, naming conventions
- [mathlib-style.md](skills/lean4-theorem-proving/references/mathlib-style.md) - Mathlib style conventions and formatting
- [tactics-reference.md](skills/lean4-theorem-proving/references/tactics-reference.md) - Comprehensive tactics catalog
- [calc-patterns.md](skills/lean4-theorem-proving/references/calc-patterns.md) - Calc chain patterns and simp optimization
- [domain-patterns.md](skills/lean4-theorem-proving/references/domain-patterns.md) - Math domain-specific patterns
- [measure-theory.md](skills/lean4-theorem-proving/references/measure-theory.md) - Sub-σ-algebras and conditional expectation
- [instance-pollution.md](skills/lean4-theorem-proving/references/instance-pollution.md) - Avoiding instance pollution when working with multiple typeclass instances
- [compilation-errors.md](skills/lean4-theorem-proving/references/compilation-errors.md) - Error debugging and solutions
- [sorry-filling.md](skills/lean4-theorem-proving/references/sorry-filling.md) - Systematic sorry filling workflows
- [axiom-elimination.md](skills/lean4-theorem-proving/references/axiom-elimination.md) - Axiom elimination strategies
- [proof-golfing.md](skills/lean4-theorem-proving/references/proof-golfing.md) - Simplifying proofs after compilation
- [proof-refactoring.md](skills/lean4-theorem-proving/references/proof-refactoring.md) - Breaking monolithic proofs into helpers
- [compiler-guided-repair.md](skills/lean4-theorem-proving/references/compiler-guided-repair.md) - APOLLO-inspired automated repair
- [lean-lsp-server.md](skills/lean4-theorem-proving/references/lean-lsp-server.md) - Lean LSP server quick reference (Claude Code users)
- [lean-lsp-tools-api.md](skills/lean4-theorem-proving/references/lean-lsp-tools-api.md) - Lean LSP tools detailed API (Claude Code users)
- [subagent-workflows.md](skills/lean4-theorem-proving/references/subagent-workflows.md) - Subagent delegation patterns (Claude Code users)

## When to Use

**Perfect for:**
- Formalizing mathematical theorems (analysis, algebra, topology)
- Working with measure theory and probability
- Contributing to mathlib
- Managing complex proof development
- Converting axioms to proven lemmas
- Dealing with type class inference issues

**Especially helpful when:**
- Starting a new Lean formalization project
- Learning Lean 4 from Lean 3 or other proof assistants
- Stuck with type class synthesis errors
- Managing multiple interrelated proofs
- Working on real analysis, probability, or abstract algebra

## Contents

```
lean4-theorem-proving/
├── README.md                      # This file
├── COMMANDS.md                    # Slash commands guide
├── commands/                      # Slash command definitions
│   ├── search-mathlib.md          # Search mathlib lemmas
│   ├── analyze-sorries.md         # Analyze incomplete proofs
│   ├── fill-sorry.md              # Fill sorries interactively
│   ├── check-axioms.md            # Verify axiom hygiene
│   ├── build-lean.md              # Build with error analysis
│   ├── golf-proofs.md             # Optimize proofs
│   └── clean-warnings.md          # Clean linter warnings
├── scripts/                       # 16 automation tools
│   ├── README.md                  # Scripts documentation
│   ├── TESTING.md                 # Comprehensive validation report
│   ├── search_mathlib.sh          # Find mathlib lemmas
│   ├── smart_search.sh            # Multi-source search
│   ├── find_instances.sh          # Type class instances
│   ├── find_usages.sh             # Usage tracking
│   ├── sorry_analyzer.py          # Sorry extraction
│   ├── check_axioms.sh            # Axiom verification (external)
│   ├── check_axioms_inline.sh     # Axiom verification (inline)
│   ├── proof_complexity.sh        # Proof metrics
│   ├── dependency_graph.sh        # Dependency visualization
│   ├── build_profile.sh           # Build profiling
│   ├── suggest_tactics.sh         # Tactic suggestions
│   ├── proof_templates.sh         # Proof scaffolding
│   ├── unused_declarations.sh     # Dead code detection
│   ├── simp_lemma_tester.sh       # Simp hygiene
│   ├── pre_commit_hook.sh         # Quality gates
│   └── minimize_imports.py        # Import minimization
└── skills/lean4-theorem-proving/  # Skill content
    ├── SKILL.md                   # Core workflow (loaded by Claude)
    └── references/                # Detailed guides (17 files)
        ├── lean-phrasebook.md     # Math English to Lean
        ├── mathlib-guide.md       # mathlib integration
        ├── mathlib-style.md       # Mathlib style conventions
        ├── tactics-reference.md   # Tactics catalog
        ├── calc-patterns.md       # Calc chain patterns
        ├── domain-patterns.md     # Math patterns
        ├── measure-theory.md      # Sub-σ-algebras, conditional expectation
        ├── instance-pollution.md  # Typeclass instance pollution
        ├── compilation-errors.md  # Error solutions
        ├── sorry-filling.md       # Sorry filling workflows
        ├── axiom-elimination.md   # Axiom elimination strategies
        ├── proof-golfing.md       # Proof simplification
        ├── proof-refactoring.md   # Breaking monolithic proofs into helpers
        ├── compiler-guided-repair.md # APOLLO-inspired automated repair
        ├── lean-lsp-server.md     # LSP quick reference (Claude Code)
        ├── lean-lsp-tools-api.md  # LSP API reference (Claude Code)
        └── subagent-workflows.md  # Subagent patterns (Claude Code)
```

## Examples from Real Projects

This skill was developed from real-world Lean 4 formalization work:

**Project:** de Finetti theorem formalization (1000+ commits, 22 files)

**Patterns extracted:**
- π-system uniqueness for measure equality
- Conditional expectation via integral identity
- Type class instance management for sub-σ-algebras
- Systematic axiom elimination (75 axioms → 6 sorries → 0)

**Scripts validated on:**
- Exchangeability formalization
- All 16 scripts tested on real codebase
- See [scripts/TESTING.md](scripts/TESTING.md) for validation report

## Requirements

- **Claude Code 2.0.13+** (for marketplace installation), OR
- **Claude.ai Pro/Max/Team/Enterprise** (for web/API), OR
- **Just Claude** (for CLAUDE.md method)
- (Optional) Lean 4 installed for working on Lean projects

## FAQ

### How does this work with the lean4-memories plugin?

The **lean4-memories plugin** (experimental) provides a skill that adds persistent learning across sessions using MCP memory server integration. This skill (lean4-theorem-proving) works standalone and provides all core functionality.

**Use together:**
- lean4-theorem-proving provides general workflows and patterns
- lean4-memories adds project-specific context that persists across sessions
- Example: lean4-memories can remember "in this project, we always use π-system arguments for measure equality"

See [lean4-memories/README.md](../lean4-memories/README.md) for details.

### How does this work with the lean4-subagents plugin?

The **lean4-subagents plugin** (experimental) provides three specialized subagents for automating mechanical Lean 4 tasks:

**Specialized subagents:**
- `lean4-proof-golfer` - Systematically optimize proofs (works with `/golf-proofs`)
- `lean4-sorry-filler` - Fill sorries using mathlib search (works with `/fill-sorry`)
- `lean4-axiom-eliminator` - Eliminate axioms systematically (works with `/check-axioms`)

**Use together:**
- lean4-theorem-proving provides workflows and slash commands
- lean4-subagents provides autonomous agents that execute those workflows in batch
- Example: "Dispatch lean4-sorry-filler to fill all 15 sorries in this file"

This skill works standalone. lean4-subagents is optional for batch automation.

See [subagent-workflows.md](skills/lean4-theorem-proving/references/subagent-workflows.md) for delegation patterns.

### Do I need all 16 scripts?

No! Scripts are organized by use case:
- **Daily use:** search_mathlib.sh, sorry_analyzer.py, suggest_tactics.sh
- **Quality gates:** pre_commit_hook.sh, check_axioms_inline.sh
- **Specific tasks:** All others (use as needed)

### Can I use just the SKILL.md without scripts?

Yes! The SKILL.md provides the core workflow. Scripts are optional automation tools.

### How is this different from Claude's general Lean knowledge?

Claude has general Lean knowledge from training. This skill provides:
- **Specific workflows** (structure before solve, one sorry at a time)
- **Project patterns** (type class management, mathlib integration)
- **Quality standards** (compile before commit, document sorries)
- **Automation tools** (16 scripts for common tasks)

It's like having a Lean 4 expert mentor coaching Claude.

## Technical Details

### Bootstrap Hook

This plugin includes a `SessionStart` hook (`hooks/bootstrap.sh`) that runs once when Claude Code starts.

**What it does:**
1. Finds Python interpreter (`python3` or `python`)
2. Copies 8 tool scripts to `.claude/tools/lean4/` in your workspace
3. Sets environment variables for the session

**Why this is safe:**
- Read-only operations (only copies files, doesn't modify your code)
- Runs in sandboxed environment
- Only copies known tool scripts (no arbitrary code execution)
- Fails gracefully if Python is not installed
- No network access, no file modification, no git operations

**Scripts staged to `.claude/tools/lean4/`:**
`sorry_analyzer.py`, `search_mathlib.sh`, `smart_search.sh`, `check_axioms.sh`, `find_golfable.py`, `analyze_let_usage.py`, `count_tokens.py`, `suggest_tactics.sh`

This staging approach allows slash commands to reference scripts reliably without triggering Claude Code's parameter substitution security filter.

### Optional CLI Helpers

The skills work without external tools, but installing **`ripgrep`** and **`timeout`** improves performance:
- **ripgrep:** Much faster searches (required for Lean LSP's `lean_local_search`)
- **timeout:** Reliably aborts long-running processes

See [INSTALLATION.md](../../INSTALLATION.md#optional-cli-helpers-ripgrep--timeout) for platform-specific installation instructions.

## Contributing

Contributions welcome! See [main README](../README.md#contributing) for guidelines.

**Ways to contribute:**
- Share additional proof patterns
- Add domain-specific tactics
- Submit examples from successful projects
- Report issues or unclear guidance

## License

MIT License - see [../LICENSE](../LICENSE)

## Related Resources

**Official Lean 4:**
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

**Claude Skills:**
- [Claude Skills Documentation](https://www.anthropic.com/news/skills)
- [Main Repository](../README.md)

---

Part of [lean4-skills](../README.md) - Lean 4 Skills for Claude
