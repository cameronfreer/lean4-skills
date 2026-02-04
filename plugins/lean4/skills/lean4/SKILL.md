---
name: lean4
description: Use when working with Lean 4 (.lean files), writing mathematical proofs, seeing "failed to synthesize instance" errors, managing sorry/axiom elimination, or searching mathlib for lemmas - provides build-first workflow, haveI/letI patterns, compiler-guided repair, and LSP integration
---

# Lean 4 Theorem Proving

## Core Principle

**Build incrementally, structure before solving, trust the type checker.** Lean's type checker is your test suite.

**Success = `lake build` passes + zero sorries + zero custom axioms.** Theorems with sorries/axioms are scaffolding, not results.

## Quick Reference

| **Resource** | **What You Get** | **Where to Find** |
|--------------|------------------|-------------------|
| **Main Command** | Planning-first autoprover with guardrails | `/lean4:autoprover` |
| **Automation Scripts** | 19 tools for search, verification, refactoring, repair | `$LEAN4_SCRIPTS/` directory |
| **Subagents** | 5 specialized agents for batch tasks | Plugin `agents/` directory |
| **LSP Server** | 30x faster feedback with instant proof state (optional) | [lean-lsp-server.md](references/lean-lsp-server.md) |
| **Reference Files** | 19 detailed guides (phrasebook, tactics, patterns, errors, repair, performance) | [List below](#reference-files) |

## When to Use

Use for ANY Lean 4 development: pure/applied math, program verification, mathlib contributions.

**Critical for:** Type class synthesis errors, sorry/axiom management, mathlib search, measure theory/probability work.

## Tools & Workflows

**Primary entry point:** `/lean4:autoprover` - planning-first agentic loop with guardrails.

**Supporting commands:**
- `/lean4:checkpoint` - Safe commit checkpoint
- `/lean4:review` - Read-only code review
- `/lean4:doctor` - Diagnostics and migration help

**Automation scripts** in `$LEAN4_SCRIPTS/`:
- `sorry_analyzer.py` - Discover and prioritize sorries
- `smart_search.sh` - Mathlib lemma search with fallbacks
- `check_axioms.sh` - Verify axiom usage
- See `$LEAN4_SCRIPTS/README.md` for complete documentation

**Lean LSP Server** (optional) provides 30x faster feedback with instant proof state and parallel tactic testing. See [lean-lsp-server.md](references/lean-lsp-server.md) for setup and workflows.

**Subagent delegation** (Claude Code users) enables batch automation. See [subagent-workflows.md](references/subagent-workflows.md) for patterns.

## Build-First Principle

**ALWAYS compile before committing.** Run `lake build` to verify. "Compiles" ≠ "Complete" - files can compile with sorries/axioms but aren't done until those are eliminated.

## The 4-Phase Workflow

1. **Structure Before Solving** - Outline proof strategy with `have` statements and documented sorries before writing tactics
2. **Helper Lemmas First** - Build infrastructure bottom-up, extract reusable components as separate lemmas
3. **Incremental Filling** - Fill ONE sorry at a time, compile after each, commit working code
4. **Type Class Management** - Add explicit instances with `haveI`/`letI` when synthesis fails, respect binder order for sub-structures

## Finding and Using Mathlib Lemmas

**Philosophy:** Search before prove. Mathlib has 100,000+ theorems.

Use `$LEAN4_SCRIPTS/smart_search.sh`, LSP server search tools, or automation scripts. See [mathlib-guide.md](references/mathlib-guide.md) for detailed search techniques, naming conventions, and import organization.

## Essential Tactics

**Key tactics:** `simp only`, `rw`, `apply`, `exact`, `refine`, `by_cases`, `rcases`, `ext`/`funext`. See [tactics-reference.md](references/tactics-reference.md) for comprehensive guide with examples and decision trees.

## Domain-Specific Patterns

**Analysis & Topology:** Integrability, continuity, compactness patterns. Tactics: `continuity`, `fun_prop`.

**Algebra:** Instance building, quotient constructions. Tactics: `ring`, `field_simp`, `group`.

**Measure Theory & Probability** (emphasis in this skill): Conditional expectation, sub-σ-algebras, a.e. properties. Tactics: `measurability`, `positivity`. See [measure-theory.md](references/measure-theory.md) for detailed patterns.

**Complete domain guide:** [domain-patterns.md](references/domain-patterns.md)

## Managing Incomplete Proofs

**Standard mathlib axioms (acceptable):** `Classical.choice`, `propext`, `quot.sound`. Check with `#print axioms theorem_name` or `$LEAN4_SCRIPTS/check_axioms.sh`.

**CRITICAL: Sorries/axioms are NOT complete work.** A theorem that compiles with sorries is scaffolding, not a result. Document every sorry with concrete strategy and dependencies. Search mathlib exhaustively before adding custom axioms.

**When sorries are acceptable:** (1) Active work in progress with documented plan, (2) User explicitly approves temporary axioms with elimination strategy.

**Not acceptable:** "Should be in mathlib", "infrastructure lemma", "will prove later" without concrete plan.

## Compiler-Guided Proof Repair

**When proofs fail to compile,** use iterative compiler-guided repair instead of blind resampling.

**How it works:**
1. Compile → extract structured error (type, location, goal, context)
2. Try automated solver cascade first (many simple cases handled mechanically, zero LLM cost)
   - Order: `rfl → simp → ring → linarith → nlinarith → omega → exact? → apply? → aesop`
3. If solvers fail → call `lean4-proof-repair` agent:
   - **Stage 1:** Haiku (fast, most common cases) - 6 attempts
   - **Stage 2:** Sonnet (precise, complex cases) - 18 attempts
4. Apply minimal patch (1-5 lines), recompile, repeat (max 24 attempts)

**Key benefits:**
- **Low sampling budget** (K=1 per attempt, not K=100)
- **Error-driven action selection** (specific fix per error type, not random guessing)
- **Fast model first** (Haiku), escalate only when needed (Sonnet)
- **Solver cascade** handles simple cases mechanically (zero LLM cost)
- **Early stopping** prevents runaway costs (bail after 3 identical errors)

**Detailed guide:** [compiler-guided-repair.md](references/compiler-guided-repair.md)

## Common Compilation Errors

| Error | Fix |
|-------|-----|
| "failed to synthesize instance" | Add `haveI : Instance := ...` |
| "maximum recursion depth" | Provide manually: `letI := ...` |
| "type mismatch" | Use coercion: `(x : ℝ)` or `↑x` |
| "unknown identifier" | Add import |

See [compilation-errors.md](references/compilation-errors.md) for detailed debugging workflows.

## Documentation Conventions

- Write **timeless** documentation (describe what code is, not development history)
- Don't highlight "axiom-free" status after proofs are complete
- Mark internal helpers as `private` or in dedicated sections
- Use `example` for educational code, not `lemma`/`theorem`

## Quality Checklist

**Before commit:**
- [ ] `lake build` succeeds on full project
- [ ] All sorries documented with concrete strategy
- [ ] No new axioms without elimination plan
- [ ] Imports minimal

**Doing it right:** Sorries/axioms decrease over time, each commit completes one lemma, proofs build on mathlib.

**Red flags:** Sorries multiply, claiming "complete" with sorries/axioms, fighting type checker for hours, monolithic proofs (>100 lines), long `have` blocks (>30 lines should be extracted as lemmas - see [proof-refactoring.md](references/proof-refactoring.md)).

## Reference Files

**Core references:** [lean-phrasebook.md](references/lean-phrasebook.md), [mathlib-guide.md](references/mathlib-guide.md), [tactics-reference.md](references/tactics-reference.md), [compilation-errors.md](references/compilation-errors.md)

**Domain-specific:** [domain-patterns.md](references/domain-patterns.md), [measure-theory.md](references/measure-theory.md), [instance-pollution.md](references/instance-pollution.md), [calc-patterns.md](references/calc-patterns.md)

**Incomplete proofs:** [sorry-filling.md](references/sorry-filling.md), [axiom-elimination.md](references/axiom-elimination.md)

**Optimization & refactoring:** [performance-optimization.md](references/performance-optimization.md), [proof-golfing.md](references/proof-golfing.md), [proof-refactoring.md](references/proof-refactoring.md), [mathlib-style.md](references/mathlib-style.md)

**Automation:** [compiler-guided-repair.md](references/compiler-guided-repair.md), [lean-lsp-server.md](references/lean-lsp-server.md), [lean-lsp-tools-api.md](references/lean-lsp-tools-api.md), [subagent-workflows.md](references/subagent-workflows.md)
