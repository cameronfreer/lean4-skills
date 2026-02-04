---
name: lean4
description: "Use when editing .lean files, seeing sorry/failed to synthesize instance, lake build errors, or searching mathlib."
---

# Lean 4 Theorem Proving

Use this skill whenever you're editing Lean 4 proofs or debugging Lean builds. It prioritizes LSP-based inspection and mathlib search, with scripted primitives for sorry analysis, axiom checking, and error parsing.

## Core Principles

**Search before prove.** Many mathematical facts already exist in mathlib. Search exhaustively before writing tactics.

**Build incrementally.** Lean's type checker is your test suite—if it compiles with no sorries and standard axioms only, the proof is sound.

**Respect scope.** Follow the user's preference: fill one sorry, its transitive dependencies, all sorries in a file, or everything. Ask if unclear.

**Never change statements or add axioms without explicit permission.** Theorem/lemma statements, type signatures, and docstrings are off-limits unless the user requests changes. Inline comments may be adjusted; docstrings may not (they're part of the API). Custom axioms require explicit approval—if a proof seems to need one, stop and discuss.

## Commands

| Command | Purpose |
|---------|---------|
| `/lean4:autoprover` | Planning-first sorry filling and repair |
| `/lean4:checkpoint` | Verified save point (build + axiom check + commit) |
| `/lean4:review` | Read-only quality review |
| `/lean4:golf` | Optimize proofs for brevity |
| `/lean4:doctor` | Plugin troubleshooting and migration help |

## LSP Tools (Preferred)

Sub-second feedback and search tools (LeanSearch, Loogle, LeanFinder) via Lean LSP MCP:

```
lean_goal(file, line)                           # See exact goal
lean_hover_info(file, line, col)                # Understand types
lean_local_search("keyword")                    # Fast local + mathlib (unlimited)
lean_leanfinder("goal or query")                # Semantic, goal-aware (rate-limited)
lean_leansearch("natural language")             # Semantic search (rate-limited)
lean_loogle("?a → ?b → _")                      # Type-pattern (rate-limited)
lean_multi_attempt(file, line, snippets=[...])  # Test multiple tactics
```

## Core Primitives

| Script | Purpose | Output |
|--------|---------|--------|
| `sorry_analyzer.py` | Find sorries with context | JSON/text |
| `check_axioms_inline.sh` | Check for non-standard axioms | text |
| `smart_search.sh` | Multi-source mathlib search | text |
| `find_golfable.py` | Detect optimization patterns | JSON |
| `find_usages.sh` | Find declaration usages | text |

**Usage:** Invoked by commands automatically. See [references/](references/) for details.

## Automation

`/lean4:autoprover` handles most tasks. It asks once per session:
- **Autonomy mode** (manual/assisted/auto)
- **Review source** (internal/external/both/none)

For complex proofs, it may delegate to internal workflows for deep sorry-filling, proof repair, or axiom elimination. You don't invoke these directly.

## Common Fixes

| Error | Fix |
|-------|-----|
| `type mismatch` | Add coercion `(x : ℝ)` or `((x : ℝ))`, use `convert`, fix argument order |
| `unknown identifier` | Add import, qualify name (`Mathlib.X.Y.foo`), check spelling |
| `failed to synthesize` | Add `haveI`/`letI`, use `open scoped`, check instance args |
| `maximum recursion` | Provide explicit instance with `letI` |
| `timeout` | Replace `simp [*]` with `simp only [...]` or targeted lemmas |

## Type Class Patterns

```lean
-- Local instance for this proof block
haveI : MeasurableSpace Ω := inferInstance
letI : Fintype α := ⟨...⟩

-- Scoped instances (affects current section)
open scoped Topology MeasureTheory
```

Order matters: provide outer structures before inner ones.

## Automation Tactics

Try in order (stop on first success):
`rfl` → `simp` → `ring` → `linarith` → `nlinarith` → `omega` → `exact?` → `apply?` → `grind` → `aesop`

Note: `exact?`/`apply?` query mathlib (slow). `grind` and `aesop` are powerful but may timeout.

## Quality Gate

A proof is complete when:
- `lake build` passes
- Zero sorries in agreed scope
- Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
- No statement changes without permission

## References

**LSP Tools:** [lean-lsp-server](references/lean-lsp-server.md) (quick start), [lean-lsp-tools-api](references/lean-lsp-tools-api.md) (full API details)

**Search:** [mathlib-guide](references/mathlib-guide.md) (finding lemmas), [lean-phrasebook](references/lean-phrasebook.md) (math-to-Lean translations)

**Errors:** [compilation-errors](references/compilation-errors.md) (when build fails), [instance-pollution](references/instance-pollution.md) (when typeclass issues persist), [compiler-guided-repair](references/compiler-guided-repair.md) (systematic repair workflow)

**Tactics:** [tactics-reference](references/tactics-reference.md) (tactic lookup), [tactic-patterns](references/tactic-patterns.md) (common patterns), [calc-patterns](references/calc-patterns.md) (calculation proofs), [simp-hygiene](references/simp-hygiene.md) (simp troubleshooting)

**Proof Development:** [proof-templates](references/proof-templates.md) (starting points), [proof-refactoring](references/proof-refactoring.md) (restructuring proofs), [sorry-filling](references/sorry-filling.md) (sorry elimination)

**Optimization:** [proof-golfing](references/proof-golfing.md) (shortening proofs), [proof-golfing-patterns](references/proof-golfing-patterns.md) (specific techniques), [proof-golfing-safety](references/proof-golfing-safety.md) (avoiding breakage), [performance-optimization](references/performance-optimization.md) (slow proof fixes)

**Domain-Specific:** [domain-patterns](references/domain-patterns.md) (by math area), [measure-theory](references/measure-theory.md) (measure/probability), [axiom-elimination](references/axiom-elimination.md) (removing sorry/axiom)

**Style:** [mathlib-style](references/mathlib-style.md) (naming/formatting conventions)

**Workflows:** [agent-workflows](references/agent-workflows.md) (internal agents), [subagent-workflows](references/subagent-workflows.md) (delegation patterns), [command-examples](references/command-examples.md) (usage examples)

**Internals:** [review-hook-schema](references/review-hook-schema.md) (hook configuration)
