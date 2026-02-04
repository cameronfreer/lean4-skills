---
name: lean4
description: Use for any Lean 4 .lean work: filling sorries, fixing build errors, searching mathlib, or resolving typeclass/instance issues. LSP-first, scripts as fallback.
---

# Lean 4 Theorem Proving

Use this skill whenever you're editing Lean 4 proofs or debugging Lean builds. It prioritizes LSP-based inspection and mathlib search, with scripted primitives for sorry analysis, axiom checking, and error parsing.

## When This Skill Applies

- You are in a `.lean` file or a Lean 4 project
- You see `sorry`, `by?`, or "failed to synthesize instance"
- `lake build` fails or type errors appear
- You need to find a lemma in mathlib or fix imports
- You need axiom/sorry hygiene checks before committing

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

Sub-second feedback via Lean LSP MCP:

```
lean_goal(file, line)                           # See exact goal
lean_hover_info(file, line, col)                # Understand types
lean_local_search("keyword")                    # Fast local + mathlib (unlimited)
lean_leanfinder("goal or query")                # Semantic, goal-aware (rate-limited)
lean_leansearch("natural language")             # Semantic search (rate-limited)
lean_loogle("?a → ?b → _")                      # Type-pattern (rate-limited)
lean_multi_attempt(file, line, snippets=[...])  # Test multiple tactics
```

## Scripts

Primitives for analysis and search:

```bash
# Sorry/axiom analysis (always available)
$LEAN4_SCRIPTS/sorry_analyzer.py . --format=json
$LEAN4_SCRIPTS/check_axioms_inline.sh File.lean

# Search fallback (when LSP unavailable)
$LEAN4_SCRIPTS/smart_search.sh "query" --source=all
```

## Common Fixes

| Error | Fix |
|-------|-----|
| `type mismatch` | Coercion `(x : ℝ)`, `convert`, or fix argument |
| `unknown identifier` | Search mathlib, add import, check spelling |
| `failed to synthesize` | Add `haveI`/`letI` to provide instance |
| `maximum recursion` | Provide instance explicitly with `letI` |
| `timeout` | Use `simp only [...]` instead of `simp [*]` |

## Type Class Patterns

```lean
haveI : MeasurableSpace Ω := inferInstance   -- Provide instance
letI : Fintype α := ⟨...⟩                    -- Computable instance
open scoped Topology MeasureTheory           -- Scoped instances
```

## Automation Tactics

Try in order (stop on first success):
`rfl` → `simp` → `ring` → `linarith` → `omega` → `exact?` → `apply?` → `aesop`

## Quality Gate

A proof is complete when:
- `lake build` passes
- Zero sorries (within agreed scope)
- Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
- No statement changes without permission

## References

**Core:** [lean-phrasebook](references/lean-phrasebook.md), [mathlib-guide](references/mathlib-guide.md), [tactics-reference](references/tactics-reference.md)

**Errors:** [compilation-errors](references/compilation-errors.md), [instance-pollution](references/instance-pollution.md)

**Patterns:** [tactic-patterns](references/tactic-patterns.md), [proof-templates](references/proof-templates.md), [domain-patterns](references/domain-patterns.md)
