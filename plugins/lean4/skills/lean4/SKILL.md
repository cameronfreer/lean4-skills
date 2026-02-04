---
name: lean4
description: Use when working with Lean 4 (.lean files), writing mathematical proofs, seeing "failed to synthesize instance" errors, managing sorry/axiom elimination, or searching mathlib for lemmas - provides build-first workflow, haveI/letI patterns, compiler-guided repair, and LSP integration
---

# Lean 4 Theorem Proving

## Core Principle

**Search before prove. Build incrementally. Trust the type checker.**

Most mathematical facts already exist in mathlib. Search exhaustively before writing tactics. Lean's type checker is your test suite - if it compiles with no sorries and standard axioms only, you're done.

**v4 Note:** This unified `lean4` plugin replaces the previous 3-plugin system. Memory integration was removed as it didn't work reliably.

## Commands

| Command | Purpose |
|---------|---------|
| `/lean4:autoprover` | Main entry - planning-first sorry filling and repair |
| `/lean4:checkpoint` | Verified save point (build + axiom check + commit) |
| `/lean4:review` | Read-only quality review with optional external hooks |
| `/lean4:golf` | Optimize proofs for brevity |
| `/lean4:doctor` | Diagnostics and migration help |

## The Golden Path

```
1. /lean4:autoprover     → Fill sorries with planning phase
2. /lean4:review         → Check quality (read-only)
3. /lean4:golf           → Optimize if desired
4. /lean4:checkpoint     → Verified commit
5. git push              → Manual, after review
```

## Search-First Approach

**90% of sorries already exist in mathlib.** Always search before writing tactics.

### With Lean LSP MCP (Preferred)

The LSP server provides sub-second feedback:

```
lean_leansearch("continuous function on compact set")  # Natural language
lean_loogle("Continuous _ → Compact _ → _")            # Type pattern
lean_local_search("IsCompact")                         # Keyword in project
lean_goal(file, line)                                  # See exact goal
lean_hover_info(file, line, col)                       # Understand types
```

### Fallback (Scripts)

When LSP unavailable:
```bash
bash $LEAN4_SCRIPTS/smart_search.sh "query" --source=all
bash $LEAN4_SCRIPTS/search_mathlib.sh "pattern" name
```

## Common Workflows

### Fill a Sorry

1. **Understand:** Read goal and context (LSP `lean_goal` or read the file)
2. **Search:** Look for existing lemma (LSP search or scripts)
3. **Try:** Apply lemma or simple tactic (`rfl`, `simp`, `ring`, `linarith`)
4. **Validate:** `lake build` must pass
5. **Commit:** One sorry = one commit

### Fix a Build Error

1. **Parse:** Understand the error message
2. **Classify:** Type mismatch? Unknown ident? Instance failure?
3. **Search:** Find correct API or missing import
4. **Fix:** Minimal change to resolve
5. **Verify:** Build again

### Common Error Fixes

| Error | Fix |
|-------|-----|
| `type mismatch` | Coercion `(x : ℝ)`, `convert _ using N`, or fix argument |
| `unknown identifier` | Search mathlib, add import, check spelling |
| `failed to synthesize` | Add `haveI : Instance := ...` or `letI` |
| `maximum recursion` | Provide instance explicitly with `letI` |
| `timeout` | Use `simp only [...]` instead of `simp [*]` |

## Type Class Management

When instance synthesis fails:

```lean
-- Provide instance for this block
haveI : MeasurableSpace Ω := inferInstance

-- Provide computable instance
letI : Fintype α := ⟨...⟩

-- Open scoped instances
open scoped Topology MeasureTheory
```

**Order matters:** Provide outer structures before inner ones.

## Automation Tactics

Try in order (stop on first success):

1. `rfl` - Definitional equality
2. `simp` / `simp only [...]` - Simplification
3. `ring` - Polynomial arithmetic
4. `linarith` / `nlinarith` - Linear/nonlinear arithmetic
5. `omega` - Integer arithmetic
6. `exact?` / `apply?` - Tactic search (slower)
7. `aesop` - General automation

**With LSP:** Use `lean_tactic_attempt` for instant feedback.

## Axiom Hygiene

**Acceptable axioms:** `propext`, `Classical.choice`, `Quot.sound`

**Check axioms:** `#print axioms theorem_name`

**Verify before commit:** Run `/lean4:checkpoint` which checks axioms automatically.

## Quality Standards

**A proof is complete when:**
- `lake build` passes
- Zero sorries
- Only standard mathlib axioms
- Imports are minimal

**Red flags:**
- Sorries "to be filled later"
- Custom axioms without elimination plan
- Fighting the type checker for hours
- Proofs over 50 lines (extract helpers)

## Reference Documentation

**Core:** [lean-phrasebook.md](references/lean-phrasebook.md), [mathlib-guide.md](references/mathlib-guide.md), [tactics-reference.md](references/tactics-reference.md)

**Errors:** [compilation-errors.md](references/compilation-errors.md), [instance-pollution.md](references/instance-pollution.md)

**Domains:** [domain-patterns.md](references/domain-patterns.md), [measure-theory.md](references/measure-theory.md), [calc-patterns.md](references/calc-patterns.md)

**Optimization:** [proof-golfing.md](references/proof-golfing.md), [proof-refactoring.md](references/proof-refactoring.md), [mathlib-style.md](references/mathlib-style.md)

**Automation:** [compiler-guided-repair.md](references/compiler-guided-repair.md), [lean-lsp-server.md](references/lean-lsp-server.md)

## See Also

- [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) - LSP server for fast feedback
- [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/) - API reference
- [Loogle](https://loogle.lean-lang.org/) - Type-based search
- [LeanSearch](https://leansearch.net/) - Natural language search
