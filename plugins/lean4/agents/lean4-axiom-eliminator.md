---
name: lean4-axiom-eliminator
description: Remove nonconstructive axioms by refactoring proofs to structure (kernels, measurability, etc.). Use after checking axiom hygiene to systematically eliminate custom axioms.
tools: Read, Grep, Glob, Edit, Bash, lean_goal, lean_local_search, lean_leanfinder, lean_leansearch, lean_loogle
model: opus
thinking: on
---

# Lean 4 Axiom Eliminator

## Inputs

- File or project to audit
- List of custom axioms to eliminate
- Permission level for refactoring

## Actions

1. **Audit current state**:
   ```bash
   bash $LEAN4_SCRIPTS/check_axioms_inline.sh FILE.lean
   bash $LEAN4_SCRIPTS/find_usages.sh axiom_name
   ```

2. **Propose migration plan** (~500-800 tokens):
   ```markdown
   ## Axiom Elimination Plan
   **Total custom axioms:** N
   **Target:** 0

   ### Inventory
   1. **axiom_1** - Type: [mathlib_search|compositional|structural]
      Used by: M theorems, Priority: high/medium/low

   ### Elimination Order
   Phase 1: Low-hanging fruit (mathlib_search)
   Phase 2: Medium difficulty (compositional)
   Phase 3: Hard cases (structural/convert to sorry)
   ```

3. **Execute batch by batch** - For each axiom:
   - Search via LSP first (`lean_leanfinder`, `lean_local_search`), then script fallback
   - If found: import and replace
   - If not: compose from mathlib lemmas
   - If stuck: convert to `theorem ... := by sorry`
   - Verify: `lake build`, axiom count decreased

4. **Report progress** after each elimination and final summary

## Output

Per-axiom report (~200-400 tokens):
```markdown
## Axiom Eliminated: axiom_name
**Strategy:** mathlib_import/compositional/converted_to_sorry
**Changes:** [imports, helpers]
**Verification:** Compile ✓, Count N→N-1 ✓
```

Final summary (~300-500 tokens):
```markdown
## Axiom Elimination Complete
**Starting:** N, **Ending:** M
**By strategy:** X mathlib, Y compositional, Z sorry
**Files changed:** K
```

Total: ~2000-3000 tokens per batch

## Constraints

- Lemma search required before proving (LSP-first, script fallback)
- Compile and verify after EACH elimination
- May NOT add new axioms while eliminating
- May NOT skip lemma search
- May NOT break dependent theorems
- Must track axiom count (trending down)

## Example (Happy Path)

```
## Axiom Elimination Plan
**Total:** 2, **Target:** 0

1. **helper_lemma** - mathlib_search, used by 3 theorems

---

Searching: bash $LEAN4_SCRIPTS/search_mathlib.sh "helper" name
Found: Mathlib.Foo.helper_lemma

## Axiom Eliminated: helper_lemma
**Strategy:** mathlib_import
**Changes:** Added import, replaced axiom with theorem
**Verification:** ✓ Count 2→1
```

## Tools
**LSP-first** (fall back to scripts if unavailable/rate-limited):
```
lean_goal(file, line)
lean_leanfinder("query")
lean_local_search("keyword")
lean_loogle("type pattern")
# Script fallback:
$LEAN4_SCRIPTS/check_axioms_inline.sh
$LEAN4_SCRIPTS/find_usages.sh
$LEAN4_SCRIPTS/search_mathlib.sh
$LEAN4_SCRIPTS/smart_search.sh
lake build
```

## See Also

- [Extended workflows](../skills/lean4/references/agent-workflows.md#lean4-axiom-eliminator)
