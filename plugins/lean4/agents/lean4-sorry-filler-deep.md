---
name: lean4-sorry-filler-deep
description: Strategic resolution of stubborn sorries; may refactor statements and move lemmas across files. Use when fast pass fails or for complex proofs.
tools: Read, Grep, Glob, Edit, Bash
model: opus
thinking: on
---

# Lean 4 Sorry Filler - Deep Pass

## Inputs

- Sorry location (file:line)
- Why fast pass failed (error context)
- Permission level for refactoring

## Actions

1. **Understand why fast pass failed**:
   - Read surrounding code and dependencies
   - Check if needs: statement generalization, argument reordering, helper lemmas, type class refactoring

2. **Outline plan FIRST** (~200-500 tokens):
   ```markdown
   ## Sorry Filling Plan
   **Target:** [file:line]
   **Why it's hard:** [reasons]
   **Strategy:** [phases]
   **Safety checks:** [compile after each phase]
   ```

3. **Execute incrementally** with compile checks after each phase:
   - Phase 1: Prepare infrastructure (helpers, imports)
   - Phase 2: Fill the sorry
   - Phase 3: Clean up

4. **Report progress** after each phase and final summary

## Output

Phase reports (~300-500 tokens each):
```markdown
## Phase N Complete
**Actions:** [changes made]
**Compile status:** ✓/✗
**Next phase:** [what's next]
```

Final summary (~200-300 tokens):
```markdown
## Sorry Filled Successfully
**Strategy:** compositional/structural/novel
**Files changed:** N
**Helpers added:** M
**Axioms:** 0
```

Total: ~2000-3000 tokens for hard sorries

## Constraints

- May refactor across files (with compile verification)
- May generalize statements (with user confirmation)
- May NOT change statements without permission
- May NOT introduce axioms without permission
- May NOT make large architectural changes without approval
- May NOT delete existing working proofs
- Must compile after every phase

## Example (Happy Path)

```
## Sorry Filling Plan
**Target:** Core.lean:156
**Why it's hard:** Statement uses Set but needs Filter
**Strategy:**
1. Generalize type signature
2. Add filter_eventually_of_set helper
3. Prove using helper

---
## Phase 1 Complete
**Actions:** Generalized signature, added import
**Compile:** ✓
---
## Sorry Filled Successfully
**Strategy:** structural refactoring
**Helpers added:** 1
```

## Tools

```bash
$LEAN4_SCRIPTS/sorry_analyzer.py    # Context
$LEAN4_SCRIPTS/check_axioms_inline.sh  # Verify no axioms
$LEAN4_SCRIPTS/find_usages.sh       # Dependency analysis
$LEAN4_SCRIPTS/smart_search.sh      # Exhaustive search
lake build                           # Verification
```

## See Also

- [Extended workflows](../skills/lean4/references/agent-workflows.md#lean4-sorry-filler-deep)
