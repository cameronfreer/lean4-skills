---
name: review
description: Read-only code review of Lean proofs
user_invocable: true
---

# Lean4 Review

Read-only review of Lean proofs for quality, style, and optimization opportunities.

**Non-destructive:** Files are restored after analysis.

## Usage

```
/lean4:review                    # Review entire project
/lean4:review File.lean          # Review specific file
/lean4:review --scope=changed    # Review only changed files (git diff)
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or directory to review |
| --scope | No | `changed` for git diff only |
| --codex | No | Include OpenAI Codex suggestions |
| --llm | No | Use llm CLI with model |
| --hook | No | Run custom analysis script |

## Actions

1. **Build Status** - `lake build`
2. **Sorry Audit** - List sorries with context:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/sorry_analyzer.py [scope] --format=json
   ```
3. **Axiom Check** - Report axiom usage:
   ```bash
   bash $LEAN4_SCRIPTS/check_axioms_inline.sh [scope]
   ```
4. **Style Review** - Check mathlib conventions (naming, structure, tactics)
5. **Golfing Opportunities** - Identify optimizations:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/find_golfable.py [scope] --filter-false-positives
   ```
6. **Complexity Metrics** - Proof sizes, longest proofs, tactic patterns

## Output

```markdown
## Lean4 Review Report

### Build Status
✓ Project compiles

### Sorry Audit (N remaining)
| File | Line | Theorem | Suggestion |
|------|------|---------|------------|
| ... | ... | ... | ... |

### Axiom Status
✓ Standard axioms only

### Style Notes
- [file:line] - [suggestion]

### Golfing Opportunities
- [pattern] → [optimization]

### Recommendations
1. [action item]
```

## External Hooks

Custom hooks receive JSON on stdin with `file`, `content`, `sorries`, `axioms`, `build_status` and return JSON with `suggestions` array.

## Safety

- Read-only (does not modify files permanently)
- Axiom check temporarily appends `#print axioms`, then restores
- Does not create commits
- Does not apply fixes

## See Also

- `/lean4:autoprover` - Fill sorries and fix proofs
- `/lean4:golf` - Apply golfing optimizations
- [mathlib-style.md](../skills/lean4/references/mathlib-style.md)
- [Examples](../skills/lean4/references/command-examples.md#review)
