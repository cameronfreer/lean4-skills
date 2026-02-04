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
| --json | No | Output structured JSON for external tools |

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

See [review-hook-schema.md](../skills/lean4/references/review-hook-schema.md) for full schema documentation.

## JSON Output Schema

When using `--json`, output follows this structure:

```json
{
  "version": "1.0",
  "build_status": "passing" | "failing",
  "sorries": [
    {"file": "Core.lean", "line": 89, "theorem": "convergence_main", "goal": "..."}
  ],
  "axioms": {
    "standard": ["propext", "Classical.choice", "Quot.sound"],
    "custom": []
  },
  "style_notes": [
    {"file": "Core.lean", "line": 42, "message": "Consider using field syntax"}
  ],
  "golfing_opportunities": [
    {"file": "Core.lean", "line": 78, "pattern": "have chain", "suggestion": "Inline or extract"}
  ],
  "summary": {
    "total_sorries": 3,
    "total_custom_axioms": 0,
    "style_issues": 2,
    "golf_opportunities": 5
  }
}
```

## Codex Hook Interface

When using `--codex`, the review command sends context to Codex and receives suggestions.

**Hook Input (sent to Codex):**
```json
{
  "version": "1.0",
  "request_type": "review",
  "files": [{
    "path": "Core.lean",
    "content": "...",
    "sorries": [{"line": 89, "goal": "...", "hypotheses": [...]}],
    "axioms": [],
    "diagnostics": []
  }],
  "build_status": "passing",
  "preferences": {"focus": "completeness", "verbosity": "detailed"}
}
```

**Hook Output (suggestions from Codex):**
```json
{
  "version": "1.0",
  "suggestions": [{
    "file": "Core.lean",
    "line": 89,
    "severity": "hint",
    "message": "Try tendsto_atTop from Mathlib",
    "fix": "exact tendsto_atTop.mpr ..."
  }]
}
```

**Example invocation:**
```bash
/lean4:review --codex           # Human-readable with Codex hints
/lean4:review --codex --json    # Structured JSON with Codex suggestions
```

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
