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

Custom hooks receive structured JSON on stdin with file information, sorries, axioms, and build status. They return JSON with a `suggestions` array.

See [review-hook-schema.md](../skills/lean4/references/review-hook-schema.md) for full input/output schemas and examples.

## External Review Handoff

When external review is selected (via `--codex` or user preference), display this prompt:

```
─────────────────────────────────────────────────────────
EXTERNAL REVIEW PROMPT (copy to Codex or paste results below)
─────────────────────────────────────────────────────────

You are an external code reviewer for Lean 4 theorem proofs.

CRITICAL CONSTRAINTS:
- Do NOT edit code directly
- Provide HIGH-LEVERAGE strategic advice only
- Focus on WHAT to search or try, not exact tactic code

Return JSON matching this schema:
{
  "version": "1.0",
  "suggestions": [
    {
      "file": "string",
      "line": number,
      "severity": "hint" | "warning",
      "category": "sorry" | "axiom" | "style" | "structure",
      "message": "string (strategic advice, not code)"
    }
  ]
}

Focus on:
1. Structural issues (wrong approach, missing lemmas)
2. Mathlib coverage (what existing lemmas to search)
3. Type class issues (instance ordering, missing constraints)

Limit to 3-5 highest-leverage suggestions.
─────────────────────────────────────────────────────────
```

Then wait for user to paste JSON response (or pipe via `--codex`).

## Post-Review Actions

After review completes (internal or external), prompt:

```
## Review Complete

Would you like me to create an action plan from the review findings?
- [yes] — Enter plan mode with 3-6 step implementation plan
- [no] — End review, return to conversation
```

If "yes":
1. Enter plan mode
2. Create plan with one task per high-priority suggestion
3. Get user approval before execution
4. Use `/lean4:autoprover` to apply fixes (review itself remains read-only)

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
    "message": "Search for tendsto_atTop in Mathlib.Topology.Order.Basic"
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
