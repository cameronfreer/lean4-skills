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
/lean4:review                              # Review changed files (default)
/lean4:review File.lean                    # Review specific file
/lean4:review File.lean --line=89          # Review single sorry
/lean4:review File.lean --line=89 --scope=deps  # Review sorry + its dependencies
/lean4:review --scope=project              # Review entire project (prompts)
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or directory to review |
| --scope | No | `sorry`, `deps`, `file`, `changed`, or `project` |
| --line | No | Line number for single-sorry scope |
| --codex | No | Include OpenAI Codex suggestions |
| --llm | No | Use llm CLI with model |
| --hook | No | Run custom analysis script |
| --json | No | Output structured JSON for external tools |
| --mode | No | `batch` (default) or `stuck` (triage) |

## Scope Behavior

**Scope levels:**
| Scope | Description |
|-------|-------------|
| `sorry` | Single sorry at --line (requires target file + --line) |
| `deps` | Sorry + same-file helpers and directly referenced lemmas (requires target file + --line) |
| `file` | All sorries in target file |
| `changed` | Files modified since last commit (git diff) |
| `project` | Entire project (requires confirmation) |

**Defaults:**
- No args → `--scope=changed`
- Target file provided → `--scope=file`
- Target + `--line` → `--scope=sorry`
- Triggered by autoprover → matches current focus (`sorry` or `file`)

**Note:** Scope filtering is implemented by the reviewing agent, not the underlying scripts. The agent reads script output and filters results to match the requested scope.

**Project-wide confirmation:**
```
⚠️  This will review the entire project.
Proceed? (yes / no)
```

**Output header always shows scope:**
```markdown
## Lean4 Review Report
**Scope:** Core.lean:89 (single sorry)
```

## Review Modes

**Batch mode (default):**
- Purpose: "What changed in this batch" + basic hygiene
- Output: Full review report with all sections
- Use: Regular cadence reviews, manual quality checks

**Stuck mode:**
- Purpose: "What's blocking progress on current focus"
- Output: Top 3 blockers with actionable next steps
- Use: Triggered by autoprover when no progress detected
- Lightweight: Skips full golf analysis and complexity metrics; focuses on blockers only

**Stuck mode output format:**
```markdown
## Stuck Review — Core.lean:89

**Top 3 blockers:**
1. Missing lemma about tendsto_atTop → search Mathlib.Topology.Order
2. Typeclass instance missing for MeasurableSpace β → add `haveI`
3. Proof too long (38 lines) → extract helper lemma first

**Recommended next action:** Search for tendsto variants in Topology/Order
```

If analysis suggests the statement may be false, add:
```markdown
**Flag:** Statement may be false (goal on decidable type failed preflight)
```

**Blocker priority (stuck mode):**
1. Build errors/diagnostics in focus
2. Sorries on critical path (target line or its dependencies)
3. Custom axioms introduced in focus
4. Long/fragile proofs (performance risk)
5. Falsification signals (decidable goal that failed `decide`, repeated proof failures)

## Actions

The agent selects files based on scope, then runs these analyses (per file or directory):

1. **Build Status** - `lake build`
2. **Sorry Audit** - `sorry_analyzer.py <target> --format=json`
3. **Axiom Check** - `check_axioms_inline.sh <target>`
4. **Style Review** - Check mathlib conventions (naming, structure, tactics)
5. **Golfing Opportunities** - `find_golfable.py <target> --filter-false-positives`
6. **Complexity Metrics** - Proof sizes, longest proofs, tactic patterns

**Stuck mode:** Steps 5–6 are skipped; focus is on blockers (steps 1–4) for quick triage.

## Output

```markdown
## Lean4 Review Report
**Scope:** Core.lean:89 (single sorry)

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
EXTERNAL REVIEW PROMPT
Scope: {scope} — {file}:{line} (or file-only, or "changed files")
─────────────────────────────────────────────────────────

[Only include content matching scope - single sorry context,
 dependencies, or file. Never send entire project unless scope=project]

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

**Note:** When `--mode=stuck` is triggered by autoprover, skip this prompt—autoprover handles the follow-up with its own "Apply this plan? [yes/no]" prompt.

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
