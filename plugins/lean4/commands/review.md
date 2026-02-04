---
name: review
description: Read-only code review of Lean proofs
user_invocable: true
---

# Lean4 Review

Read-only review of Lean proofs for quality, style, and optimization opportunities.

**This command is non-destructive** (files are restored after analysis).

---

## What It Does

1. **Build Status** - Verify project compiles
2. **Sorry Audit** - List remaining sorries with context
3. **Axiom Check** - Report axiom usage
4. **Style Review** - Check mathlib style compliance
5. **Golfing Opportunities** - Identify proof optimizations
6. **Complexity Metrics** - Report proof sizes and structure

---

## Usage

```
/lean4:review                    # Review entire project
/lean4:review File.lean          # Review specific file
/lean4:review --scope=changed    # Review only changed files (git diff)
```

---

## Review Sections

### 1. Build Status

```bash
lake build
```

Report:
- ✓ Build passing, OR
- ✗ Build failing with error summary

### 2. Sorry Audit

```bash
${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/sorry_analyzer.py [scope] --format=json
```

For each sorry, report:
- Location (file:line)
- Theorem name
- Context (surrounding code)

### 3. Axiom Check

```bash
bash $LEAN4_SCRIPTS/check_axioms_inline.sh [scope]
```

Report:
- Standard axioms: ✓ (expected)
- Custom axioms: ⚠️ List with elimination suggestions

### 4. Style Review

Check against mathlib conventions:

- **Naming:** `snake_case` for lemmas, descriptive names
- **Structure:** Short proofs (<30 lines), extracted helpers
- **Tactics:** Prefer `simp only` over `simp`, explicit over magic

Flag violations with suggestions.

### 5. Golfing Opportunities

```bash
${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/find_golfable.py [scope] --filter-false-positives
```

For each opportunity:
- Pattern detected (e.g., `rw; exact` → `rwa`)
- Estimated savings
- Safety note if inlining requires verification

### 6. Complexity Metrics

Analyze proof structure by reading files:
- Count lines per proof
- Identify long proofs (potential refactoring targets)
- Check tactic diversity

Report:
- Average proof length
- Longest proofs (>30 lines suggests extraction)
- Tactic usage patterns

---

## Output Format

```markdown
## Lean4 Review Report

### Build Status
✓ Project compiles successfully

### Sorry Audit (3 remaining)

| File | Line | Theorem | Approach |
|------|------|---------|----------|
| Core.lean | 42 | `helper_bound` | Try `linarith` |
| Core.lean | 89 | `main_result` | Search mathlib for `Continuous.comp` |
| Aux.lean | 15 | `trivial_fact` | Try `simp` |

### Axiom Status
✓ Standard axioms only (propext, Classical.choice, Quot.sound)

### Style Notes
- `Core.lean:156` - Proof is 45 lines, consider extracting helper
- `Aux.lean:23` - Use `simp only [...]` instead of bare `simp`

### Golfing Opportunities (2 found)
- `Core.lean:78` - `rw [h]; exact` → `rwa [h]` (saves 1 line)
- `Aux.lean:31` - `ext x; rfl` → `rfl` (if definitional)

### Complexity Summary
- Total theorems: 24
- Average proof: 12 lines
- Longest: `main_theorem` (45 lines)

### Recommendations
1. Fill 3 remaining sorries with `/lean4:autoprover`
2. Consider extracting `main_theorem` helper lemmas
3. Apply 2 golfing opportunities for cleaner code
```

---

## Sandbox Mode

This command is **non-destructive**:

- ✓ Runs analysis scripts
- ✓ Runs `lake build`
- ✓ Reports findings
- ✗ Does NOT permanently modify files
- ✗ Does NOT create commits
- ✗ Does NOT apply fixes

**Note:** The axiom check (`check_axioms_inline.sh`) temporarily appends `#print axioms` commands to files, then restores them automatically. Files are unchanged after the command completes.

To apply changes, use `/lean4:autoprover` or edit manually.

---

## When to Use

- **Before pushing** - Final quality check
- **Before PR** - Ensure review-ready
- **After autoprover** - Verify results
- **Learning** - Understand proof quality standards

---

## Example

```
User: /lean4:review Core.lean

Claude: Running review on Core.lean...

## Lean4 Review Report

### Build Status
✓ Core.lean compiles successfully

### Sorry Audit (1 remaining)
- Core.lean:89 - `convergence_bound`
  Goal: `∀ ε > 0, ∃ N, ∀ n ≥ N, |f n - L| < ε`
  Suggestion: Search mathlib for `Metric.tendsto_atTop`

### Axiom Status
✓ Standard axioms only

### Style Notes
- Line 45: Consider `simp only [add_comm, mul_comm]` instead of `simp [*]`
- Line 78: Proof is 38 lines - consider extracting `bound_helper` lemma

### Golfing Opportunities
- Line 23: `rw [h]; exact trivial` → `rwa [h]`
- Line 56: `ext x; simp` - verify if `simp` alone suffices

### Complexity Summary
- Theorems in file: 8
- Average proof: 15 lines
- Longest: `convergence_bound` (38 lines)

### Recommendations
1. Fill `convergence_bound` sorry - likely in mathlib
2. Extract helper from long proof at line 78
3. Tighten `simp` calls for faster compilation
```

---

## External Tool Hooks (Optional)

Review can optionally call external tools for additional analysis or second opinions.

**Availability:** Tools are checked before use (`command -v codex`, etc.). If a tool isn't installed, review continues without it and notes the skip.

### Supported Tools

| Tool | Flag | What It Does |
|------|------|--------------|
| Codex CLI | `--codex` | Get OpenAI Codex suggestions |
| `llm` CLI | `--llm` | Use Simon Willison's llm tool |
| Custom script | `--hook=path` | Run your own analysis |

### Usage

```
/lean4:review --codex              # Include Codex suggestions
/lean4:review --llm="claude-3"     # Use llm CLI with specific model
/lean4:review --hook=./my_linter.sh # Run custom script
```

### Custom Hook Interface

Custom hooks receive JSON on stdin:
```json
{
  "file": "Core.lean",
  "content": "...",
  "sorries": [...],
  "axioms": [...],
  "build_status": "passing"
}
```

And should output JSON:
```json
{
  "suggestions": [
    {"line": 42, "message": "Consider using...", "severity": "hint"}
  ]
}
```

### Example with Codex

```
User: /lean4:review Core.lean --codex

Claude: Running review with Codex integration...

## Lean4 Review Report

### Build Status
✓ Core.lean compiles

### Sorry Audit
- Line 89: `convergence_bound` - needs proof

### Codex Suggestions
- Line 89: "Try `tendsto_atTop_of_eventually_ge` from Mathlib"
- Line 45: "The `simp` call could be replaced with `simp only [add_comm]`"

### Claude Analysis
[standard review sections...]
```

### Notes

- External tools are **optional** - review works without them
- Tool output is incorporated into the report, not blindly trusted
- You can combine multiple tools: `--codex --hook=./lint.sh`
- Custom hooks must be executable and in your PATH or use absolute path

---

## See Also

- `/lean4:autoprover` - Fill sorries and fix proofs
- `/lean4:checkpoint` - Save verified progress
- `/lean4:golf` - Apply golfing optimizations
- `/lean4:doctor` - Diagnostics and troubleshooting
- [mathlib-style.md](../skills/lean4/references/mathlib-style.md) - Style guide
- [proof-golfing.md](../skills/lean4/references/proof-golfing.md) - Optimization patterns
