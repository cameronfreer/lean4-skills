# Review Hook Schema

JSON schema for `/lean4:review` external hooks and Codex integration.

---

## Hook Input Schema

Input sent to hooks via stdin (or to Codex via `--codex`):

```json
{
  "version": "1.0",
  "request_type": "review",
  "mode": "batch",
  "focus": {
    "scope": "sorry",
    "file": "Core.lean",
    "line": 89
  },
  "files": [
    {
      "path": "Core.lean",
      "content": "-- File content here...",
      "sorries": [
        {
          "line": 89,
          "column": 4,
          "goal": "⊢ Continuous f",
          "hypotheses": ["f : ℝ → ℝ", "h : Differentiable ℝ f"]
        }
      ],
      "axioms": [],
      "diagnostics": [
        {
          "line": 42,
          "column": 10,
          "severity": "warning",
          "message": "unused variable `x`"
        }
      ]
    }
  ],
  "build_status": "passing",
  "preferences": {
    "focus": "completeness",
    "verbosity": "detailed"
  }
}
```

### Field Descriptions

| Field | Type | Description |
|-------|------|-------------|
| `version` | string | Schema version (currently "1.0") |
| `request_type` | string | Always "review" for review hooks |
| `focus` | object | Scope of this review |
| `focus.scope` | string | "sorry", "deps", "file", "changed", or "project" |
| `focus.file` | string | Target file (if applicable) |
| `focus.line` | number | Target line (for sorry/deps scope) |
| `mode` | string | "batch" (default) or "stuck" (triage) — top-level field |
| `files` | array | Files being reviewed |
| `files[].path` | string | Relative path to file |
| `files[].content` | string | Full file content |
| `files[].sorries` | array | Incomplete proofs in file |
| `files[].sorries[].line` | number | Line number (1-indexed) |
| `files[].sorries[].column` | number | Column number (0-indexed) |
| `files[].sorries[].goal` | string | Proof goal at sorry |
| `files[].sorries[].hypotheses` | array | Available hypotheses |
| `files[].axioms` | array | Custom axioms used |
| `files[].diagnostics` | array | Compiler warnings/errors |
| `build_status` | string | "passing" or "failing" |
| `preferences.focus` | string | "completeness", "style", or "performance" |
| `preferences.verbosity` | string | "minimal", "normal", or "detailed" |

---

## Hook Output Schema

Output returned by hooks (via stdout):

```json
{
  "version": "1.0",
  "suggestions": [
    {
      "file": "Core.lean",
      "line": 89,
      "column": 4,
      "severity": "hint",
      "category": "sorry",
      "message": "Try tendsto_atTop from Mathlib.Topology.Order.Basic",
      "fix": "exact tendsto_atTop.mpr fun n => ⟨n, fun m hm => hm⟩"
    },
    {
      "file": "Core.lean",
      "line": 42,
      "severity": "style",
      "category": "naming",
      "message": "Consider renaming `aux` to describe its purpose"
    }
  ],
  "summary": {
    "total_suggestions": 2,
    "by_severity": {
      "hint": 1,
      "style": 1
    }
  }
}
```

### Suggestion Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `file` | string | Yes | File the suggestion applies to |
| `line` | number | Yes | Line number (1-indexed) |
| `column` | number | No | Column number (0-indexed) |
| `severity` | string | Yes | "error", "warning", "hint", or "style" |
| `category` | string | No | "sorry", "axiom", "naming", "golf", "import" |
| `message` | string | Yes | Human-readable suggestion |
| `fix` | string | No | Suggested code (internal hooks only; external reviews omit this) |

---

## Codex Integration

**Note:** Codex CLI's `/review` command is interactive-only—there's no `codex review --stdin` for automation. When using `--codex`, the review command:

1. Collects file context using the input schema above
2. Displays formatted context for manual handoff to Codex CLI
3. User runs `codex` → `/review` interactively, or uses `codex exec` with a prompt
4. User pastes suggestions back; review command parses and merges them

For CI automation, use `codex exec` with structured output. See [review.md](../../../commands/review.md#codex-integration) for details.

### Example Custom Hook Script

```python
#!/usr/bin/env python3
"""
Example INTERNAL hook for /lean4:review --hook=./my_hook.py

Internal hooks can include `fix` fields with suggested code.
External reviews (--codex) should omit `fix` and provide strategic advice only.
"""

import json
import sys

def analyze_sorries(files):
    """Generate suggestions for sorries."""
    suggestions = []
    for f in files:
        for sorry in f.get("sorries", []):
            goal = sorry.get("goal", "")

            # Simple heuristic: suggest tactics based on goal shape
            if "Continuous" in goal:
                suggestions.append({
                    "file": f["path"],
                    "line": sorry["line"],
                    "severity": "hint",
                    "category": "sorry",
                    "message": "Try `continuity` or search for Continuous.* lemmas",
                    "fix": "continuity"
                })
            elif "=" in goal and "+" in goal:
                suggestions.append({
                    "file": f["path"],
                    "line": sorry["line"],
                    "severity": "hint",
                    "category": "sorry",
                    "message": "Arithmetic goal - try `ring` or `omega`",
                    "fix": "ring"
                })
    return suggestions

def main():
    # Read input from stdin
    input_data = json.load(sys.stdin)

    # Generate suggestions
    suggestions = analyze_sorries(input_data.get("files", []))

    # Output result
    output = {
        "version": "1.0",
        "suggestions": suggestions,
        "summary": {
            "total_suggestions": len(suggestions),
            "by_severity": {"hint": len(suggestions)}
        }
    }

    json.dump(output, sys.stdout, indent=2)

if __name__ == "__main__":
    main()
```

### Usage

```bash
# Run review with custom hook
/lean4:review --hook=./my_hook.py

# Run review with Codex (interactive handoff)
/lean4:review --codex

# Export JSON for external processing
/lean4:review --json > review.json
```

---

## Error Handling

Hooks should handle errors gracefully:

```json
{
  "version": "1.0",
  "suggestions": [],
  "error": {
    "code": "PARSE_ERROR",
    "message": "Failed to parse file Core.lean at line 42"
  }
}
```

The review command will report hook errors but continue with other analysis.

---

## Hook Performance Tips

For rate-limited APIs (Codex, etc.):
- **Trim content:** Include only ±50 lines around each sorry, not full file
- **Batch sorries:** Group multiple sorries per API call when possible
- **Cache by goal:** Same goal/context → same suggestions

Use `preferences.verbosity` to signal desired response detail level.

---

## See Also

- [/lean4:review](../../../commands/review.md) - Review command documentation
- [mathlib-style.md](mathlib-style.md) - Style guidelines for suggestions
