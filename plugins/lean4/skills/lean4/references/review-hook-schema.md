# Review Hook Schema

JSON schema for `/lean4:review` external hooks and Codex integration.

**Normative machine-readable schemas (v2):** the enums and structure below are
documentation of two shipped JSON Schema files — do not treat the tables as an
independent source of truth:

- Output (Codex `--output-schema` and hook stdout): [`lean4-review-schema.json`](lean4-review-schema.json)
- Input (hook stdin): [`lean4-review-input-schema.json`](lean4-review-input-schema.json)

The output schema is OpenAI Structured Outputs constrained (object root,
`additionalProperties: false` everywhere, every property required, semantic
optionals as nullable types). Category values are the mathlib-review taxonomy
(#114) plus legacy-accepted values (`sorry, axiom, style, structure, naming,
golf, import`) — accepted, not normalized.

---

## Hook Input Schema

Input sent to custom hooks via stdin. For `--codex`, this context is displayed for manual copy/paste to Codex CLI (see [Codex Integration](#codex-integration)):

```json
{
  "version": "2.0",
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
| `version` | string | Schema version (currently "2.0") |
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

Every suggestion carries all fields (nulls where a value is absent), per the
Structured-Outputs output schema:

```json
{
  "version": "2.0",
  "suggestions": [
    {
      "file": "Core.lean",
      "line": 89,
      "column": 4,
      "severity": "hint",
      "category": "sorry",
      "rule_id": null,
      "message": "Try tendsto_atTop from Mathlib.Topology.Order.Basic",
      "fix": "exact tendsto_atTop.mpr fun n ↦ ⟨n, fun m hm ↦ hm⟩"
    },
    {
      "file": "Core.lean",
      "line": 42,
      "column": null,
      "severity": "style",
      "category": "naming",
      "rule_id": null,
      "message": "Consider renaming `aux` to describe its purpose",
      "fix": null
    }
  ],
  "summary": {
    "total_suggestions": 2,
    "by_severity": {"error": null, "warning": null, "advisory": null, "hint": 1, "style": 1}
  }
}
```

### Suggestion Fields

Enums are normative in [`lean4-review-schema.json`](lean4-review-schema.json).
Under Structured Outputs every field is present; "required-but-nullable" means
the value may be `null` (e.g. a PR-level `metadata` finding has no `file`/`line`).

| Field | Type | Description |
|-------|------|-------------|
| `file` | string \| null | File the suggestion applies to (`null` for a location-less finding) |
| `line` | integer \| null | Line number (1-indexed; `null` when there is no location) |
| `column` | integer \| null | Column number (0-indexed; `null` when unknown) |
| `severity` | enum | `error`, `warning`, `advisory`, `hint`; legacy `style` accepted |
| `category` | enum | Taxonomy vocabulary + legacy-accepted values — see the JSON schema |
| `rule_id` | string \| null | Specific rule within a category, e.g. `vacuous-api` under `api`; `null` when unset |
| `message` | string | Human-readable suggestion |
| `fix` | string \| null | Suggested code (internal hooks); external Codex reviews set `null` |

---

## Codex Integration

**Note:** Codex CLI's `/review` command is interactive-only—there's no `codex review --stdin` for automation. When using `--codex`, the review command:

1. Collects file context using the input schema above
2. Displays formatted context for manual handoff to Codex CLI
3. User runs `codex` → `/review` interactively, or uses `codex exec` with a prompt
4. User pastes suggestions back; review command parses and merges them

For CI automation, use `codex exec` with structured output. See [review.md](https://github.com/cameronfreer/lean4-skills/blob/main/plugins/lean4/commands/review.md#codex-integration) (live repository copy) for details.

### Example Custom Hook Script

```python
#!/usr/bin/env python3
"""
Example INTERNAL hook for /lean4:review --hook=./my_hook.py

Internal hooks can include `fix` fields with suggested code.
External reviews (--codex) set `fix` to null and provide strategic advice only.
Simplified for illustration — a fully conforming hook emits every field
(including column, rule_id, and the full by_severity object) per
lean4-review-schema.json.
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
        "version": "2.0",
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
  "version": "2.0",
  "suggestions": [],
  "summary": {"total_suggestions": 0, "by_severity": {"error": null, "warning": null, "advisory": null, "hint": null, "style": null}},
  "error": "PARSE_ERROR: Failed to parse file Core.lean at line 42"
}
```

`error` is a nullable string — a message when the reviewer could not complete
(with `suggestions` then empty), `null` on success.

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

- [`/lean4:review`](https://github.com/cameronfreer/lean4-skills/blob/main/plugins/lean4/commands/review.md) - Review command documentation (live repository copy)
- [mathlib-style.md](mathlib-style.md) - Style guidelines for suggestions
