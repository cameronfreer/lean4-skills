#!/usr/bin/env python3
"""
Parse Lean compiler errors into structured JSON for repair routing.

Output schema:
{
  "errorHash": "type_mismatch_42",
  "errorType": "type_mismatch",
  "message": "type mismatch at...",
  "file": "Foo.lean",
  "line": 42,
  "column": 10,
  "goal": "⊢ Continuous f",
  "localContext": ["h1 : Measurable f", "h2 : Integrable f μ"],
  "codeSnippet": "theorem foo : Continuous f := by\n  exact h1  -- ❌ type mismatch\n",
  "suggestionKeywords": ["continuous", "measurable", "apply"]
}

Inspired by APOLLO's compiler-feedback-driven repair approach
https://arxiv.org/abs/2505.05758
"""

import json
import re
import sys
import hashlib
from pathlib import Path
from typing import Optional


ERROR_PATTERNS = [
    (r"type mismatch", "type_mismatch"),
    (r"don't know how to synthesize implicit argument", "synth_implicit"),
    (r"unsolved goals", "unsolved_goals"),
    (r"unknown identifier '([^']+)'", "unknown_ident"),
    (r"failed to synthesize instance", "synth_instance"),
    (r"tactic 'sorry' has not been implemented", "sorry_present"),
    (r"maximum recursion depth", "recursion_depth"),
    (r"deterministic timeout", "timeout"),
    (r"expected type", "type_expected"),
    (r"application type mismatch", "app_type_mismatch"),
]


def parse_location(line: str) -> Optional[dict]:
    """Extract file:line:column from error line."""
    match = re.match(r"^([^:]+):(\d+):(\d+):", line)
    if match:
        return {
            "file": match.group(1),
            "line": int(match.group(2)),
            "column": int(match.group(3))
        }
    return None


def classify_error(message: str) -> str:
    """Classify error type from message."""
    for pattern, error_type in ERROR_PATTERNS:
        if re.search(pattern, message, re.IGNORECASE):
            return error_type
    return "unknown"


def extract_goal(error_text: str) -> Optional[str]:
    """Extract goal state from error (if present)."""
    # Look for lines starting with ⊢
    goal_match = re.search(r"⊢\s+(.+)", error_text)
    if goal_match:
        return goal_match.group(1).strip()
    return None


def extract_local_context(error_text: str) -> list[str]:
    """Extract local context (hypotheses) from error."""
    # Look for lines like "h1 : Type" before ⊢
    context = []
    in_context = False
    for line in error_text.split("\n"):
        if "⊢" in line:
            in_context = False
        if in_context and ":" in line:
            # Extract hypothesis
            hyp = line.strip()
            if hyp and not hyp.startswith("case"):
                context.append(hyp)
        if "context:" in line.lower() or line.strip().endswith(":"):
            in_context = True
    return context


def extract_code_snippet(file_path: str, line: int, context_lines: int = 3) -> str:
    """Extract code snippet around error location."""
    try:
        with open(file_path) as f:
            lines = f.readlines()
        start = max(0, line - context_lines - 1)
        end = min(len(lines), line + context_lines)
        snippet_lines = []
        for i in range(start, end):
            prefix = "❌ " if i == line - 1 else "   "
            snippet_lines.append(f"{prefix}{i+1:4d} | {lines[i].rstrip()}")
        return "\n".join(snippet_lines)
    except Exception:
        return ""


def extract_suggestion_keywords(message: str) -> list[str]:
    """Extract relevant keywords for search/suggestions."""
    keywords = []
    # Extract identifiers in single quotes
    keywords.extend(re.findall(r"'([^']+)'", message))
    # Extract common type class names
    for term in ["Continuous", "Measurable", "Integrable", "Differentiable",
                 "Fintype", "DecidableEq", "Group", "Ring", "Field"]:
        if term.lower() in message.lower():
            keywords.append(term)
    return list(set(keywords))[:10]  # Limit to 10


def compute_error_hash(error_type: str, file: str, line: int) -> str:
    """Compute deterministic hash for error tracking."""
    content = f"{error_type}:{file}:{line}"
    return hashlib.sha256(content.encode()).hexdigest()[:12]


def parse_lean_errors(error_file: Path) -> dict:
    """Parse Lean error output file into structured JSON."""
    with open(error_file) as f:
        error_text = f.read()

    lines = error_text.strip().split("\n")
    if not lines:
        return {"error": "No error output"}

    # First line usually has location
    location = parse_location(lines[0])
    if not location:
        location = {"file": "unknown", "line": 0, "column": 0}

    # Full message is everything after the location line
    message = error_text[len(lines[0]):].strip() if len(lines) > 1 else ""

    # For classification, use the full error text (includes first line)
    error_type = classify_error(error_text)
    error_hash = compute_error_hash(error_type, location["file"], location["line"])

    result = {
        "errorHash": error_hash,
        "errorType": error_type,
        "message": message[:500],  # Truncate long messages
        "file": location["file"],
        "line": location["line"],
        "column": location["column"],
        "goal": extract_goal(error_text),
        "localContext": extract_local_context(error_text),
        "codeSnippet": extract_code_snippet(location["file"], location["line"]),
        "suggestionKeywords": extract_suggestion_keywords(message),
    }

    return result


def main():
    if len(sys.argv) < 2:
        print("Usage: parseLeanErrors.py ERROR_FILE", file=sys.stderr)
        sys.exit(1)

    error_file = Path(sys.argv[1])
    if not error_file.exists():
        print(f"Error file not found: {error_file}", file=sys.stderr)
        sys.exit(1)

    result = parse_lean_errors(error_file)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
