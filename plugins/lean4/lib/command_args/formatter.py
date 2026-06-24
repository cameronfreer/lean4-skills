"""Format ParseResult as a validated-invocation block and parse it back.

The block is a fenced markdown block with the label ``validated-invocation``
containing pretty-printed JSON from ``result.to_dict()``. Using real JSON
inside the fence eliminates the ad-hoc escaping problems of the previous
line-based format (multiline input, embedded fences, string/int ambiguity).
"""

from __future__ import annotations

import json

from .types import ParseResult, ResolvedFlag


def format_validated_block(result: ParseResult) -> str:
    """Serialize a ParseResult into a fenced validated-invocation block.

    The block body is pretty-printed JSON from ``result.to_dict()``.
    """
    body = json.dumps(result.to_dict(), indent=2, ensure_ascii=False)
    return f"```validated-invocation\n{body}\n```"


def parse_validated_block(text: str) -> ParseResult:
    """Parse a validated-invocation fenced block back into a ParseResult.

    This is the exact inverse of ``format_validated_block``.
    """
    json_str = _extract_block_body(text)
    data = json.loads(json_str)

    positionals: dict[str, str] = data.get("positionals", {})
    options: dict[str, ResolvedFlag] = {}
    for name, rf_data in data.get("options", {}).items():
        options[name] = ResolvedFlag(
            value=rf_data["value"],
            source=rf_data["source"],
            enforcement=rf_data["enforcement"],
            coerced_from=rf_data.get("coerced_from"),
        )

    return ParseResult(
        command=data["command"],
        raw_tail=data["raw_tail"],
        positionals=positionals,
        options=options,
        coercions=data.get("coercions", []),
        warnings=data.get("warnings", []),
        errors=data.get("errors", []),
    )


def _extract_block_body(text: str) -> str:
    """Extract the JSON body between ```validated-invocation and ``` fences."""
    lines = text.split("\n")
    in_block = False
    body_lines: list[str] = []
    for line in lines:
        if line.strip() == "```validated-invocation":
            in_block = True
            continue
        if in_block and line.strip() == "```":
            break
        if in_block:
            body_lines.append(line)
    if not body_lines:
        raise ValueError("No validated-invocation block found in text")
    return "\n".join(body_lines)
