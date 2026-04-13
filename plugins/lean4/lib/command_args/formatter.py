"""Format ParseResult as a validated-invocation block and parse it back."""
from __future__ import annotations

from .types import EnforcementClass, ParseResult, ResolvedFlag, Source


def format_validated_block(result: ParseResult) -> str:
    """Serialize a ParseResult into a fenced validated-invocation markdown block."""
    lines: list[str] = []
    lines.append("```validated-invocation")
    lines.append(f"command: {result.command}")
    lines.append(f"raw_tail: {result.raw_tail}")

    # Positionals
    lines.append("positionals:")
    if result.positionals:
        for name, value in result.positionals.items():
            lines.append(f"  {name}: {value}")
    else:
        lines.append("  (none)")

    # Options — structured per-flag entries
    lines.append("options:")
    for name, rf in result.options.items():
        lines.append(f"  {name}:")
        lines.append(f"    value: {_format_value(rf.value)}")
        lines.append(f"    source: {rf.source}")
        lines.append(f"    enforcement: {rf.enforcement}")
        if rf.coerced_from is not None:
            lines.append(f"    coerced_from: {_format_value(rf.coerced_from)}")

    # Coercions
    lines.append("coercions:")
    if result.coercions:
        for note in result.coercions:
            lines.append(f"  - {note}")
    else:
        lines.append("  (none)")

    # Warnings
    lines.append("warnings:")
    if result.warnings:
        for note in result.warnings:
            lines.append(f"  - {note}")
    else:
        lines.append("  (none)")

    # Errors
    lines.append(f"errors: {result.errors!r}")

    lines.append("```")
    return "\n".join(lines)


def parse_validated_block(text: str) -> ParseResult:
    """Parse a validated-invocation fenced block back into a ParseResult.

    This is the exact inverse of format_validated_block.
    """
    # Extract the block content between the fences
    block_lines = _extract_block_lines(text)

    result = ParseResult(command="", raw_tail="")
    section = None

    i = 0
    while i < len(block_lines):
        line = block_lines[i]

        if line.startswith("command: "):
            result.command = line[len("command: "):]
        elif line.startswith("raw_tail: "):
            result.raw_tail = line[len("raw_tail: "):]
        elif line == "positionals:":
            section = "positionals"
        elif line == "options:":
            section = "options"
        elif line == "coercions:":
            section = "coercions"
        elif line == "warnings:":
            section = "warnings"
        elif line.startswith("errors: "):
            import ast
            result.errors = ast.literal_eval(line[len("errors: "):])
        elif section == "positionals" and line.startswith("  ") and line.strip() != "(none)":
            key, _, val = line.strip().partition(": ")
            result.positionals[key] = val
        elif section == "options" and line.startswith("  ") and not line.startswith("    "):
            # New flag entry
            flag_name = line.strip().rstrip(":")
            flag_data: dict[str, str] = {}
            i += 1
            while i < len(block_lines) and block_lines[i].startswith("    "):
                sub_line = block_lines[i].strip()
                sub_key, _, sub_val = sub_line.partition(": ")
                flag_data[sub_key] = sub_val
                i += 1
            result.options[flag_name] = ResolvedFlag(
                value=_parse_value(flag_data.get("value", "None")),
                source=flag_data.get("source", "default"),  # type: ignore[arg-type]
                enforcement=flag_data.get("enforcement", "startup-validated"),  # type: ignore[arg-type]
                coerced_from=_parse_value(flag_data["coerced_from"]) if "coerced_from" in flag_data else None,
            )
            continue  # already advanced i past the sub-entries
        elif section == "coercions" and line.startswith("  - "):
            result.coercions.append(line[4:])
        elif section == "warnings" and line.startswith("  - "):
            result.warnings.append(line[4:])

        i += 1

    return result


def _extract_block_lines(text: str) -> list[str]:
    """Extract lines between ```validated-invocation and ``` fences."""
    lines = text.split("\n")
    in_block = False
    block_lines: list[str] = []
    for line in lines:
        if line.strip() == "```validated-invocation":
            in_block = True
            continue
        if in_block and line.strip() == "```":
            break
        if in_block:
            block_lines.append(line)
    return block_lines


def _format_value(v: object) -> str:
    """Format a value for the block with unambiguous type encoding.

    Strings are double-quoted so they survive round-trip without being
    reinterpreted as None, bool, or int. This makes the block a truly
    lossless serialization: draft --source=123 stays the string "123",
    not the integer 123.
    """
    if v is None:
        return "None"
    if isinstance(v, bool):
        return str(v).lower()
    if isinstance(v, int):
        return str(v)
    # All strings are quoted to prevent ambiguity with None/true/false/int
    return f'"{v}"'


def _parse_value(s: str) -> object:
    """Parse a value string from the block back into a Python object."""
    if s == "None":
        return None
    if s == "true":
        return True
    if s == "false":
        return False
    # Quoted string — strip quotes and return as str
    if len(s) >= 2 and s.startswith('"') and s.endswith('"'):
        return s[1:-1]
    try:
        return int(s)
    except ValueError:
        pass
    return s
