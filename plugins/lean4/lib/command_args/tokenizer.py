"""shlex-based POSIX tokenizer for slash-command raw tails."""

from __future__ import annotations

import shlex


def tokenize(raw_tail: str) -> list[str]:
    """Split a raw tail into tokens using POSIX shell quoting rules.

    Handles --flag=value, --flag value, "quoted strings", and backslash escapes.
    Returns an empty list for empty/whitespace-only input.
    """
    stripped = raw_tail.strip()
    if not stripped:
        return []
    try:
        return shlex.split(stripped)
    except ValueError as e:
        raise ValueError(f"Failed to tokenize input: {e}") from e


def normalize_flags(tokens: list[str]) -> list[str]:
    """Expand --flag=value into [--flag, value] and pass other tokens through."""
    result: list[str] = []
    for token in tokens:
        if token.startswith("--") and "=" in token:
            flag, _, value = token.partition("=")
            result.append(flag)
            result.append(value)
        else:
            result.append(token)
    return result
