#!/usr/bin/env python3
"""Classify a /lean4:disprove TARGET argument into a structured descriptor.

Usage:
    disprove_target_resolve.py <target>

Stdout: JSON describing the target.
    {"kind": "file-line", "file": "Foo/Bar.lean", "line": 42}
    {"kind": "qualified-name", "name": "MyNs.SubNs.myThm"}

Exit codes:
    0 — successful classification (JSON on stdout)
    2 — unrecognized target shape (error on stderr)
"""

from __future__ import annotations

import json
import os
import sys

# lib/scripts/disprove_target_resolve.py -> dirname = lib/scripts -> parent = lib
_LIB_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _LIB_ROOT not in sys.path:
    sys.path.insert(0, _LIB_ROOT)

from command_args.target_patterns import (  # noqa: E402
    FILE_LINE_RE as _FILE_LINE_RE,
)
from command_args.target_patterns import (  # noqa: E402
    QUALIFIED_NAME_RE as _QUALIFIED_NAME_RE,
)


def classify(target: str) -> dict[str, object]:
    """Classify a target string into a structured descriptor.

    Args:
        target: A target argument as accepted by ``/lean4:disprove``.

    Returns:
        Either ``{"kind": "file-line", "file": str, "line": int}`` for
        ``File.lean:LINE`` inputs (line is always ≥ 1), or
        ``{"kind": "qualified-name", "name": str}`` for dotted names.

    Raises:
        ValueError: If the target matches neither shape — including a
            ``.lean`` path missing ``:LINE``, a non-positive line number,
            an inline ``Prop`` expression, or any other malformed input.
    """
    m = _FILE_LINE_RE.match(target)
    if m:
        return {
            "kind": "file-line",
            "file": m.group("file"),
            "line": int(m.group("line")),
        }
    if target.endswith(".lean"):
        raise ValueError(
            f"target {target!r}: file path is missing ':LINE'. "
            "Use 'File.lean:LINE' (e.g. 'Foo.lean:42')."
        )
    if _QUALIFIED_NAME_RE.match(target):
        return {"kind": "qualified-name", "name": target}
    raise ValueError(
        f"target {target!r}: expected 'File.lean:LINE' or "
        "'Namespace.theoremName' (inline Props not supported in v1)."
    )


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(
            "usage: disprove_target_resolve.py <target>",
            file=sys.stderr,
        )
        return 2
    try:
        result = classify(argv[1])
    except ValueError as e:
        print(str(e), file=sys.stderr)
        return 2
    json.dump(result, sys.stdout)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
