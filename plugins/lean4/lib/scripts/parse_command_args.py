#!/usr/bin/env python3
"""Standalone CLI for the lean4 slash-command parser.

Usage:
    python3 parse_command_args.py <command> [--cwd PATH] -- <raw tail>

Exit codes:
    0 — success (prints ParseResult JSON to stdout)
    1 — usage error (bad CLI arguments)
    2 — validation error (prints error JSON to stdout)
"""

from __future__ import annotations

import json
import os
import sys

# lib/scripts/parse_command_args.py -> dirname = lib/scripts -> parent = lib
_LIB_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _LIB_ROOT not in sys.path:
    sys.path.insert(0, _LIB_ROOT)

from command_args import COMMAND_SPECS, parse_invocation  # noqa: E402


def main() -> int:
    args = sys.argv[1:]

    if not args or args[0] in ("-h", "--help"):
        print(__doc__, file=sys.stderr)
        return 1

    # Parse CLI: <command> [--cwd PATH] -- <single raw tail string>
    # The raw tail is passed as exactly ONE shell argument after "--" so that
    # quoting boundaries are preserved. Using multiple args after "--" would
    # lose the original quoting (e.g. -- "Theorem 1" becomes two words).
    command_name = args[0]
    cwd = os.getcwd()
    raw_tail: str | None = None
    past_separator = False

    i = 1
    while i < len(args):
        if past_separator:
            if raw_tail is not None:
                print(
                    "Error: expected exactly one argument after '--' (the raw tail "
                    "as a single string). Got multiple arguments. Wrap the tail in "
                    "quotes: -- '\"Theorem 1\" --mode=attempt'",
                    file=sys.stderr,
                )
                return 1
            raw_tail = args[i]
        elif args[i] == "--":
            past_separator = True
        elif args[i] == "--cwd" and i + 1 < len(args):
            cwd = args[i + 1]
            i += 1
        else:
            print(
                f"Error: unexpected argument {args[i]!r} before '--'", file=sys.stderr
            )
            return 1
        i += 1

    if not past_separator:
        print("Error: missing '--' separator before raw tail", file=sys.stderr)
        return 1

    if raw_tail is None:
        raw_tail = ""

    # Look up spec
    spec = COMMAND_SPECS.get(command_name)
    if spec is None:
        available = ", ".join(sorted(COMMAND_SPECS.keys()))
        print(
            f"Error: unknown command {command_name!r}; available: {available}",
            file=sys.stderr,
        )
        return 1

    # Normalize cwd and parse
    cwd = os.path.abspath(cwd)
    result = parse_invocation(spec, raw_tail, cwd=cwd)

    if result.errors:
        json.dump(
            {"errors": result.errors, "command": command_name}, sys.stdout, indent=2
        )
        sys.stdout.write("\n")
        return 2

    # Success — print full result as JSON
    json.dump(result.to_dict(), sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
