#!/usr/bin/env python3
"""Append-only writer for /lean4:disprove counterexample artifacts.

Reads the full theorem block from stdin and appends it to --scope-file if a
declaration with the same theorem name is not already present. Idempotent
on repeat invocation with identical inputs.

Safety:
    - Only appends; never rewrites or deletes existing content.
    - Refuses any file path that does not end in .lean.
    - Refuses to operate if the requested theorem name already appears in the
      file (treated as "already present" — exit 0, no change).

Usage:
    disprove_emit_artifact.py --scope-file=PATH --theorem-name=NAME [--dry-run]
    cat snippet.lean | disprove_emit_artifact.py --scope-file=PATH ...

If --scope-file=- (or omitted with --dry-run), the snippet is echoed to
stdout instead of being written.

Exit codes:
    0 — wrote (or determined idempotent / dry-run)
    2 — bad invocation or refused operation (error on stderr)
"""
from __future__ import annotations

import argparse
import os
import re
import sys


def _parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(add_help=True)
    p.add_argument("--scope-file", required=True,
                   help="Path to .lean file to append to, or '-' for stdout.")
    p.add_argument("--theorem-name", required=True,
                   help="Name of the theorem in the snippet (used for idempotency check).")
    p.add_argument("--dry-run", action="store_true",
                   help="Print the snippet to stdout instead of writing.")
    return p.parse_args(argv[1:])


def _theorem_already_present(content: str, name: str) -> bool:
    """Return True iff a declaration named NAME already appears at start of a line.

    Recognises `theorem`, `lemma`, `def`, `abbrev`, and `instance`, with any
    leading combination of `private`, `protected`, `noncomputable`, `partial`,
    or `unsafe` modifiers. Best-effort: `lake env lean` is the authoritative
    collision check; this is the cheap idempotency probe used to avoid
    re-appending an identical artifact on retry.
    """
    pattern = re.compile(
        r"^(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance)\s+" + re.escape(name) + r"\b",
        re.MULTILINE,
    )
    return bool(pattern.search(content))


def main(argv: list[str]) -> int:
    args = _parse_args(argv)
    snippet = sys.stdin.read()
    if not snippet.strip():
        print("error: empty snippet on stdin", file=sys.stderr)
        return 2

    if args.scope_file == "-" or args.dry_run:
        sys.stdout.write(snippet)
        if not snippet.endswith("\n"):
            sys.stdout.write("\n")
        return 0

    if not args.scope_file.endswith(".lean"):
        print(
            f"error: --scope-file must end in .lean (got {args.scope_file!r})",
            file=sys.stderr,
        )
        return 2

    if not os.path.exists(args.scope_file):
        print(
            f"error: --scope-file does not exist: {args.scope_file}",
            file=sys.stderr,
        )
        return 2

    with open(args.scope_file, "r", encoding="utf-8") as f:
        content = f.read()

    if _theorem_already_present(content, args.theorem_name):
        print(
            f"note: theorem {args.theorem_name!r} already present in "
            f"{args.scope_file}; no change.",
            file=sys.stderr,
        )
        return 0

    needs_leading_newline = content and not content.endswith("\n")
    block = ("\n" if needs_leading_newline else "") + snippet
    if not block.endswith("\n"):
        block += "\n"

    try:
        with open(args.scope_file, "a", encoding="utf-8") as f:
            f.write(block)
    except PermissionError as exc:
        print(
            f"error: cannot append to {args.scope_file!r}: {exc}",
            file=sys.stderr,
        )
        return 2
    except OSError as exc:
        print(
            f"error: I/O error appending to {args.scope_file!r}: {exc}",
            file=sys.stderr,
        )
        return 2

    print(
        f"wrote {args.theorem_name!r} to {args.scope_file}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
