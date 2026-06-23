#!/usr/bin/env python3
"""Append-only writer for /lean4:disprove counterexample artifacts.

Reads the full theorem block from stdin and appends it to --scope-file unless a
declaration with the same theorem name is already present, in which case the
existing declaration is compared against the incoming snippet:

    - no declaration with that name        → append it
    - same name, identical (normalized)    → idempotent, no change (exit 0)
    - same name, DIFFERENT body/type       → hard collision, refuse (exit 2)

The collision case is the important safety property: a stale or unrelated
`T_counterexample` must NOT be silently treated as the freshly-found refutation.

Safety:
    - Only appends; never rewrites or deletes existing content.
    - Refuses any file path that does not end in .lean.
    - Refuses (exit 2) if the requested name already exists with a different body.

Usage:
    disprove_emit_artifact.py --scope-file=PATH --theorem-name=NAME [--dry-run]
    cat snippet.lean | disprove_emit_artifact.py --scope-file=PATH ...

If --scope-file=- (or omitted with --dry-run), the snippet is echoed to
stdout instead of being written.

Exit codes:
    0 — wrote (or determined idempotent / dry-run)
    2 — bad invocation, refused operation, or name collision (error on stderr)
"""
from __future__ import annotations

import argparse
import os
import re
import sys

# Top-level declaration header (any name) — used to find where an existing
# declaration block ends (the next top-level decl starts the next block).
_DECL_KEYWORDS = "theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom"
_MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"


def _parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(add_help=True)
    p.add_argument("--scope-file", required=True,
                   help="Path to .lean file to append to, or '-' for stdout.")
    p.add_argument("--theorem-name", required=True,
                   help="Name of the theorem in the snippet (used for the collision check).")
    p.add_argument("--dry-run", action="store_true",
                   help="Print the snippet to stdout instead of writing.")
    return p.parse_args(argv[1:])


def _extract_declaration_block(content: str, name: str) -> str | None:
    """Return the existing top-level declaration block named NAME, or None.

    Recognises `theorem`, `lemma`, `def`, `abbrev`, and `instance`, with any
    leading combination of `private`, `protected`, `noncomputable`, `partial`,
    or `unsafe` modifiers. The block runs from the declaration header through
    the line before the next top-level declaration (or EOF), so multi-line
    proof bodies are captured whole. Best-effort: `lake env lean` is the
    authoritative check; this is the cheap collision/idempotency probe.
    """
    header = re.compile(
        r"^" + _MODIFIERS + r"(?:theorem|lemma|def|abbrev|instance)\s+"
        + re.escape(name) + r"\b",
        re.MULTILINE,
    )
    m = header.search(content)
    if not m:
        return None
    nxt = re.compile(r"^" + _MODIFIERS + r"(?:" + _DECL_KEYWORDS + r")\b", re.MULTILINE)
    after = nxt.search(content, m.end())
    end = after.start() if after else len(content)
    return content[m.start():end]


def _normalize(block: str) -> str:
    """Normalize a declaration block for byte-for-byte comparison.

    Strips trailing whitespace on each line and leading/trailing blank lines,
    so an appended block (with a leading separator newline) compares equal to
    the same declaration on stdin.
    """
    lines = [ln.rstrip() for ln in block.splitlines()]
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    return "\n".join(lines)


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

    existing = _extract_declaration_block(content, args.theorem_name)
    if existing is not None:
        if _normalize(existing) == _normalize(snippet):
            print(
                f"note: theorem {args.theorem_name!r} already present (identical) in "
                f"{args.scope_file}; no change.",
                file=sys.stderr,
            )
            return 0
        print(
            f"error: theorem {args.theorem_name!r} already exists in "
            f"{args.scope_file} with a different body; refusing to append a "
            f"conflicting declaration (collision).",
            file=sys.stderr,
        )
        return 2

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
