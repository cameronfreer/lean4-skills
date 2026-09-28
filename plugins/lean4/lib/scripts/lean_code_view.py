#!/usr/bin/env python3
"""lean_code_view.py — code-only mirror of a Lean source tree (issue #185).

Usage: lean_code_view.py SRC_DIR MIRROR_DIR

Copies every ``*.lean`` file under SRC_DIR to the same relative path under
MIRROR_DIR with comments and string literals blanked out: each stripped
character becomes a space, so line numbers, columns and token boundaries
are preserved and any grep-based tool can run over the mirror and report
locations that are valid in the original tree.

The scanner is a character-level port of ``sorry_analyzer.strip_lean_
comments_and_strings`` (line comments ``--``, nested block comments
``/- … -/`` including docstrings, string literals with backslash escapes),
hardened for this use: the string state is threaded across lines as well
as the block-comment depth, so a string literal that spans lines is
blanked on every line it covers. No Lean parsing is attempted; this is
enough for reference counting, not for semantics.

Exit status: 0 on success (prints the number of files mirrored); 1 on a
usage error; 2 if any file could not be read or written — a caller must
treat that as "cannot analyze", never as "no findings".
"""

from __future__ import annotations

import os
import sys


def code_view_line(line: str, depth: int, in_string: bool) -> tuple[str, int, bool]:
    """Blank comments and strings in one line; return the new state.

    ``depth`` is the block-comment nesting depth and ``in_string`` whether a
    string literal is open at the start of the line. The returned text has
    exactly the same length as ``line``.
    """
    out: list[str] = []
    i = 0
    n = len(line)
    while i < n:
        ch = line[i]
        nxt = line[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if in_string:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
                continue
            if ch == '"':
                in_string = False
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        if ch == "-" and nxt == "-":
            # line comment: blank the rest of the line, keep the newline
            rest = line[i:]
            out.append("\n" if rest.endswith("\n") else "")
            out.insert(
                len(out) - 1, " " * (len(rest) - (1 if rest.endswith("\n") else 0))
            )
            break
        if ch == "/" and nxt == "-":
            depth += 1
            out.append("  ")
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out), depth, in_string


def code_view(text: str) -> str:
    depth = 0
    in_string = False
    pieces: list[str] = []
    for line in text.splitlines(keepends=True):
        stripped, depth, in_string = code_view_line(line, depth, in_string)
        pieces.append(stripped)
    return "".join(pieces)


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print("usage: lean_code_view.py SRC_DIR MIRROR_DIR", file=sys.stderr)
        return 1
    src, mirror = argv[1], argv[2]
    if not os.path.isdir(src):
        print(f"error: {src!r} is not a directory", file=sys.stderr)
        return 1
    count = 0
    for root, _dirs, files in os.walk(src):
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(root, name)
            rel = os.path.relpath(path, src)
            dest = os.path.join(mirror, rel)
            try:
                with open(path, encoding="utf-8", errors="surrogateescape") as f:
                    text = f.read()
                os.makedirs(os.path.dirname(dest), exist_ok=True)
                with open(dest, "w", encoding="utf-8", errors="surrogateescape") as f:
                    f.write(code_view(text))
            except OSError as ex:
                print(f"error: cannot mirror {path}: {ex}", file=sys.stderr)
                return 2
            count += 1
    print(count)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
