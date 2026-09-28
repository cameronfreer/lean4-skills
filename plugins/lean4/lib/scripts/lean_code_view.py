#!/usr/bin/env python3
"""lean_code_view.py — code-only mirror of a Lean source tree (issue #185).

Usage: lean_code_view.py SRC_DIR MIRROR_DIR [--files LIST]

Copies Lean files under SRC_DIR to the same relative path under MIRROR_DIR
with comments and string/character literals blanked out: every stripped
character becomes a space and every newline is kept, so line numbers,
columns and token boundaries are preserved and any grep-based tool can run
over the mirror and report locations that are valid in the original tree.

Which files: with ``--files LIST`` (``-`` = stdin), exactly the NUL-separated
paths listed — the caller establishes the eligible set with its own backend
(``rg --files`` honours ignore metadata, ``find`` does not) so relocating the
search never broadens it. Without ``--files`` every ``*.lean`` under SRC_DIR
is mirrored, and a directory that cannot be traversed is an error.

The scanner is a character-level port of ``sorry_analyzer.strip_lean_
comments_and_strings`` (line comments ``--``, nested block comments
``/- … -/`` including docstrings, string literals with backslash escapes),
hardened for this use: the string state is threaded across lines, an
escaped newline inside a string stays a newline, character literals
(``'"'``, ``'\\''``, ``'\\x41'``, ``'\\u{3b1}'``) and raw strings (``r"…"``,
``r#"…"#``) are blanked whole. No Lean parsing is attempted; this is
enough for reference counting, not for semantics.

Exit status: 0 on success (prints the number of files mirrored); 1 on a
usage error; 2 if any file or directory could not be read, listed or
written — a caller must treat that as "cannot analyze", never as "no
findings".
"""

from __future__ import annotations

import os
import re
import sys

_IDENT = re.compile(r"[A-Za-z0-9_'.À-\U0010ffff]")
_CHAR_LIT = re.compile(r"'(?:\\x[0-9A-Fa-f]{2}|\\u\{[0-9A-Fa-f]+\}|\\.|[^'\\\n])'")
_RAW_OPEN = re.compile(r'r(#*)"')


def _blank(text: str) -> str:
    """Spaces for every character except newlines, which are kept."""
    return "".join("\n" if c == "\n" else " " for c in text)


def code_view(text: str) -> str:
    """Blank comments and string/char literals; newline positions unchanged."""
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0  # block-comment nesting
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
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
        at_token_start = i == 0 or not _IDENT.match(text[i - 1])
        if ch == "r" and at_token_start:
            m = _RAW_OPEN.match(text, i)
            if m:
                close = '"' + "#" * len(m.group(1))
                end = text.find(close, m.end())
                end = n if end < 0 else end + len(close)
                out.append(_blank(text[i:end]))
                i = end
                continue
        if ch == "'" and at_token_start:
            m = _CHAR_LIT.match(text, i)
            if m:
                out.append(" " * (m.end() - i))
                i = m.end()
                continue
        if ch == '"':
            # string literal: runs to the next unescaped quote, across lines;
            # an escaped newline keeps its newline
            j = i + 1
            while j < n:
                c = text[j]
                if c == "\\" and j + 1 < n:
                    j += 2
                    continue
                if c == '"':
                    j += 1
                    break
                j += 1
            out.append(_blank(text[i:j]))
            i = j
            continue
        if ch == "-" and nxt == "-":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        if ch == "/" and nxt == "-":
            depth += 1
            out.append("  ")
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _walk_all(src: str) -> list[str]:
    errors: list[OSError] = []
    files: list[str] = []
    for root, _dirs, names in os.walk(src, onerror=errors.append):
        for name in names:
            if name.endswith(".lean"):
                files.append(os.path.join(root, name))
    if errors:
        raise errors[0]
    return files


def main(argv: list[str]) -> int:
    args = [a for a in argv[1:] if a != "--files"]
    list_src = None
    if "--files" in argv:
        k = argv.index("--files")
        if k + 1 >= len(argv):
            print(
                "usage: lean_code_view.py SRC_DIR MIRROR_DIR [--files LIST]",
                file=sys.stderr,
            )
            return 1
        list_src = argv[k + 1]
        args = [a for a in argv[1:] if a not in ("--files", list_src)]
    if len(args) != 2:
        print(
            "usage: lean_code_view.py SRC_DIR MIRROR_DIR [--files LIST]",
            file=sys.stderr,
        )
        return 1
    src, mirror = args
    if not os.path.isdir(src):
        print(f"error: {src!r} is not a directory", file=sys.stderr)
        return 1
    try:
        if list_src is None:
            files = _walk_all(src)
        else:
            if list_src == "-":
                raw = sys.stdin.buffer.read()
            else:
                with open(list_src, "rb") as lf:
                    raw = lf.read()
            files = [
                os.fsdecode(p)
                if os.path.isabs(os.fsdecode(p))
                else os.path.join(src, os.fsdecode(p))
                for p in raw.split(b"\0")
                if p
            ]
    except OSError as ex:
        print(f"error: cannot list {src}: {ex}", file=sys.stderr)
        return 2
    count = 0
    for path in files:
        rel = os.path.relpath(path, src)
        if rel.startswith(".."):
            print(f"error: {path} is outside {src}", file=sys.stderr)
            return 2
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
