#!/usr/bin/env python3
"""lean_code_view.py — code-only mirror of a Lean source tree (issue #185).

Usage: lean_code_view.py SRC_DIR MIRROR_DIR [--files LIST]

Copies Lean files under SRC_DIR to the same relative path under MIRROR_DIR
with comments and string/character literals blanked out: every stripped
character becomes a space and every newline is kept, so line numbers,
columns and token boundaries are preserved and any grep-based tool can run
over the mirror and report locations that are valid in the original tree.

Which files: with ``--files LIST`` (``-`` = stdin), exactly the NUL-separated
paths listed, taken as the backend printed them — absolute, or relative to
the current working directory (``rg --files src`` prints ``src/A.lean``) —
so the caller establishes the eligible set with its own backend (``rg
--files`` honours ignore metadata, ``find`` does not) and relocating the
search never broadens it. Every listed path must lie under SRC_DIR. Without
``--files`` every ``*.lean`` under SRC_DIR is mirrored, and a directory that
cannot be traversed is an error.

The scanner is a character-level port of ``sorry_analyzer.strip_lean_
comments_and_strings`` (line comments ``--``, nested block comments
``/- … -/`` including docstrings, string literals with backslash escapes),
hardened for this use: the string state is threaded across lines, an
escaped newline inside a string stays a newline, character literals
(``'"'``, ``'\\''``, ``'\\x41'``, ``'\\u{3b1}'``) and raw strings (``r"…"``,
``r#"…"#``) are blanked whole — a literal is recognised at any token
boundary, Lean's identifier alphabet deciding what is a boundary (so
``⟨'"', x⟩`` is a char literal, ``x'`` a primed name) — an escaped
identifier ``«…»`` is opaque up to its ``»``, and in an interpolated string
(the string after ``s!``/``m!``/any ``ident!`` or after core ``throwError``/
``logInfo``-family names, whitespace and comments in between allowed) the
literal text is blanked but each ``{…}`` interpolation is code and is kept
(scanned by the same pass, so a nested string or a ``}`` inside a comment
or raw string there is handled in turn; ``\\{`` is a literal brace).
Strings of other, user-defined interpolating macros are blanked whole —
a ``{…}`` reference there is not counted (advisory tool). No Lean parsing
is attempted; this is enough for reference counting, not for semantics.

Exit status: 0 on success (prints the number of files mirrored); 1 on a
usage error; 2 if any file or directory could not be read, listed or
written — a caller must treat that as "cannot analyze", never as "no
findings".
"""

from __future__ import annotations

import os
import re
import sys

# Lean's identifier alphabet (Lean.isIdFirst / isIdRest, src/Init/Meta.lean):
# ASCII letters, digits, `_`, `'`, `!`, `?`, letter-like Unicode (Greek but
# λ Π Σ, Coptic, polytonic Greek, the letter-like block, mathematical
# script/double-struck/fraktur) and subscripts. Everything else — `⟨`, `(`,
# `,`, `←`, `∀`, spaces… — ends a token, so a literal right after it is
# recognised. Ident rest additionally continues over `.` (qualified names).
_LETTER_LIKE = (
    "\u03b1-\u03ba\u03bc-\u03c9"  # lower Greek but λ
    "\u0391-\u039f\u03a1\u03a2\u03a4-\u03a9"  # upper Greek but Π Σ
    "\u03ca-\u03fb"  # Coptic
    "\u1f00-\u1ffe"  # polytonic Greek
    "\u2100-\u214f"  # letter-like block
    "\U0001d49c-\U0001d59f"  # script, double-struck, fraktur
)
_SUBSCRIPT = "\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a"
_ID_FIRST = re.compile(f"[A-Za-z_{_LETTER_LIKE}]")
_IDENT = re.compile(f"[A-Za-z0-9_'!?.{_LETTER_LIKE}{_SUBSCRIPT}]")
# Identifiers whose next string literal Lean parses as an interpolated
# string: any `ident!` (s!, m!, f!, throwError!-style macros) and the core
# `throwError`/`logInfo` family (`interpolatedStr(term) <|> term`). Other
# user macros that interpolate are not recognised — a `{…}` reference in
# such a string is blanked like literal text (advisory tool; see #185).
_INTERP_WORDS = frozenset(
    {
        "throwError",
        "throwErrorAt",
        "logInfo",
        "logInfoAt",
        "logWarning",
        "logWarningAt",
        "logError",
        "logErrorAt",
        "trace",
    }
)
_CHAR_LIT = re.compile(r"'(?:\\x[0-9A-Fa-f]{2}|\\u\{[0-9A-Fa-f]+\}|\\.|[^'\\\n])'")
_RAW_OPEN = re.compile(r'r(#*)"')


def _blank(text: str) -> str:
    """Spaces for every character except newlines, which are kept."""
    return "".join("\n" if c == "\n" else " " for c in text)


def code_view(text: str) -> str:
    """Blank comments and string/char literals; newline positions unchanged."""
    out: list[str] = []
    _scan(text, 0, out, until_brace=False)
    return "".join(out)


def _scan(text: str, i: int, out: list[str], *, until_brace: bool) -> int:
    """The one lexical pass. Appends the view of text[i:] to ``out``.

    With ``until_brace`` the scan is the code of an interpolation: it stops
    at the first `}` not balanced by a `{` at code level and returns its
    index (the caller emits the brace). Comments, string/char literals,
    raw strings and nested interpolations are consumed by the same rules
    either way, so a `}` inside any of them never ends an interpolation.
    Returns len(text) when it runs to the end.
    """
    n = len(text)
    depth = 0  # block-comment nesting
    braces = 0  # code-level `{` … `}` nesting, only used with until_brace
    interp_pending = False  # the next string literal is interpolated
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
        if ch == "«":
            # escaped identifier component: opaque up to `»` — may hold
            # comment markers, quotes, braces, newlines; kept verbatim
            j = text.find("»", i + 1)
            j = n if j < 0 else j + 1
            out.append(text[i:j])
            i = j
            interp_pending = False
            continue
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
        if ch == '"' and interp_pending:
            # interpolated string (`s! "…"`, `throwError "…"`): literal
            # text blanked, each `{…}` is code (scanned by this function)
            i = _interp_string(text, i, out)
            interp_pending = False
            continue
        if ch == '"':
            interp_pending = False
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
        if at_token_start and _ID_FIRST.match(ch):
            # identifier token, kept verbatim; decides whether the string
            # literal that follows (after whitespace/comments) interpolates
            j = i + 1
            while j < n and _IDENT.match(text[j]):
                j += 1
            word = text[i:j]
            last = word.rsplit(".", 1)[-1]
            interp_pending = last.endswith("!") or last in _INTERP_WORDS
            out.append(word)
            i = j
            continue
        if until_brace:
            if ch == "{":
                braces += 1
            elif ch == "}":
                if braces == 0:
                    return i
                braces -= 1
        if not ch.isspace():
            interp_pending = False
        out.append(ch)
        i += 1
    return n


def _interp_string(text: str, i: int, out: list[str]) -> int:
    """Scan the interpolated string opening at text[i] == '"'; append its
    view to ``out`` and return the index just past its closing quote."""
    n = len(text)
    out.append(" ")
    j = i + 1
    while j < n:
        c = text[j]
        if c == "\\" and j + 1 < n:
            out.append(_blank(text[j : j + 2]))
            j += 2
            continue
        if c == '"':
            out.append(" ")
            return j + 1
        if c == "{":
            out.append("{")
            k = _scan(text, j + 1, out, until_brace=True)
            if k < n:
                out.append("}")
                k += 1
            j = k
            continue
        out.append("\n" if c == "\n" else " ")
        j += 1
    return n


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
            files = [os.fsdecode(p) for p in raw.split(b"\0") if p]
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
