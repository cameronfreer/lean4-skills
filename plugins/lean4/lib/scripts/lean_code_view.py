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
the literal text is blanked but each ``{…}`` interpolation is code and is
kept (scanned by the same pass, so a nested string or a ``}`` inside a
comment or raw string there is handled in turn; ``\\{`` is a literal
brace). A string is interpolated exactly where core Lean's syntax says so:
after the keyword ``s!``, ``m!``, ``f!``, ``println!``, ``dbg_trace``,
``throwError``…, or after ``throwErrorAt ref``, ``trace[cls]``,
``throwNamedError name``… — the argument skipped as one token (a
qualified name whose components may be escaped, ``Syntax.«missing»``, or a
leading-dot name, ``.missing``) or bracket group, with its postfixes
(``stx[0]!``), whitespace and comments allowed in between. ``logInfo "…"``, ``panic! "…"``, ``Lean.throwError "…"`` and
user-defined interpolating macros take the string as ordinary text (for
the latter a ``{…}`` reference is not counted; advisory tool). No Lean
parsing is attempted; this is enough for reference counting, not for
semantics.

Exit status: 0 on success (prints the number of files mirrored); 1 on a
usage error; 2 if any file or directory could not be read, listed or
written — a caller must treat that as "cannot analyze", never as "no
findings".
"""

from __future__ import annotations

import os
import re
import sys

# Lean's identifier alphabet, transcribed from Lean 4.34 (src/lean/Init/Meta/
# Defs.lean: isLetterLike, isSubScriptAlnum, isIdFirst, isIdRest): ASCII
# letters, digits, `_`, `'`, `!`, `?`, letter-like Unicode and subscripts.
# Everything else — `⟨`, `(`, `,`, `←`, `∀`, the multiplication sign,
# spaces… — ends a token, so a literal right after it is recognised. Ident
# rest additionally continues over `.` (qualified names).
_LETTER_LIKE = (
    "\u03b1-\u03ba\u03bc-\u03c9"  # lower Greek but lambda
    "\u0391-\u039f\u03a1\u03a2\u03a4-\u03a9"  # upper Greek but Pi, Sigma
    "\u03ca-\u03fb"  # Coptic
    "\u1f00-\u1ffe"  # polytonic Greek
    "\u2100-\u214f"  # letter-like block
    "\U0001d49c-\U0001d59f"  # script, double-struck, fraktur
    "\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u00ff"  # Latin-1 letters but U+00D7, U+00F7
    "\u0100-\u017f"  # Latin Extended-A
)
_SUBSCRIPT = "\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
_ID_FIRST = re.compile(f"[A-Za-z_{_LETTER_LIKE}]")
_IDENT = re.compile(f"[A-Za-z0-9_'!?.{_LETTER_LIKE}{_SUBSCRIPT}]")
# The core Lean 4.34 syntaxes whose string argument is `interpolatedStr`
# (every use of it under src/lean), each mapped to the arguments that come
# before the string: `T` a term:max (the error reference), `I` an
# identifier (the error name). The keyword must be the whole token:
# `logInfo`, `panic!` and the plain function `Lean.throwError` take an
# ordinary string, whose `{…}` is literal text. Strings of user-defined
# interpolating macros are blanked whole too — a `{…}` reference there is
# not counted (advisory tool; see #185).
_INTERP_ARGS = {
    "s!": "",
    "f!": "",
    "m!": "",
    "println!": "",
    "dbg_trace": "",
    "throwError": "",
    "throwErrorAt": "T",
    "throwNamedError": "I",
    "throwNamedErrorAt": "TI",
    "logNamedError": "I",
    "logNamedErrorAt": "TI",
    "logNamedWarning": "I",
    "logNamedWarningAt": "TI",
    "reportIssue!": "",
    "reportDbgIssue!": "",
    "reportEMatchIssue!": "",
}
# `trace[cls] "…"`: the keyword is `trace[` (no space), the bracket group
# the one argument before the string.
_INTERP_BRACKET = frozenset({"trace", "trace_goal", "Macro.trace"})
_CLOSER = {"(": ")", "[": "]", "⟨": "⟩", "{": "}"}
_OPENER = {c: o for o, c in _CLOSER.items()}
_CHAR_LIT = re.compile(r"'(?:\\x[0-9A-Fa-f]{2}|\\u\{[0-9A-Fa-f]+\}|\\.|[^'\\\n])'")
_RAW_OPEN = re.compile(r'r(#*)"')


def _blank(text: str) -> str:
    """Spaces for every character except newlines, which are kept."""
    return "".join("\n" if c == "\n" else " " for c in text)


def _component_start(c: str) -> bool:
    """Can ``c`` begin a name component after a `.`?"""
    return c == "«" or (c != "." and bool(_IDENT.match(c)))


def _ident_end(text: str, i: int) -> int:
    """End of the name starting at text[i]: components of identifier
    characters or escaped ``«…»`` (opaque up to ``»`` — it may hold
    comment markers, quotes, braces, newlines), joined by `.`. A leading
    `.` (``.missing``) is part of the name."""
    n = len(text)
    j = i
    while j < n:
        if text[j] == "«":
            k = text.find("»", j + 1)
            j = n if k < 0 else k + 1
        else:
            while j < n and text[j] != "." and _IDENT.match(text[j]):
                j += 1
        if j + 1 < n and text[j] == "." and _component_start(text[j + 1]):
            j += 1
            continue
        return j
    return j


def code_view(text: str) -> str:
    """Blank comments and string/char literals; newline positions unchanged."""
    out: list[str] = []
    _scan(text, 0, out, until="")
    return "".join(out)


def _scan(text: str, i: int, out: list[str], *, until: str) -> int:
    """The one lexical pass. Appends the view of text[i:] to ``out``.

    With ``until`` (a closing bracket) the scan is the inside of a bracket
    group — an interpolation's ``{…}`` code, or a bracketed argument before
    an interpolated string: it stops at the first ``until`` not balanced by
    its opener at code level and returns its index (the caller emits it).
    Comments, string/char literals, raw strings and nested interpolations
    are consumed by the same rules either way, so a closer inside any of
    them never ends a group. Returns len(text) when it runs to the end.
    """
    n = len(text)
    depth = 0  # block-comment nesting
    balance = 0  # code-level nesting of the `until` bracket
    # Arguments still expected before an interpolated string (see
    # _INTERP_ARGS); "" = the string itself comes next; None = no
    # interpolating keyword is pending. Whitespace and comments keep it.
    need: str | None = None
    post = False  # a postfix (`[…]`, `.x`, `!`) may extend the last argument
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
        was_post, post = post, False
        at_token_start = i == 0 or not _IDENT.match(text[i - 1])
        if ch == "r" and at_token_start:
            m = _RAW_OPEN.match(text, i)
            if m:
                close = '"' + "#" * len(m.group(1))
                end = text.find(close, m.end())
                end = n if end < 0 else end + len(close)
                out.append(_blank(text[i:end]))
                i = end
                need = None
                continue
        if ch == "'" and at_token_start:
            m = _CHAR_LIT.match(text, i)
            if m:
                out.append(" " * (m.end() - i))
                i = m.end()
                need = None
                continue
        if ch == '"' and need == "":
            # interpolated string: literal text blanked, each `{…}` is code
            # (scanned by this function)
            i = _interp_string(text, i, out)
            need = None
            continue
        if ch == '"':
            need = None
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
        if (
            ch == "«"
            or (at_token_start and _ID_FIRST.match(ch))
            or (need and not was_post and ch == "." and _component_start(nxt))
        ):
            # identifier token, kept verbatim — `Syntax.«missing»`, and in
            # argument position `.missing`, are one token: an expected
            # argument, or a keyword whose string argument interpolates,
            # or neither
            j = _ident_end(text, i)
            word = text[i:j]
            if need:
                need, post = need[1:], True
            elif word in _INTERP_BRACKET and text.startswith("[", j):
                need = "T"
            else:
                need = _INTERP_ARGS.get(word)
            out.append(word)
            i = j
            continue
        if was_post and (ch in "!?" or (ch == "." and _component_start(nxt))):
            # postfix of the argument just read: `x[0]!`, `(f x).raw`
            j = i + 1 if ch in "!?" else _ident_end(text, i)
            out.append(text[i:j])
            i = j
            post = True
            continue
        if ch in _CLOSER and (need or (was_post and ch == "[")):
            # bracketed argument `(…)`/`⟨…⟩`/`[…]`, or postfix index `x[…]`
            if need and not (was_post and ch == "["):
                need = need[1:]
            out.append(ch)
            k = _scan(text, i + 1, out, until=_CLOSER[ch])
            if k < n:
                out.append(text[k])
                k += 1
            i = k
            post = True
            continue
        if until:
            if ch == _OPENER[until]:
                balance += 1
            elif ch == until:
                if balance == 0:
                    return i
                balance -= 1
        if not ch.isspace():
            need = None
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
            k = _scan(text, j + 1, out, until="}")
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
