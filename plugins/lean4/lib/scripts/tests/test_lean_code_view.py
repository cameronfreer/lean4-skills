#!/usr/bin/env python3
"""
Unit tests for lean_code_view.py — the code-only view behind
unused_declarations.sh (#185). End-to-end behaviour is covered by the
fixtures in tests/test_unused_declarations.sh; these pin the scanner
decisions that are awkward to express as fixtures: which strings are
interpolated, and where Lean's identifier alphabet ends a token.

Every interpolation case below that is valid Lean was checked against
Lean 4.34.0-rc1 by writing an undeclared name inside the braces: the
interpolated forms fail with "Unknown identifier", the ordinary ones
compile.

Run:
    python3 tests/test_lean_code_view.py
    # or from repo root:
    python3 plugins/lean4/lib/scripts/tests/test_lean_code_view.py
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lean_code_view import _INTERP_ARGS, code_view

_FIXTURES = Path(__file__).resolve().parents[3] / "tests" / "fixtures" / "unused_decls"

# The string after these is interpolatedStr: `{x}` is code and is kept.
INTERPOLATED = [
    's!"v {x}"',
    's! "v {x}"',
    's! /- c -/ "v {x}"',
    'f!"v {x}"',
    'throwError m!"v {x}"',
    'println! "v {x}"',
    'dbg_trace "v {x}"; ()',
    'throwError "v {x}"',
    'throwErrorAt Syntax.missing "v {x}"',
    'throwErrorAt .missing "v {x}"',
    'throwErrorAt Syntax.\u00abmissing\u00bb "v {x}"',
    'throwErrorAt \u00abstx\u00bb.getArgs[0]! "v {x}"',
    'throwErrorAt (stx).\u00abraw\u00bb "v {x}"',
    'throwErrorAt (stx.getArg 0) "v {x}"',
    'throwErrorAt ⟨stx⟩ "v {x}"',
    'throwErrorAt stx.getArgs[0]! /- ref -/ "v {x}"',
    'throwErrorAt (f "not {code}") "v {x}"',
    'trace[Meta.debug] "v {x}"',
    'throwNamedError lean.foo "v {x}"',
    'throwNamedErrorAt ref lean.foo "v {x}"',
    'logNamedWarning lean.foo "v {x}"',
]

# Ordinary strings: `{x}` is literal text and is blanked.
LITERAL = [
    'logInfo "v {x}"',
    'Lean.logInfo "v {x}"',
    'logWarning "v {x}"',
    'panic! "v {x}"',
    'Lean.throwError "v {x}"',
    'foo "v {x}"',
    'xs! "v {x}"',
    'throwErrorAt stx foo "v {x}"',
    # not valid Lean (the keyword is `trace[`, `s!` wants a plain string);
    # the scanner must still not treat these as interpolation
    'trace [cls] "v {x}"',
    's! r"v {x}"',
]


class InterpolationTest(unittest.TestCase):
    def test_interpolated(self) -> None:
        for src in INTERPOLATED:
            with self.subTest(src=src):
                view = code_view(src)
                self.assertEqual(len(view), len(src))
                self.assertIn("{x}", view)  # the interpolation is code
                self.assertNotIn("v {", view)  # the literal text is not
                self.assertNotIn("code", view)  # nor a string inside an argument

    def test_literal(self) -> None:
        for src in LITERAL:
            with self.subTest(src=src):
                view = code_view(src)
                self.assertEqual(len(view), len(src))
                self.assertNotIn("{", view)
                self.assertNotIn("}", view)


class NameLiteralTest(unittest.TestCase):
    # `` `throwError `` is a Name value (one token in Lean's lexer), not the
    # keyword: the string after it is ordinary, whatever it holds. (Lean
    # rejects ``kw for keyword tokens; the scanner must still not treat the
    # quoted form as the keyword.)
    def test_open_brace_does_not_swallow_the_tail(self) -> None:
        src = '#check Lean.Name.str `throwError "{"\n#check live\ndef after : Nat := 2\n#check after\n'
        view = code_view(src)
        self.assertEqual(len(view), len(src))
        for line in ("#check live", "def after : Nat := 2", "#check after"):
            self.assertIn(line, view.splitlines())

    def test_quoted_keywords_are_not_keywords(self) -> None:
        for kw in (*_INTERP_ARGS, "trace", "Lean.\u00abthrowError\u00bb"):
            for quote in ("`", "``"):
                src = f'#check Lean.Name.str {quote}{kw} "literal {{x}}"'
                with self.subTest(src=src):
                    view = code_view(src)
                    self.assertIn(f"{quote}{kw}", view)
                    self.assertNotIn("{", view)

    def test_syntax_quotation_is_code(self) -> None:
        src = '`(throwError "v {x}")'
        self.assertEqual(code_view(src), "`(throwError    {x} )")


class TokenBoundaryTest(unittest.TestCase):
    def test_lean_identifier_alphabet(self) -> None:
        # Latin-1 / Latin Extended-A letters and the U+2C7C subscript
        # continue an identifier, so `'b'` after them is part of the name,
        # not a char literal ...
        for stem in ("caf\u00e9", "\u0142", "x\u2c7c", "\u03b1", "x\u2081"):
            with self.subTest(stem=stem):
                src = f"def {stem}'b' := 1"
                self.assertEqual(code_view(src), src)
        # ... while delimiters and operators end one, so a char literal or
        # raw string right after them is recognised
        self.assertEqual(code_view("⟨'\"', live⟩"), "⟨   , live⟩")
        self.assertEqual(code_view('(r#"a "b" c"#, live)'), "(" + " " * 12 + ", live)")
        self.assertEqual(code_view("a\u00d7'\"' live"), "a\u00d7    live")

    def test_escaped_identifier_is_opaque(self) -> None:
        self.assertEqual(code_view("«x--» live"), "«x--» live")
        self.assertEqual(code_view('«y"z» live'), '«y"z» live')


class InvariantTest(unittest.TestCase):
    def test_fixture_newlines_and_length_preserved(self) -> None:
        files = sorted(_FIXTURES.rglob("*.lean"))
        self.assertTrue(files)
        for path in files:
            with self.subTest(path=path.name, fixture=path.parent.name):
                src = path.read_text(encoding="utf-8")
                view = code_view(src)
                self.assertEqual(len(view), len(src))
                self.assertEqual(
                    [i for i, c in enumerate(src) if c == "\n"],
                    [i for i, c in enumerate(view) if c == "\n"],
                )


if __name__ == "__main__":
    unittest.main()
