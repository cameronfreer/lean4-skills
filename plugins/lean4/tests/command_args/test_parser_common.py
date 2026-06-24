"""Layer 1 parser golden tests for cross-command / structural behaviour."""

from __future__ import annotations

import json
import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

CWD = "/tmp"


class TestMultiPositionalRejection(unittest.TestCase):
    """Commands that allow at most 1 positional reject extras."""

    def test_draft_rejects_two_positionals(self):
        spec = COMMAND_SPECS["draft"]
        result = parse_invocation(spec, '"first" "second"', cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        matching = [e for e in result.errors if "positional" in e.lower()]
        self.assertTrue(
            len(matching) > 0, f"Expected positional error, got: {result.errors}"
        )

    def test_prove_rejects_two_positionals(self):
        spec = COMMAND_SPECS["prove"]
        result = parse_invocation(spec, "Foo.lean Bar.lean", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        matching = [e for e in result.errors if "positional" in e.lower()]
        self.assertTrue(
            len(matching) > 0, f"Expected positional error, got: {result.errors}"
        )


class TestWhitespaceHandling(unittest.TestCase):
    """Leading/trailing whitespace and internal whitespace."""

    def test_leading_trailing_whitespace(self):
        spec = COMMAND_SPECS["prove"]
        result = parse_invocation(spec, "   Foo.lean   ", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["scope"], "Foo.lean")

    def test_multiple_internal_spaces(self):
        spec = COMMAND_SPECS["prove"]
        result = parse_invocation(spec, "Foo.lean    --planning=on", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["scope"], "Foo.lean")
        self.assertEqual(result.options["--planning"].value, "on")


class TestFlagEqualsVsSpace(unittest.TestCase):
    """--flag=value and --flag value produce identical results."""

    def test_equals_form(self):
        spec = COMMAND_SPECS["autoprove"]
        r1 = parse_invocation(spec, "--max-cycles=5", cwd=CWD)
        self.assertEqual(r1.errors, [])
        self.assertEqual(r1.options["--max-cycles"].value, 5)

    def test_space_form(self):
        spec = COMMAND_SPECS["autoprove"]
        r2 = parse_invocation(spec, "--max-cycles 5", cwd=CWD)
        self.assertEqual(r2.errors, [])
        self.assertEqual(r2.options["--max-cycles"].value, 5)

    def test_equals_and_space_identical(self):
        spec = COMMAND_SPECS["autoprove"]
        r1 = parse_invocation(spec, "--max-cycles=5", cwd=CWD)
        r2 = parse_invocation(spec, "--max-cycles 5", cwd=CWD)
        self.assertEqual(
            r1.options["--max-cycles"].value, r2.options["--max-cycles"].value
        )
        self.assertEqual(
            r1.options["--max-cycles"].source, r2.options["--max-cycles"].source
        )


class TestToDict(unittest.TestCase):
    """ParseResult.to_dict() produces JSON-serializable output."""

    def test_to_dict_json_serializable(self):
        spec = COMMAND_SPECS["draft"]
        result = parse_invocation(spec, '"hello"', cwd=CWD)
        self.assertEqual(result.errors, [])
        d = result.to_dict()
        # Must not raise
        serialized = json.dumps(d)
        self.assertIsInstance(serialized, str)
        # Round-trip check
        loaded = json.loads(serialized)
        self.assertEqual(loaded["command"], "draft")
        self.assertEqual(loaded["positionals"]["topic"], "hello")

    def test_to_dict_with_coercion(self):
        spec = COMMAND_SPECS["draft"]
        result = parse_invocation(spec, '"hello" --intent=auto', cwd=CWD)
        self.assertEqual(result.errors, [])
        d = result.to_dict()
        serialized = json.dumps(d)
        loaded = json.loads(serialized)
        self.assertEqual(loaded["options"]["--intent"]["value"], "usage")
        self.assertEqual(loaded["options"]["--intent"]["source"], "coerced")
        self.assertEqual(loaded["options"]["--intent"]["coerced_from"], "auto")


class TestEmptyRawTail(unittest.TestCase):
    """Empty raw_tail for commands with no required positionals."""

    def test_prove_empty_ok(self):
        spec = COMMAND_SPECS["prove"]
        result = parse_invocation(spec, "", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertNotIn("scope", result.positionals)

    def test_autoprove_empty_ok(self):
        spec = COMMAND_SPECS["autoprove"]
        result = parse_invocation(spec, "", cwd=CWD)
        self.assertEqual(result.errors, [])


class TestUnknownCommandSpec(unittest.TestCase):
    """Unknown command name raises KeyError on COMMAND_SPECS lookup."""

    def test_unknown_command_keyerror(self):
        with self.assertRaises(KeyError):
            _ = COMMAND_SPECS["nonexistent"]


if __name__ == "__main__":
    unittest.main()
