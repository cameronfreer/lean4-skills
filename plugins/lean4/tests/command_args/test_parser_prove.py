"""Layer 1 parser golden tests for /lean4:prove."""

from __future__ import annotations

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

SPEC = COMMAND_SPECS["prove"]
CWD = "/tmp"


class TestProveHappyPath(unittest.TestCase):
    """Happy-path tests."""

    def test_scope_positional(self):
        result = parse_invocation(SPEC, "Foo.lean", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["scope"], "Foo.lean")

    def test_empty_scope_ok(self):
        result = parse_invocation(SPEC, "", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertNotIn("scope", result.positionals)

    def test_all_defaults_no_coercions(self):
        result = parse_invocation(SPEC, "Foo.lean", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.coercions, [])
        self.assertEqual(result.warnings, [])
        # Verify key defaults
        self.assertEqual(result.options["--planning"].value, "ask")
        self.assertEqual(result.options["--planning"].source, "default")
        self.assertEqual(result.options["--commit"].value, "ask")
        self.assertEqual(result.options["--commit"].source, "default")
        self.assertEqual(result.options["--deep"].value, "never")
        self.assertEqual(result.options["--deep"].source, "default")


class TestProvePlanningAskIsValid(unittest.TestCase):
    """--planning=ask is valid for prove (interactive, NOT coerced)."""

    def test_planning_ask_not_coerced(self):
        result = parse_invocation(SPEC, "Foo.lean --planning=ask", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--planning"].value, "ask")
        self.assertEqual(result.options["--planning"].source, "explicit")
        self.assertIsNone(result.options["--planning"].coerced_from)


class TestProveCommitAskIsValid(unittest.TestCase):
    """--commit=ask is valid for prove (interactive, NOT coerced)."""

    def test_commit_ask_not_coerced(self):
        result = parse_invocation(SPEC, "--commit=ask", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--commit"].value, "ask")
        self.assertEqual(result.options["--commit"].source, "explicit")
        self.assertIsNone(result.options["--commit"].coerced_from)


class TestProveBadEnum(unittest.TestCase):
    """Bad enum values produce errors."""

    def test_bad_deep_value(self):
        result = parse_invocation(SPEC, "--deep=banana", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("banana", result.errors[0])
        # Should list valid values
        self.assertIn("never", result.errors[0])
        self.assertIn("ask", result.errors[0])
        self.assertIn("stuck", result.errors[0])
        self.assertIn("always", result.errors[0])

    def test_bad_planning_value(self):
        result = parse_invocation(SPEC, "--planning=banana", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("banana", result.errors[0])


class TestProveNoCrossValidations(unittest.TestCase):
    """prove has no cross-validations, so no warning/error from them."""

    def test_no_cross_validation_errors(self):
        result = parse_invocation(SPEC, "Foo.lean", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.warnings, [])

    def test_no_cross_validation_with_explicit_flags(self):
        result = parse_invocation(
            SPEC,
            "Foo.lean --commit=auto --planning=on --deep=stuck",
            cwd=CWD,
        )
        self.assertEqual(result.errors, [])
        self.assertEqual(result.warnings, [])
        self.assertEqual(result.options["--commit"].value, "auto")
        self.assertEqual(result.options["--planning"].value, "on")
        self.assertEqual(result.options["--deep"].value, "stuck")


class TestProveBooleanFlags(unittest.TestCase):
    """Boolean flags support explicit =false negation."""

    def test_repair_only_false(self):
        """--repair-only=false must not produce a stray positional error."""
        result = parse_invocation(SPEC, "Foo.lean --repair-only=false", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertFalse(result.options["--repair-only"].value)

    def test_repair_only_true(self):
        result = parse_invocation(SPEC, "Foo.lean --repair-only=true", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertTrue(result.options["--repair-only"].value)

    def test_repair_only_presence(self):
        """Bare --repair-only (no value) means true."""
        result = parse_invocation(SPEC, "Foo.lean --repair-only", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertTrue(result.options["--repair-only"].value)

    def test_checkpoint_false(self):
        result = parse_invocation(SPEC, "--checkpoint=false", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertFalse(result.options["--checkpoint"].value)


if __name__ == "__main__":
    unittest.main()
