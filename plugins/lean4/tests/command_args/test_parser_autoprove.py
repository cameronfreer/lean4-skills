"""Layer 1 parser golden tests for /lean4:autoprove."""

from __future__ import annotations

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

SPEC = COMMAND_SPECS["autoprove"]
CWD = "/tmp"


class TestAutoproveHappyPath(unittest.TestCase):
    """Happy-path tests."""

    def test_scope_and_max_cycles(self):
        result = parse_invocation(SPEC, "Foo.lean --max-cycles=10", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["scope"], "Foo.lean")
        self.assertEqual(result.options["--max-cycles"].value, 10)
        self.assertEqual(result.options["--max-cycles"].source, "explicit")

    def test_defaults_applied(self):
        result = parse_invocation(SPEC, "Foo.lean", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--deep"].value, "stuck")
        self.assertEqual(result.options["--deep"].source, "default")
        self.assertEqual(result.options["--commit"].value, "auto")
        self.assertEqual(result.options["--commit"].source, "default")

    def test_no_positional_ok(self):
        """Scope is optional for autoprove."""
        result = parse_invocation(SPEC, "", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertNotIn("scope", result.positionals)


class TestAutoproveCommitCoercion(unittest.TestCase):
    """--commit=ask -> coerced to auto."""

    def test_commit_ask_coerced_to_auto(self):
        result = parse_invocation(SPEC, "--commit=ask", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--commit"].value, "auto")
        self.assertEqual(result.options["--commit"].source, "coerced")
        self.assertEqual(result.options["--commit"].coerced_from, "ask")
        self.assertTrue(len(result.coercions) > 0, "Expected a coercion note")


class TestAutoproveReviewSourceCoercion(unittest.TestCase):
    """--review-source=external|both -> coerced to internal."""

    def test_review_source_external_coerced(self):
        result = parse_invocation(SPEC, "--review-source=external", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--review-source"].value, "internal")
        self.assertEqual(result.options["--review-source"].source, "coerced")
        self.assertEqual(result.options["--review-source"].coerced_from, "external")

    def test_review_source_both_coerced(self):
        result = parse_invocation(SPEC, "--review-source=both", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--review-source"].value, "internal")
        self.assertEqual(result.options["--review-source"].source, "coerced")
        self.assertEqual(result.options["--review-source"].coerced_from, "both")

    def test_review_source_internal_not_coerced(self):
        result = parse_invocation(SPEC, "--review-source=internal", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--review-source"].value, "internal")
        self.assertEqual(result.options["--review-source"].source, "explicit")


class TestAutoproveDeepCoercion(unittest.TestCase):
    """--deep=ask -> coerced to stuck."""

    def test_deep_ask_coerced_to_stuck(self):
        result = parse_invocation(SPEC, "--deep=ask", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--deep"].value, "stuck")
        self.assertEqual(result.options["--deep"].source, "coerced")
        self.assertEqual(result.options["--deep"].coerced_from, "ask")


class TestAutoproveDeepRollbackCoercion(unittest.TestCase):
    """--deep-rollback=never -> coerced to on-regression."""

    def test_deep_rollback_never_coerced(self):
        result = parse_invocation(SPEC, "--deep-rollback=never", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--deep-rollback"].value, "on-regression")
        self.assertEqual(result.options["--deep-rollback"].source, "coerced")
        self.assertEqual(result.options["--deep-rollback"].coerced_from, "never")


class TestAutoproveDeepRegressionGateCoercion(unittest.TestCase):
    """--deep-regression-gate=off -> coerced to strict."""

    def test_deep_regression_gate_off_coerced(self):
        result = parse_invocation(SPEC, "--deep-regression-gate=off", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--deep-regression-gate"].value, "strict")
        self.assertEqual(result.options["--deep-regression-gate"].source, "coerced")
        self.assertEqual(result.options["--deep-regression-gate"].coerced_from, "off")


class TestAutoproveTypeErrors(unittest.TestCase):
    """Type validation errors."""

    def test_bad_int_max_cycles(self):
        result = parse_invocation(SPEC, "--max-cycles=cat", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("cat", result.errors[0])

    def test_bad_duration(self):
        result = parse_invocation(SPEC, "--max-total-runtime=10banana", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("10banana", result.errors[0])

    def test_valid_duration_minutes(self):
        result = parse_invocation(SPEC, "--max-total-runtime=15m", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--max-total-runtime"].value, "15m")

    def test_valid_duration_seconds(self):
        result = parse_invocation(SPEC, "--max-total-runtime=30s", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--max-total-runtime"].value, "30s")

    def test_valid_duration_90s(self):
        """Sub-minute budgets survive with explicit suffix — tracker reads '90s' as 90 seconds."""
        result = parse_invocation(SPEC, "--max-total-runtime=90s", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--max-total-runtime"].value, "90s")

    def test_valid_duration_hours(self):
        result = parse_invocation(SPEC, "--max-total-runtime=2h", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--max-total-runtime"].value, "2h")

    def test_bare_numeric_normalized_to_minutes(self):
        """Bare number (no suffix) is interpreted as minutes, normalized to '<N>m'."""
        result = parse_invocation(SPEC, "--max-total-runtime=120", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--max-total-runtime"].value, "120m")

    def test_fractional_hours_rejected(self):
        """1.5h is rejected — tracker only accepts integer prefixes."""
        result = parse_invocation(SPEC, "--max-total-runtime=1.5h", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("fractional", result.errors[0].lower())

    def test_fractional_minutes_rejected(self):
        result = parse_invocation(SPEC, "--max-total-runtime=0.5m", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("fractional", result.errors[0].lower())

    def test_dot_prefix_rejected(self):
        result = parse_invocation(SPEC, "--max-total-runtime=.5h", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)


class TestAutoproveUnknownFlag(unittest.TestCase):
    """Unknown flags produce errors."""

    def test_unknown_flag(self):
        result = parse_invocation(SPEC, "--nonexistent=foo", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("Unknown flag", result.errors[0])
        self.assertIn("--nonexistent", result.errors[0])


if __name__ == "__main__":
    unittest.main()
