"""Layer 1 parser golden tests for /lean4:autoformalize."""

from __future__ import annotations

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

SPEC = COMMAND_SPECS["autoformalize"]
CWD = "/tmp"


class TestAutoformalizeHappyPath(unittest.TestCase):
    """Happy-path tests."""

    def test_all_required_flags(self):
        result = parse_invocation(
            SPEC,
            "--source=paper.pdf --claim-select=first --out=Out.lean",
            cwd=CWD,
        )
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--source"].value, "paper.pdf")
        self.assertEqual(result.options["--source"].source, "explicit")
        self.assertEqual(result.options["--claim-select"].value, "first")
        self.assertEqual(result.options["--out"].value, "Out.lean")

    def test_all_required_with_extras(self):
        result = parse_invocation(
            SPEC,
            "--source=paper.pdf --claim-select=first --out=Out.lean --rigor=checked",
            cwd=CWD,
        )
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--rigor"].value, "checked")
        self.assertEqual(result.options["--rigor"].source, "explicit")


class TestAutoformalizeMissingRequired(unittest.TestCase):
    """Missing required flags produce errors."""

    def test_missing_source(self):
        result = parse_invocation(
            SPEC,
            "--claim-select=first --out=Out.lean",
            cwd=CWD,
        )
        self.assertTrue(len(result.errors) > 0)
        matching = [e for e in result.errors if "source" in e.lower()]
        self.assertTrue(
            len(matching) > 0, f"Expected source error, got: {result.errors}"
        )

    def test_missing_claim_select(self):
        result = parse_invocation(
            SPEC,
            "--source=paper.pdf --out=Out.lean",
            cwd=CWD,
        )
        self.assertTrue(len(result.errors) > 0)
        matching = [e for e in result.errors if "claim-select" in e.lower()]
        self.assertTrue(
            len(matching) > 0, f"Expected claim-select error, got: {result.errors}"
        )

    def test_missing_out(self):
        result = parse_invocation(
            SPEC,
            "--source=paper.pdf --claim-select=first",
            cwd=CWD,
        )
        self.assertTrue(len(result.errors) > 0)
        matching = [e for e in result.errors if "out" in e.lower()]
        self.assertTrue(len(matching) > 0, f"Expected out error, got: {result.errors}")

    def test_empty_input_all_missing(self):
        result = parse_invocation(SPEC, "", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        # Should have at least source, claim-select, and out errors
        self.assertTrue(
            len(result.errors) >= 3, f"Expected >=3 errors, got: {result.errors}"
        )


class TestAutoformalizeReviewSourceCoercion(unittest.TestCase):
    """--review-source=external -> coerced to internal."""

    def test_review_source_external_coerced(self):
        result = parse_invocation(
            SPEC,
            "--source=paper.pdf --claim-select=first --out=Out.lean --review-source=external",
            cwd=CWD,
        )
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--review-source"].value, "internal")
        self.assertEqual(result.options["--review-source"].source, "coerced")
        self.assertEqual(result.options["--review-source"].coerced_from, "external")

    def test_review_source_both_coerced(self):
        result = parse_invocation(
            SPEC,
            "--source=paper.pdf --claim-select=first --out=Out.lean --review-source=both",
            cwd=CWD,
        )
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--review-source"].value, "internal")
        self.assertEqual(result.options["--review-source"].source, "coerced")
        self.assertEqual(result.options["--review-source"].coerced_from, "both")

    def test_review_source_internal_not_coerced(self):
        result = parse_invocation(
            SPEC,
            "--source=paper.pdf --claim-select=first --out=Out.lean --review-source=internal",
            cwd=CWD,
        )
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--review-source"].value, "internal")
        self.assertEqual(result.options["--review-source"].source, "explicit")


class TestAutoformalizeNoPositionals(unittest.TestCase):
    """autoformalize has no positionals, so any positional is rejected."""

    def test_positional_rejected(self):
        result = parse_invocation(
            SPEC,
            "unexpected --source=paper.pdf --claim-select=first --out=Out.lean",
            cwd=CWD,
        )
        self.assertTrue(len(result.errors) > 0)
        matching = [e for e in result.errors if "positional" in e.lower()]
        self.assertTrue(
            len(matching) > 0, f"Expected positional error, got: {result.errors}"
        )


if __name__ == "__main__":
    unittest.main()
