"""Layer 1 parser golden tests for /lean4:draft."""

from __future__ import annotations

import os
import sys
import unittest

# Ensure the library package is importable.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

SPEC = COMMAND_SPECS["draft"]
CWD = "/tmp"


class TestDraftHappyPath(unittest.TestCase):
    """Happy-path tests for the draft command parser."""

    def test_topic_only_all_defaults(self):
        result = parse_invocation(SPEC, '"Theorem 1"', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["topic"], "Theorem 1")
        self.assertEqual(result.options["--mode"].value, "skeleton")
        self.assertEqual(result.options["--mode"].source, "default")

    def test_topic_with_explicit_mode(self):
        result = parse_invocation(SPEC, '"x" --mode=attempt', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--mode"].value, "attempt")
        self.assertEqual(result.options["--mode"].source, "explicit")

    def test_topic_with_spaces(self):
        result = parse_invocation(
            SPEC, '"every even number > 2 is the sum of two primes"', cwd=CWD
        )
        self.assertEqual(result.errors, [])
        self.assertEqual(
            result.positionals["topic"],
            "every even number > 2 is the sum of two primes",
        )

    def test_source_only_no_topic(self):
        result = parse_invocation(SPEC, "--source=paper.pdf", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertNotIn("topic", result.positionals)
        self.assertEqual(result.options["--source"].value, "paper.pdf")

    def test_topic_and_source_both_present(self):
        result = parse_invocation(SPEC, '"Zorn" --source=notes.pdf', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["topic"], "Zorn")
        self.assertEqual(result.options["--source"].value, "notes.pdf")


class TestDraftBadEnum(unittest.TestCase):
    """Enum validation errors."""

    def test_bad_mode_value(self):
        result = parse_invocation(SPEC, '"x" --mode=banana', cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("banana", result.errors[0])
        self.assertIn("skeleton", result.errors[0])
        self.assertIn("attempt", result.errors[0])


class TestDraftMissingRequired(unittest.TestCase):
    """Cross-validation: topic-or-source required."""

    def test_no_topic_no_source(self):
        result = parse_invocation(SPEC, "--mode=skeleton", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        matching = [
            e for e in result.errors if "topic" in e.lower() or "source" in e.lower()
        ]
        self.assertTrue(
            len(matching) > 0, f"Expected topic/source error, got: {result.errors}"
        )

    def test_empty_input(self):
        result = parse_invocation(SPEC, "", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        matching = [
            e for e in result.errors if "topic" in e.lower() or "source" in e.lower()
        ]
        self.assertTrue(
            len(matching) > 0, f"Expected topic/source error, got: {result.errors}"
        )


class TestDraftClaimSelect(unittest.TestCase):
    """--claim-select requires --source."""

    def test_claim_select_without_source_errors(self):
        result = parse_invocation(SPEC, '"x" --claim-select=first', cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        matching = [
            e for e in result.errors if "claim-select" in e and "source" in e.lower()
        ]
        self.assertTrue(
            len(matching) > 0,
            f"Expected claim-select/source error, got: {result.errors}",
        )

    def test_claim_select_with_source_ok(self):
        result = parse_invocation(
            SPEC, "--source=paper.pdf --claim-select=first", cwd=CWD
        )
        self.assertEqual(result.errors, [])


class TestDraftOutputFileRequiresOut(unittest.TestCase):
    """--output=file without --out."""

    def test_output_file_without_out_errors(self):
        result = parse_invocation(SPEC, '"x" --output=file', cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        matching = [
            e for e in result.errors if "output" in e.lower() and "out" in e.lower()
        ]
        self.assertTrue(
            len(matching) > 0, f"Expected output/out error, got: {result.errors}"
        )


class TestDraftIntentCoercion(unittest.TestCase):
    """Intent auto-collapse coercion."""

    def test_intent_auto_coerced_to_usage(self):
        result = parse_invocation(SPEC, '"x" --intent=auto', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--intent"].value, "usage")
        self.assertEqual(result.options["--intent"].source, "coerced")
        self.assertEqual(result.options["--intent"].coerced_from, "auto")

    def test_intent_math_not_coerced(self):
        result = parse_invocation(SPEC, '"x" --intent=math', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--intent"].value, "math")
        self.assertEqual(result.options["--intent"].source, "explicit")
        self.assertIsNone(result.options["--intent"].coerced_from)


if __name__ == "__main__":
    unittest.main()
