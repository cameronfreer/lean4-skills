"""Layer 1 parser golden tests for /lean4:formalize."""

from __future__ import annotations

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

SPEC = COMMAND_SPECS["formalize"]
CWD = "/tmp"


class TestFormalizeHappyPath(unittest.TestCase):
    """Happy-path tests."""

    def test_topic_with_rigor(self):
        result = parse_invocation(SPEC, '"Zorn" --rigor=axiomatic', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["topic"], "Zorn")
        self.assertEqual(result.options["--rigor"].value, "axiomatic")
        self.assertEqual(result.options["--rigor"].source, "explicit")

    def test_topic_only_defaults(self):
        result = parse_invocation(SPEC, '"Zorn"', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--rigor"].value, "checked")
        self.assertEqual(result.options["--rigor"].source, "default")

    def test_source_only(self):
        result = parse_invocation(SPEC, "--source=paper.pdf", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertNotIn("topic", result.positionals)
        self.assertEqual(result.options["--source"].value, "paper.pdf")


class TestFormalizeMissingTopicAndSource(unittest.TestCase):
    """topic OR source: missing both -> error."""

    def test_neither_topic_nor_source(self):
        result = parse_invocation(SPEC, "--rigor=checked", cwd=CWD)
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


class TestFormalizeClaimSelectRequiresSource(unittest.TestCase):
    """--claim-select requires --source."""

    def test_claim_select_without_source_errors(self):
        result = parse_invocation(SPEC, '"Zorn" --claim-select=first', cwd=CWD)
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


class TestFormalizeIntentCoercion(unittest.TestCase):
    """--intent=auto is coerced to usage (formalize intent_auto_collapse)."""

    def test_intent_auto_coerced(self):
        result = parse_invocation(SPEC, '"Zorn" --intent=auto', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--intent"].value, "usage")
        self.assertEqual(result.options["--intent"].source, "coerced")
        self.assertEqual(result.options["--intent"].coerced_from, "auto")

    def test_intent_math_not_coerced(self):
        result = parse_invocation(SPEC, '"Zorn" --intent=math', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--intent"].value, "math")
        self.assertEqual(result.options["--intent"].source, "explicit")

    def test_intent_usage_not_coerced(self):
        result = parse_invocation(SPEC, '"Zorn" --intent=usage', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--intent"].value, "usage")
        self.assertEqual(result.options["--intent"].source, "explicit")


class TestFormalizeOutputFileRequiresOut(unittest.TestCase):
    """--output=file without --out errors."""

    def test_output_file_without_out_errors(self):
        result = parse_invocation(SPEC, '"Zorn" --output=file', cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        matching = [
            e for e in result.errors if "output" in e.lower() and "out" in e.lower()
        ]
        self.assertTrue(
            len(matching) > 0, f"Expected output/out error, got: {result.errors}"
        )


if __name__ == "__main__":
    unittest.main()
