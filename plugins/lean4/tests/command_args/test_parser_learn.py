"""Layer 1 parser golden tests for /lean4:learn."""

from __future__ import annotations

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

SPEC = COMMAND_SPECS["learn"]
CWD = "/tmp"


class TestLearnHappyPath(unittest.TestCase):
    """Happy-path tests."""

    def test_topic_only(self):
        result = parse_invocation(SPEC, '"continuity"', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["topic"], "continuity")
        self.assertEqual(result.options["--mode"].value, "auto")
        self.assertEqual(result.options["--mode"].source, "default")

    def test_empty_input_ok(self):
        """learn allows no positional (conversational discovery)."""
        result = parse_invocation(SPEC, "", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertNotIn("topic", result.positionals)

    def test_topic_with_style(self):
        result = parse_invocation(SPEC, '"groups" --style=socratic', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--style"].value, "socratic")
        self.assertEqual(result.options["--style"].source, "explicit")


class TestLearnTrackWithoutGame(unittest.TestCase):
    """--track without --style=game is coerced to None (warn+ignore)."""

    def test_track_without_game_coerced(self):
        result = parse_invocation(SPEC, '"x" --track=nng-like --style=tour', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--track"].value, None)
        self.assertEqual(result.options["--track"].source, "coerced")
        self.assertEqual(result.options["--track"].coerced_from, "nng-like")

    def test_track_with_game_ok(self):
        result = parse_invocation(SPEC, '"x" --track=nng-like --style=game', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--track"].value, "nng-like")
        self.assertEqual(result.options["--track"].source, "explicit")
        self.assertIsNone(result.options["--track"].coerced_from)


class TestLearnSourceOverridesScope(unittest.TestCase):
    """--source + --scope=file|changed|project -> warning."""

    def test_source_plus_scope_file_warns(self):
        result = parse_invocation(SPEC, "--source=notes.pdf --scope=file", cwd=CWD)
        self.assertEqual(result.errors, [])
        matching = [
            w for w in result.warnings if "source" in w.lower() and "scope" in w.lower()
        ]
        self.assertTrue(
            len(matching) > 0, f"Expected source/scope warning, got: {result.warnings}"
        )

    def test_source_plus_scope_auto_no_warning(self):
        result = parse_invocation(SPEC, "--source=notes.pdf --scope=auto", cwd=CWD)
        self.assertEqual(result.errors, [])
        matching = [
            w for w in result.warnings if "source" in w.lower() and "scope" in w.lower()
        ]
        self.assertEqual(len(matching), 0, f"Unexpected warning: {result.warnings}")


class TestLearnEnumValues(unittest.TestCase):
    """Valid enum values for --mode, --style, --level, --adaptive."""

    def test_mode_valid_values(self):
        for val in ("auto", "repo", "mathlib"):
            result = parse_invocation(SPEC, f'"x" --mode={val}', cwd=CWD)
            self.assertEqual(
                result.errors, [], f"Unexpected error for --mode={val}: {result.errors}"
            )

    def test_style_valid_values(self):
        for val in ("tour", "socratic", "exercise", "game"):
            result = parse_invocation(SPEC, f'"x" --style={val}', cwd=CWD)
            self.assertEqual(
                result.errors,
                [],
                f"Unexpected error for --style={val}: {result.errors}",
            )

    def test_level_valid_values(self):
        for val in ("beginner", "intermediate", "expert"):
            result = parse_invocation(SPEC, f'"x" --level={val}', cwd=CWD)
            self.assertEqual(
                result.errors,
                [],
                f"Unexpected error for --level={val}: {result.errors}",
            )


class TestLearnBadAdaptive(unittest.TestCase):
    """Bad enum for --adaptive."""

    def test_bad_adaptive_value(self):
        result = parse_invocation(SPEC, '"x" --adaptive=banana', cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("banana", result.errors[0])
        self.assertIn("on", result.errors[0])
        self.assertIn("off", result.errors[0])


if __name__ == "__main__":
    unittest.main()
