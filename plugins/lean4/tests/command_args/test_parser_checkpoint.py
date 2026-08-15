"""Layer 1 parser golden tests for /lean4:checkpoint (#111)."""

from __future__ import annotations

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

SPEC = COMMAND_SPECS["checkpoint"]
CWD = "/tmp"


class TestCheckpointHappyPath(unittest.TestCase):
    def test_all_defaults(self):
        result = parse_invocation(SPEC, "", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--mathlib-mk-all"].value, False)
        self.assertEqual(result.options["--mathlib-mk-all"].source, "default")
        self.assertEqual(result.options["--no-mathlib-mk-all"].value, False)

    def test_message_positional_survives(self):
        result = parse_invocation(SPEC, '"checkpoint after refactor"', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["message"], "checkpoint after refactor")

    def test_message_and_flag(self):
        result = parse_invocation(SPEC, '"msg" --mathlib-mk-all', cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["message"], "msg")
        self.assertEqual(result.options["--mathlib-mk-all"].value, True)
        self.assertEqual(result.options["--mathlib-mk-all"].source, "explicit")

    def test_opt_in(self):
        result = parse_invocation(SPEC, "--mathlib-mk-all", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--mathlib-mk-all"].value, True)

    def test_opt_out(self):
        result = parse_invocation(SPEC, "--no-mathlib-mk-all", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--no-mathlib-mk-all"].value, True)


class TestCheckpointConflict(unittest.TestCase):
    def test_both_flags_single_error(self):
        result = parse_invocation(SPEC, "--mathlib-mk-all --no-mathlib-mk-all", cwd=CWD)
        matching = [e for e in result.errors if "mutually exclusive" in e]
        self.assertEqual(
            len(matching),
            1,
            f"Expected exactly one conflict error, got: {result.errors}",
        )
        self.assertEqual(
            len(result.errors), 1, f"Unexpected extra errors: {result.errors}"
        )

    def test_explicit_false_is_omission(self):
        # Explicit false does not participate in precedence or the conflict.
        result = parse_invocation(
            SPEC, "--mathlib-mk-all=false --no-mathlib-mk-all", cwd=CWD
        )
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--mathlib-mk-all"].value, False)
        self.assertEqual(result.options["--no-mathlib-mk-all"].value, True)

    def test_message_with_conflict_still_errors_once(self):
        result = parse_invocation(
            SPEC, '"msg" --mathlib-mk-all --no-mathlib-mk-all', cwd=CWD
        )
        matching = [e for e in result.errors if "mutually exclusive" in e]
        self.assertEqual(len(matching), 1, f"got: {result.errors}")


class TestCheckpointUnknownFlag(unittest.TestCase):
    def test_unknown_flag_rejected(self):
        result = parse_invocation(SPEC, "--bogus", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertTrue(
            any("bogus" in e.lower() for e in result.errors),
            f"Expected unknown-flag error, got: {result.errors}",
        )


if __name__ == "__main__":
    unittest.main()
