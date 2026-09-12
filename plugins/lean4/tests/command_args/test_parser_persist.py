"""Layer 1 parser golden tests for the run-persistence flags (#82B, Refs #82).

`--persist` (bool, default off) and `--run-store DIR` (requires `--persist`)
on /lean4:prove and /lean4:autoprove. Existing invocations must parse exactly
as before, and `--run-store` alone must be a startup validation error.
"""

from __future__ import annotations

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

CWD = "/tmp"


class TestPersistFlags(unittest.TestCase):
    def _parse(self, command: str, tail: str):
        return parse_invocation(COMMAND_SPECS[command], tail, cwd=CWD)

    def test_default_off_for_both_commands(self):
        for command in ("prove", "autoprove"):
            result = self._parse(command, "Foo.lean")
            self.assertEqual(result.errors, [])
            self.assertEqual(result.options["--persist"].value, False)
            self.assertIsNone(result.options["--run-store"].value)

    def test_persist_alone(self):
        for command in ("prove", "autoprove"):
            result = self._parse(command, "Foo.lean --persist")
            self.assertEqual(result.errors, [])
            self.assertEqual(result.options["--persist"].value, True)
            self.assertIsNone(result.options["--run-store"].value)

    def test_persist_with_run_store(self):
        for command in ("prove", "autoprove"):
            result = self._parse(command, "Foo.lean --persist --run-store /tmp/store")
            self.assertEqual(result.errors, [])
            self.assertEqual(result.options["--run-store"].value, "/tmp/store")

    def test_run_store_requires_persist(self):
        for command in ("prove", "autoprove"):
            result = self._parse(command, "Foo.lean --run-store /tmp/store")
            self.assertTrue(
                any("--run-store requires --persist" in e for e in result.errors),
                result.errors,
            )

    def test_explicit_false_is_omission(self):
        result = self._parse("prove", "Foo.lean --persist=false")
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--persist"].value, False)

    def test_run_store_with_explicit_false_persist_is_an_error(self):
        # the companion rule is judged on the RESOLVED value, not token presence
        for command in ("prove", "autoprove"):
            result = self._parse(
                command, "Foo.lean --persist=false --run-store /unused"
            )
            self.assertTrue(
                any("--run-store requires --persist" in e for e in result.errors),
                result.errors,
            )
            self.assertEqual(
                len([e for e in result.errors if "--run-store" in e]), 1, result.errors
            )

    def test_unknown_persist_like_flag_rejected(self):
        result = self._parse("autoprove", "Foo.lean --persist-to /x")
        self.assertTrue(result.errors)


if __name__ == "__main__":
    unittest.main()
