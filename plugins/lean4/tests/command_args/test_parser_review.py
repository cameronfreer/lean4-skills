"""Layer 1 parser golden tests for /lean4:review (#110).

/lean4:review gets its first command_args spec in #110: all previously
documented flags plus the two mathlib-review gate flags. These tests pin that
(a) every currently-documented invocation still parses, (b) unknown flags and
bad enums are rejected, and (c) the two gate flags obey the conflict rule
(explicit false == omission; both true -> exactly one error).
"""

from __future__ import annotations

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

SPEC = COMMAND_SPECS["review"]
CWD = "/tmp"


class TestReviewDocumentedInvocations(unittest.TestCase):
    """Every invocation shown in review.md's Usage block still parses."""

    def _ok(self, tail: str):
        result = parse_invocation(SPEC, tail, cwd=CWD)
        self.assertEqual(result.errors, [], f"{tail!r} unexpectedly errored")
        return result

    def test_no_args(self):
        result = self._ok("")
        self.assertNotIn("target", result.positionals)
        self.assertEqual(result.options["--mode"].value, "batch")
        self.assertEqual(result.options["--mathlib-review"].value, False)
        self.assertEqual(result.options["--no-mathlib-review"].value, False)

    def test_target_only(self):
        result = self._ok("File.lean")
        self.assertEqual(result.positionals["target"], "File.lean")

    def test_target_and_line(self):
        result = self._ok("File.lean --line=89")
        self.assertEqual(result.positionals["target"], "File.lean")
        self.assertEqual(result.options["--line"].value, 89)

    def test_target_line_scope_deps(self):
        result = self._ok("File.lean --line=89 --scope=deps")
        self.assertEqual(result.options["--scope"].value, "deps")
        self.assertEqual(result.options["--line"].value, 89)

    def test_scope_project(self):
        self._ok("--scope=project")

    def test_codex_flag(self):
        result = self._ok("File.lean --codex")
        self.assertEqual(result.options["--codex"].value, True)

    def test_hook_path(self):
        result = self._ok("File.lean --hook=./my_hook.py")
        self.assertEqual(result.options["--hook"].value, "./my_hook.py")

    def test_llm_and_mode(self):
        result = self._ok("--llm=gpt-4o --mode=stuck")
        self.assertEqual(result.options["--llm"].value, "gpt-4o")
        self.assertEqual(result.options["--mode"].value, "stuck")

    def test_json_flag(self):
        result = self._ok("--json")
        self.assertEqual(result.options["--json"].value, True)


class TestReviewMathlibFlags(unittest.TestCase):
    def test_opt_in(self):
        result = parse_invocation(SPEC, "--mathlib-review", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--mathlib-review"].value, True)

    def test_opt_out(self):
        result = parse_invocation(SPEC, "--no-mathlib-review", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--no-mathlib-review"].value, True)


class TestReviewConflict(unittest.TestCase):
    def test_both_flags_single_error(self):
        result = parse_invocation(SPEC, "--mathlib-review --no-mathlib-review", cwd=CWD)
        matching = [e for e in result.errors if "mutually exclusive" in e]
        self.assertEqual(len(matching), 1, f"got: {result.errors}")
        self.assertEqual(len(result.errors), 1, f"extra errors: {result.errors}")

    def test_explicit_false_is_omission(self):
        # Explicit false does not participate in the conflict.
        result = parse_invocation(
            SPEC, "--mathlib-review=false --no-mathlib-review", cwd=CWD
        )
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--mathlib-review"].value, False)
        self.assertEqual(result.options["--no-mathlib-review"].value, True)

    def test_target_with_conflict_still_errors_once(self):
        result = parse_invocation(
            SPEC, "File.lean --mathlib-review --no-mathlib-review", cwd=CWD
        )
        matching = [e for e in result.errors if "mutually exclusive" in e]
        self.assertEqual(len(matching), 1, f"got: {result.errors}")


class TestReviewRejections(unittest.TestCase):
    def test_unknown_flag_rejected(self):
        result = parse_invocation(SPEC, "--bogus", cwd=CWD)
        self.assertTrue(any("bogus" in e.lower() for e in result.errors))

    def test_bad_scope_enum_rejected(self):
        result = parse_invocation(SPEC, "--scope=banana", cwd=CWD)
        self.assertTrue(any("banana" in e for e in result.errors))

    def test_bad_mode_enum_rejected(self):
        result = parse_invocation(SPEC, "--mode=turbo", cwd=CWD)
        self.assertTrue(any("turbo" in e for e in result.errors))

    def test_non_positive_line_rejected(self):
        result = parse_invocation(SPEC, "File.lean --line=0", cwd=CWD)
        self.assertTrue(any("line" in e.lower() for e in result.errors))

    def test_two_positionals_rejected(self):
        result = parse_invocation(SPEC, "A.lean B.lean", cwd=CWD)
        self.assertTrue(any("positional" in e.lower() for e in result.errors))


class TestReviewScopePreconditions(unittest.TestCase):
    """sorry/deps require target+line; file requires target (documented in
    review.md's Scope Behavior). The parser is authoritative at startup, so it
    must reject these — the input schema only protects the hook payload."""

    def _errs(self, tail: str) -> list[str]:
        return parse_invocation(SPEC, tail, cwd=CWD).errors

    def test_sorry_without_target_or_line_rejected(self):
        errs = self._errs("--scope=sorry")
        self.assertTrue(any("target" in e for e in errs))
        self.assertTrue(any("--line" in e for e in errs))

    def test_sorry_with_target_but_no_line_rejected(self):
        errs = self._errs("Core.lean --scope=sorry")
        self.assertTrue(any("--line" in e for e in errs))
        self.assertFalse(any("target" in e for e in errs))

    def test_deps_without_target_rejected(self):
        self.assertTrue(any("target" in e for e in self._errs("--scope=deps --line=9")))

    def test_file_without_target_rejected(self):
        self.assertTrue(any("target" in e for e in self._errs("--scope=file")))

    def test_bare_line_without_target_rejected(self):
        self.assertTrue(any("target" in e for e in self._errs("--line=9")))

    def test_documented_valid_scopes_accepted(self):
        for tail in (
            "",
            "Core.lean",
            "Core.lean --line=89",
            "Core.lean --line=89 --scope=deps",
            "Core.lean --scope=file",
            "Core.lean --scope=sorry --line=5",
            "--scope=changed",
            "--scope=project",
        ):
            self.assertEqual(self._errs(tail), [], f"{tail!r} should be accepted")


if __name__ == "__main__":
    unittest.main()
