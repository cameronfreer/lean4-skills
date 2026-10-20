"""Layer 1 parser golden tests for /lean4:autoprove."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
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


_PLUGIN = os.path.join(os.path.dirname(__file__), "..", "..")
_TRACKER = os.path.join(_PLUGIN, "lib", "scripts", "cycle_tracker.sh")


class TestAutoproveConcludeAfter(unittest.TestCase):
    """#85: --conclude-after grammar, ranges and fit within its budget."""

    def _parse(self, tail):
        return parse_invocation(SPEC, tail, cwd=CWD)

    def test_default_is_fifteen_percent(self):
        r = self._parse("")
        self.assertEqual(r.errors, [])
        self.assertEqual(r.options["--conclude-after"].value, "15%")
        self.assertEqual(r.options["--conclude-after"].source, "default")
        self.assertEqual(r.options["--conclude-after"].enforcement, "session-enforced")

    def test_valid_forms(self):
        for v in ("0", "0%", "15%", "50%", "2c", "19c", "5m", "90s", "1h", "2C"):
            with self.subTest(v=v):
                self.assertEqual(self._parse(f"--conclude-after={v}").errors, [])

    def test_invalid_forms(self):
        for v in ("51%", "x", "15", "-5%", "2.5%", "0c", "0s", "0m", "c", "%"):
            with self.subTest(v=v):
                errs = self._parse(f"--conclude-after={v}").errors
                self.assertEqual(len(errs), 1, errs)
                self.assertIn("--conclude-after", errs[0])

    def test_zero_forms_name_the_fix(self):
        for v in ("0c", "0s"):
            with self.subTest(v=v):
                self.assertIn(
                    "use 0 to disable", self._parse(f"--conclude-after={v}").errors[0]
                )

    def test_reserve_larger_than_its_budget(self):
        r = self._parse("--max-cycles=3 --conclude-after=3c")
        self.assertIn("reserve larger than its budget", r.errors[0])
        self.assertEqual(self._parse("--max-cycles=3 --conclude-after=2c").errors, [])
        r = self._parse("--max-total-runtime=10m --conclude-after=10m")
        self.assertIn("reserve larger than its budget", r.errors[0])
        self.assertEqual(
            self._parse("--max-total-runtime=10m --conclude-after=599s").errors, []
        )

    def test_duration_against_unlimited_runtime(self):
        r = self._parse("--max-total-runtime=0 --conclude-after=5m")
        self.assertIn("unlimited", r.errors[0])
        # a percentage just reserves no runtime there
        self.assertEqual(
            self._parse("--max-total-runtime=0 --conclude-after=15%").errors, []
        )

    def test_formalize_auto_warns_that_the_phase_is_off(self):
        tail = "--formalize=auto --source=p.pdf --claim-select=first --formalize-out=O.lean"
        r = self._parse(tail)
        self.assertEqual(r.errors, [])
        self.assertTrue(any("per-claim budgets" in w for w in r.warnings), r.warnings)
        r = self._parse(tail + " --conclude-after=0")
        self.assertFalse(any("per-claim budgets" in w for w in r.warnings), r.warnings)

    def test_doc_phrases_are_documented(self):
        docs = ""
        for rel in ("commands/autoprove.md", "skills/lean4/references/cycle-engine.md"):
            with open(os.path.join(_PLUGIN, rel), encoding="utf-8") as f:
                docs += f.read()
        for cv in SPEC.cross_validations:
            if cv.rule_id.startswith("autoprove-conclude-after"):
                for phrase in cv.doc_phrases:
                    with self.subTest(rule=cv.rule_id, phrase=phrase):
                        self.assertIn(phrase, docs)

    @unittest.skipUnless(
        os.name == "posix" and shutil.which("bash"), "the tracker is a bash script"
    )
    def test_parser_and_tracker_agree(self):
        """Startup validation is the same in both places: the parser rejects a
        value iff `cycle-tracker init` refuses it (exit 2)."""
        cases = [
            ("20", "120m", v)
            for v in (
                "0",
                "0%",
                "15%",
                "50%",
                "51%",
                "2c",
                "19c",
                "20c",
                "0c",
                "5m",
                "119m",
                "120m",
                "0s",
                "x",
                "15",
                "2.5%",
            )
        ] + [("3", "0", "5m"), ("3", "0", "15%")]
        with tempfile.TemporaryDirectory() as tmp:
            env = dict(os.environ, TMPDIR=tmp, LEAN4_SESSION_DIR=tmp)
            for k in ("LEAN4_ENV_FILE", "CLAUDE_ENV_FILE", "LEAN4_SESSION_ID"):
                env.pop(k, None)
            for cycles, runtime, v in cases:
                with self.subTest(cycles=cycles, runtime=runtime, v=v):
                    parsed = self._parse(
                        f"--max-cycles={cycles} --max-total-runtime={runtime} "
                        f"--conclude-after={v}"
                    )
                    rt = parsed.options.get("--max-total-runtime")
                    p = subprocess.run(
                        [
                            "bash",
                            _TRACKER,
                            "init",
                            f"--max-cycles={cycles}",
                            "--max-stuck=3",
                            f"--max-runtime={rt.value if rt else runtime}",
                            f"--conclude-after={v}",
                        ],
                        capture_output=True,
                        text=True,
                        env=env,
                        check=False,
                    )
                    self.assertEqual(
                        bool(parsed.errors),
                        p.returncode == 2,
                        (parsed.errors, p.stderr),
                    )


if __name__ == "__main__":
    unittest.main()
