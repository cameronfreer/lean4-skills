"""Layer 1 parser golden tests for /lean4:disprove."""
import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args import COMMAND_SPECS, parse_invocation

SPEC = COMMAND_SPECS["disprove"]
CWD = "/tmp"


class TestDisproveHappyPath(unittest.TestCase):
    def test_target_file_line(self):
        result = parse_invocation(SPEC, "Foo.lean:42", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["target"], "Foo.lean:42")

    def test_target_nested_file_line(self):
        result = parse_invocation(SPEC, "Sub/Dir/Foo.lean:7", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["target"], "Sub/Dir/Foo.lean:7")

    def test_target_qualified_name(self):
        result = parse_invocation(SPEC, "MyNs.SubNs.myThm", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.positionals["target"], "MyNs.SubNs.myThm")

    def test_target_bare_identifier(self):
        result = parse_invocation(SPEC, "myThm", cwd=CWD)
        self.assertEqual(result.errors, [])

    def test_defaults_applied(self):
        result = parse_invocation(SPEC, "Foo.lean:1", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--max-cycles"].value, 3)
        self.assertEqual(result.options["--max-stuck-cycles"].value, 2)
        self.assertEqual(result.options["--max-runtime"].value, "5m")
        self.assertEqual(result.options["--negation-policy"].value, "counterexample-only")
        self.assertEqual(result.options["--commit"].value, "ask")
        self.assertEqual(result.options["--commit"].source, "default")


class TestDisproveTargetRequired(unittest.TestCase):
    def test_no_target_errors(self):
        result = parse_invocation(SPEC, "", cwd=CWD)
        self.assertEqual(len(result.errors), 1)
        self.assertIn("target", result.errors[0])

    def test_only_flags_no_target_errors(self):
        result = parse_invocation(SPEC, "--max-cycles=5", cwd=CWD)
        self.assertEqual(len(result.errors), 1)
        self.assertIn("target", result.errors[0])


class TestDisproveTargetShape(unittest.TestCase):
    def test_inline_prop_rejected(self):
        result = parse_invocation(SPEC, '"∀ n : ℕ, n^2 ≥ n"', cwd=CWD)
        self.assertEqual(len(result.errors), 1)
        self.assertIn("expected", result.errors[0])

    def test_file_without_line_rejected(self):
        result = parse_invocation(SPEC, "Foo.lean", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("Foo.lean", result.errors[0])

    def test_file_with_non_numeric_line_rejected(self):
        result = parse_invocation(SPEC, "Foo.lean:abc", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)

    def test_file_with_zero_line_rejected(self):
        """Lean line numbers are 1-indexed; ``Foo.lean:0`` must be rejected."""
        result = parse_invocation(SPEC, "Foo.lean:0", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("Foo.lean:0", result.errors[0])

    def test_name_with_internal_double_dot_rejected(self):
        result = parse_invocation(SPEC, "Ns..Thm", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)


class TestDisproveCommit(unittest.TestCase):
    """--commit is no longer coerced; always-interactive workflow honors the value."""

    def test_commit_default_is_ask(self):
        result = parse_invocation(SPEC, "Foo.lean:1", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--commit"].value, "ask")
        self.assertEqual(result.options["--commit"].source, "default")

    def test_commit_ask_passes_through(self):
        result = parse_invocation(SPEC, "Foo.lean:1 --commit=ask", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--commit"].value, "ask")
        self.assertEqual(result.options["--commit"].source, "explicit")

    def test_commit_auto_passes_through(self):
        result = parse_invocation(SPEC, "Foo.lean:1 --commit=auto", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--commit"].value, "auto")
        self.assertEqual(result.options["--commit"].source, "explicit")

    def test_commit_never_passes_through(self):
        result = parse_invocation(SPEC, "Foo.lean:1 --commit=never", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--commit"].value, "never")
        self.assertEqual(result.options["--commit"].source, "explicit")


class TestDisproveNegationPolicy(unittest.TestCase):
    def test_negation_policy_default(self):
        result = parse_invocation(SPEC, "Foo.lean:1", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(
            result.options["--negation-policy"].value, "counterexample-only"
        )

    def test_negation_policy_with_salvage_rejected(self):
        result = parse_invocation(
            SPEC, "Foo.lean:1 --negation-policy=with-salvage", cwd=CWD
        )
        self.assertTrue(len(result.errors) > 0)


class TestDisproveBudgetTypes(unittest.TestCase):
    def test_max_cycles_negative_rejected(self):
        result = parse_invocation(SPEC, "Foo.lean:1 --max-cycles=-1", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)

    def test_max_cycles_zero_rejected(self):
        result = parse_invocation(SPEC, "Foo.lean:1 --max-cycles=0", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("below minimum", result.errors[0])

    def test_max_stuck_cycles_zero_rejected(self):
        result = parse_invocation(SPEC, "Foo.lean:1 --max-stuck-cycles=0", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)

    def test_max_runtime_valid_minutes(self):
        result = parse_invocation(SPEC, "Foo.lean:1 --max-runtime=10m", cwd=CWD)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.options["--max-runtime"].value, "10m")


class TestDisproveUnknownFlag(unittest.TestCase):
    def test_unknown_flag_errors(self):
        result = parse_invocation(SPEC, "Foo.lean:1 --bogus=x", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("Unknown flag", result.errors[0])

    def test_dropped_mode_flag_errors(self):
        """--mode was removed in the always-interactive refactor."""
        result = parse_invocation(SPEC, "Foo.lean:1 --mode=auto", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)
        self.assertIn("--mode", result.errors[0])

    def test_dropped_external_solver_errors(self):
        """--external-solver moved into the Step 2 menu for the external method."""
        result = parse_invocation(SPEC, "Foo.lean:1 --external-solver=z3", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)

    def test_dropped_allow_native_decide_errors(self):
        """--allow-native-decide moved into the Step 2 menu for decide-cascade."""
        result = parse_invocation(SPEC, "Foo.lean:1 --allow-native-decide=true", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)

    def test_dropped_max_witness_bound_errors(self):
        """--max-witness-bound moved into the Step 2 menu for enumerate."""
        result = parse_invocation(SPEC, "Foo.lean:1 --max-witness-bound=64", cwd=CWD)
        self.assertTrue(len(result.errors) > 0)


if __name__ == "__main__":
    unittest.main()
