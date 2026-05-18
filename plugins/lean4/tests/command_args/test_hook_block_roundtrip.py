"""Layer 4 hook -> block round-trip integration tests.

For each of the 6 covered commands, verify that:
1. The hook subprocess produces valid JSON with the expected structure.
2. The validated-invocation block in additionalContext round-trips through
   parse_validated_block / format_validated_block.
3. A direct parse_invocation call produces the same ParseResult as the hook.
4. Blocked payloads yield decision=block with expected error phrases.

Also tests the two fail-open paths:
- Import-broken (no lib/command_args on sys.path).
- Parser-exception (shim that raises from parse_invocation).
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

# Ensure lib is importable for direct parse_invocation calls.
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lib"))

from command_args import COMMAND_SPECS, parse_invocation
from command_args.formatter import format_validated_block, parse_validated_block

# ---------------------------------------------------------------------------
# Module-scope constants
# ---------------------------------------------------------------------------

_PLUGIN_ROOT = Path(__file__).resolve().parents[2]
HOOK = str((_PLUGIN_ROOT / "hooks" / "validate_user_prompt.py").resolve(strict=True))


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _run_hook(prompt: str, cwd: str, session_id: str = "test-roundtrip") -> dict:
    """Invoke the hook subprocess and return parsed JSON stdout."""
    payload = json.dumps(
        {
            "session_id": session_id,
            "cwd": cwd,
            "prompt": prompt,
        }
    )
    result = subprocess.run(
        [HOOK],
        input=payload,
        capture_output=True,
        text=True,
        timeout=30,
        env={**os.environ, "CLAUDE_PLUGIN_ROOT": str(_PLUGIN_ROOT)},
    )
    assert result.returncode == 0, (
        f"Hook exited {result.returncode}\nstderr: {result.stderr}"
    )
    return json.loads(result.stdout)


def _extract_block(hook_output: dict) -> str:
    """Pull the additionalContext string from a success hook response."""
    return hook_output["hookSpecificOutput"]["additionalContext"]


def _assert_parse_results_equal(test: unittest.TestCase, a, b, msg_prefix: str = ""):
    """Assert two ParseResult objects have equivalent data."""
    prefix = f"{msg_prefix}: " if msg_prefix else ""
    test.assertEqual(a.command, b.command, f"{prefix}command mismatch")
    test.assertEqual(a.raw_tail, b.raw_tail, f"{prefix}raw_tail mismatch")
    test.assertEqual(a.positionals, b.positionals, f"{prefix}positionals mismatch")
    test.assertEqual(a.errors, b.errors, f"{prefix}errors mismatch")
    test.assertEqual(a.coercions, b.coercions, f"{prefix}coercions mismatch")
    test.assertEqual(a.warnings, b.warnings, f"{prefix}warnings mismatch")
    test.assertEqual(
        set(a.options.keys()), set(b.options.keys()), f"{prefix}option keys mismatch"
    )
    for name in a.options:
        ra, rb = a.options[name], b.options[name]
        test.assertEqual(ra.value, rb.value, f"{prefix}option {name} value")
        test.assertEqual(ra.source, rb.source, f"{prefix}option {name} source")
        test.assertEqual(
            ra.enforcement, rb.enforcement, f"{prefix}option {name} enforcement"
        )
        test.assertEqual(
            ra.coerced_from, rb.coerced_from, f"{prefix}option {name} coerced_from"
        )


# ═══════════════════════════════════════════════════════════════════════════
# /lean4:draft
# ═══════════════════════════════════════════════════════════════════════════


class TestDraftRoundTrip(unittest.TestCase):
    def setUp(self):
        self.tmpdir = tempfile.mkdtemp(prefix="hook_draft_")

    def tearDown(self):
        shutil.rmtree(self.tmpdir, ignore_errors=True)

    def test_draft_topic_defaults(self):
        tail = '"Theorem 1"'
        out = _run_hook(f"/lean4:draft {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["draft"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.command, "draft")
        self.assertEqual(from_hook.positionals["topic"], "Theorem 1")
        _assert_parse_results_equal(self, from_hook, direct, "draft defaults")

        # Format round-trip
        re_block = format_validated_block(direct)
        self.assertEqual(parse_validated_block(re_block).command, "draft")

    def test_draft_with_source_and_mode(self):
        tail = "--source=paper.pdf --mode=attempt"
        out = _run_hook(f"/lean4:draft {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["draft"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.options["--mode"].value, "attempt")
        self.assertEqual(from_hook.options["--source"].value, "paper.pdf")
        _assert_parse_results_equal(self, from_hook, direct, "draft source+mode")

    def test_draft_blocked_no_topic_no_source(self):
        out = _run_hook("/lean4:draft --mode=skeleton", self.tmpdir)
        self.assertEqual(out["decision"], "block")
        self.assertIn("topic", out["reason"].lower())


# ═══════════════════════════════════════════════════════════════════════════
# /lean4:learn
# ═══════════════════════════════════════════════════════════════════════════


class TestLearnRoundTrip(unittest.TestCase):
    def setUp(self):
        self.tmpdir = tempfile.mkdtemp(prefix="hook_learn_")

    def tearDown(self):
        shutil.rmtree(self.tmpdir, ignore_errors=True)

    def test_learn_topic_defaults(self):
        tail = "topology"
        out = _run_hook(f"/lean4:learn {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["learn"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.positionals["topic"], "topology")
        _assert_parse_results_equal(self, from_hook, direct, "learn defaults")

    def test_learn_with_style_and_level(self):
        tail = "groups --style=socratic --level=beginner"
        out = _run_hook(f"/lean4:learn {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["learn"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.options["--style"].value, "socratic")
        self.assertEqual(from_hook.options["--level"].value, "beginner")
        _assert_parse_results_equal(self, from_hook, direct, "learn style+level")

    def test_learn_blocked_bad_style(self):
        out = _run_hook("/lean4:learn topology --style=invalid", self.tmpdir)
        self.assertEqual(out["decision"], "block")
        self.assertIn("invalid", out["reason"])


# ═══════════════════════════════════════════════════════════════════════════
# /lean4:formalize
# ═══════════════════════════════════════════════════════════════════════════


class TestFormalizeRoundTrip(unittest.TestCase):
    def setUp(self):
        self.tmpdir = tempfile.mkdtemp(prefix="hook_formalize_")

    def tearDown(self):
        shutil.rmtree(self.tmpdir, ignore_errors=True)

    def test_formalize_topic_defaults(self):
        tail = '"every prime > 2 is odd"'
        out = _run_hook(f"/lean4:formalize {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["formalize"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.positionals["topic"], "every prime > 2 is odd")
        _assert_parse_results_equal(self, from_hook, direct, "formalize defaults")

    def test_formalize_with_rigor_and_source(self):
        tail = "--source=paper.pdf --rigor=sketch"
        out = _run_hook(f"/lean4:formalize {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["formalize"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.options["--rigor"].value, "sketch")
        _assert_parse_results_equal(self, from_hook, direct, "formalize rigor+source")

    def test_formalize_blocked_no_topic_no_source(self):
        out = _run_hook("/lean4:formalize --rigor=checked", self.tmpdir)
        self.assertEqual(out["decision"], "block")
        self.assertIn("topic", out["reason"].lower())


# ═══════════════════════════════════════════════════════════════════════════
# /lean4:autoformalize
# ═══════════════════════════════════════════════════════════════════════════


class TestAutoformalizeRoundTrip(unittest.TestCase):
    def setUp(self):
        self.tmpdir = tempfile.mkdtemp(prefix="hook_autoformalize_")

    def tearDown(self):
        shutil.rmtree(self.tmpdir, ignore_errors=True)

    def test_autoformalize_valid(self):
        tail = "--source=paper.pdf --claim-select=first --out=output.lean"
        out = _run_hook(f"/lean4:autoformalize {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["autoformalize"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.options["--source"].value, "paper.pdf")
        self.assertEqual(from_hook.options["--claim-select"].value, "first")
        self.assertEqual(from_hook.options["--out"].value, "output.lean")
        _assert_parse_results_equal(self, from_hook, direct, "autoformalize valid")

    def test_autoformalize_with_extras(self):
        tail = "--source=notes.pdf --claim-select=first --out=out.lean --rigor=checked --deep=always"
        out = _run_hook(f"/lean4:autoformalize {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["autoformalize"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.options["--rigor"].value, "checked")
        self.assertEqual(from_hook.options["--deep"].value, "always")
        _assert_parse_results_equal(self, from_hook, direct, "autoformalize extras")

    def test_autoformalize_blocked_missing_source(self):
        out = _run_hook(
            "/lean4:autoformalize --claim-select=first --out=o.lean", self.tmpdir
        )
        self.assertEqual(out["decision"], "block")
        self.assertIn("source", out["reason"].lower())


# ═══════════════════════════════════════════════════════════════════════════
# /lean4:prove
# ═══════════════════════════════════════════════════════════════════════════


class TestProveRoundTrip(unittest.TestCase):
    def setUp(self):
        self.tmpdir = tempfile.mkdtemp(prefix="hook_prove_")

    def tearDown(self):
        shutil.rmtree(self.tmpdir, ignore_errors=True)

    def test_prove_scope_defaults(self):
        tail = "MyFile.lean"
        out = _run_hook(f"/lean4:prove {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["prove"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.positionals["scope"], "MyFile.lean")
        _assert_parse_results_equal(self, from_hook, direct, "prove defaults")

    def test_prove_with_flags(self):
        tail = "Thm.lean --repair-only --planning=on --deep=stuck"
        out = _run_hook(f"/lean4:prove {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["prove"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.options["--repair-only"].value, True)
        self.assertEqual(from_hook.options["--planning"].value, "on")
        self.assertEqual(from_hook.options["--deep"].value, "stuck")
        _assert_parse_results_equal(self, from_hook, direct, "prove flags")

    def test_prove_blocked_bad_flag(self):
        out = _run_hook("/lean4:prove --planning=banana", self.tmpdir)
        self.assertEqual(out["decision"], "block")
        self.assertIn("banana", out["reason"])


# ═══════════════════════════════════════════════════════════════════════════
# /lean4:autoprove
# ═══════════════════════════════════════════════════════════════════════════


class TestAutoproveRoundTrip(unittest.TestCase):
    def setUp(self):
        self.tmpdir = tempfile.mkdtemp(prefix="hook_autoprove_")

    def tearDown(self):
        shutil.rmtree(self.tmpdir, ignore_errors=True)

    def test_autoprove_scope_defaults(self):
        tail = "MyThm.lean"
        out = _run_hook(f"/lean4:autoprove {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["autoprove"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.positionals["scope"], "MyThm.lean")
        _assert_parse_results_equal(self, from_hook, direct, "autoprove defaults")

    def test_autoprove_with_deep_and_commit(self):
        tail = "--deep=always --commit=never --max-cycles=5"
        out = _run_hook(f"/lean4:autoprove {tail}", self.tmpdir)
        block = _extract_block(out)
        from_hook = parse_validated_block(block)
        direct = parse_invocation(COMMAND_SPECS["autoprove"], tail, cwd=self.tmpdir)

        self.assertEqual(from_hook.options["--deep"].value, "always")
        self.assertEqual(from_hook.options["--commit"].value, "never")
        self.assertEqual(from_hook.options["--max-cycles"].value, 5)
        _assert_parse_results_equal(self, from_hook, direct, "autoprove deep+commit")

    def test_autoprove_blocked_bad_deep(self):
        out = _run_hook("/lean4:autoprove --deep=turbo", self.tmpdir)
        self.assertEqual(out["decision"], "block")
        self.assertIn("turbo", out["reason"])


# ═══════════════════════════════════════════════════════════════════════════
# Fail-open tests
# ═══════════════════════════════════════════════════════════════════════════


class TestFailOpen(unittest.TestCase):
    def test_import_broken_fail_open(self):
        """Hook with no lib/command_args on path emits fail-open warning."""
        tmpdir = tempfile.mkdtemp(prefix="hook_failopen_import_")
        try:
            # Copy hook to isolated directory with no lib/command_args
            isolated_hook = os.path.join(tmpdir, "validate_user_prompt.py")
            shutil.copy2(HOOK, isolated_hook)
            os.chmod(isolated_hook, 0o755)

            payload = json.dumps(
                {
                    "session_id": "test-failopen",
                    "cwd": tmpdir,
                    "prompt": '/lean4:draft "hello"',
                }
            )

            # Build a hermetic env: scrub PYTHONPATH, CLAUDE_PLUGIN_ROOT,
            # set PYTHONNOUSERSITE=1 so no user-site packages sneak in.
            env = {}
            for k, v in os.environ.items():
                if k in ("PYTHONPATH", "CLAUDE_PLUGIN_ROOT"):
                    continue
                env[k] = v
            env["PYTHONNOUSERSITE"] = "1"
            # Point CLAUDE_PLUGIN_ROOT at tmpdir (which has no lib/)
            env["CLAUDE_PLUGIN_ROOT"] = tmpdir

            result = subprocess.run(
                [isolated_hook],
                input=payload,
                capture_output=True,
                text=True,
                timeout=30,
                env=env,
            )
            self.assertEqual(result.returncode, 0, f"stderr: {result.stderr}")

            out = json.loads(result.stdout)
            ctx = out["hookSpecificOutput"]["additionalContext"]
            self.assertIn("lean4 parser unavailable", ctx)
            self.assertIn("fell back to model parsing", ctx)
        finally:
            shutil.rmtree(tmpdir, ignore_errors=True)

    def test_parser_exception_fail_open(self):
        """Hook with a shim that raises from parse_invocation emits crash warning."""
        tmpdir = tempfile.mkdtemp(prefix="hook_failopen_crash_")
        try:
            # Copy hook
            isolated_hook = os.path.join(tmpdir, "validate_user_prompt.py")
            shutil.copy2(HOOK, isolated_hook)
            os.chmod(isolated_hook, 0o755)

            # Create a shim command_args package that raises
            lib_dir = os.path.join(tmpdir, "lib")
            pkg_dir = os.path.join(lib_dir, "command_args")
            os.makedirs(pkg_dir)

            # Copy the real specs and types so the import succeeds but
            # parse_invocation raises.
            real_pkg = os.path.join(str(_PLUGIN_ROOT), "lib", "command_args")
            for fname in ("types.py", "tokenizer.py", "formatter.py", "coercions.py"):
                src = os.path.join(real_pkg, fname)
                if os.path.exists(src):
                    shutil.copy2(src, os.path.join(pkg_dir, fname))

            # Copy the specs sub-package wholesale
            real_specs = os.path.join(real_pkg, "specs")
            shutil.copytree(real_specs, os.path.join(pkg_dir, "specs"))

            # Write __init__.py that re-exports everything but overrides parse_invocation
            init_content = (
                "from .formatter import format_validated_block, parse_validated_block\n"
                "from .specs import COMMAND_SPECS\n"
                "\n"
                "def parse_invocation(spec, raw_tail, *, cwd):\n"
                "    raise RuntimeError('Intentional shim explosion for testing')\n"
            )
            with open(os.path.join(pkg_dir, "__init__.py"), "w") as f:
                f.write(init_content)

            payload = json.dumps(
                {
                    "session_id": "test-crash",
                    "cwd": tmpdir,
                    "prompt": '/lean4:draft "hello"',
                }
            )

            env = {}
            for k, v in os.environ.items():
                if k in ("PYTHONPATH", "CLAUDE_PLUGIN_ROOT"):
                    continue
                env[k] = v
            env["PYTHONNOUSERSITE"] = "1"
            env["CLAUDE_PLUGIN_ROOT"] = tmpdir

            result = subprocess.run(
                [isolated_hook],
                input=payload,
                capture_output=True,
                text=True,
                timeout=30,
                env=env,
            )
            self.assertEqual(result.returncode, 0, f"stderr: {result.stderr}")

            out = json.loads(result.stdout)
            ctx = out["hookSpecificOutput"]["additionalContext"]
            self.assertTrue(
                ctx.startswith("[lean4 parser crashed"),
                f"Expected crash prefix, got: {ctx!r}",
            )
        finally:
            shutil.rmtree(tmpdir, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
