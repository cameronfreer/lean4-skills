"""Layer 1 supplement: subprocess tests for the standalone CLI.

Exercises the lib/scripts/parse_command_args.py sys.path bootstrap
from a clean cwd with no PYTHONPATH.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

_PLUGIN_ROOT = Path(__file__).resolve().parents[2]
CLI = str(
    (_PLUGIN_ROOT / "lib" / "scripts" / "parse_command_args.py").resolve(strict=True)
)


class TestStandaloneCLI(unittest.TestCase):
    """Test parse_command_args.py from a controlled subprocess."""

    def _run(
        self,
        args: list[str],
        *,
        cwd: str | None = None,
        env_override: dict | None = None,
    ) -> subprocess.CompletedProcess:
        env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
        env["PYTHONNOUSERSITE"] = "1"
        if env_override:
            env.update(env_override)
        return subprocess.run(
            [sys.executable, CLI, *args],
            capture_output=True,
            text=True,
            cwd=cwd or tempfile.gettempdir(),
            env=env,
        )

    def test_happy_path_draft(self):
        r = self._run(["draft", "--", '"Theorem 1"'])
        self.assertEqual(r.returncode, 0, msg=r.stderr)
        data = json.loads(r.stdout)
        self.assertEqual(data["command"], "draft")
        self.assertIn("topic", data["positionals"])

    def test_validation_error_exit_2(self):
        r = self._run(["draft", "--", '--output=file "x"'])
        self.assertEqual(r.returncode, 2, msg=r.stderr)
        data = json.loads(r.stdout)
        self.assertIn("errors", data)
        self.assertTrue(len(data["errors"]) > 0)

    def test_unknown_command_exit_1(self):
        r = self._run(["nonexistent", "--", "foo"])
        self.assertEqual(r.returncode, 1)
        self.assertIn("unknown command", r.stderr.lower())

    def test_missing_separator_exit_1(self):
        r = self._run(["draft", "foo"])
        self.assertEqual(r.returncode, 1)
        self.assertIn("--", r.stderr)

    def test_coercion_autoprove(self):
        r = self._run(["autoprove", "--", "--commit=ask --max-cycles=10"])
        self.assertEqual(r.returncode, 0, msg=r.stderr)
        data = json.loads(r.stdout)
        commit = data["options"]["--commit"]
        self.assertEqual(commit["value"], "auto")
        self.assertEqual(commit["source"], "coerced")
        self.assertEqual(commit["coerced_from"], "ask")

    def test_cwd_flag(self):
        """--cwd is passed through to the parser for path-sensitive checks."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create a file so overwrite check fires
            target = os.path.join(tmpdir, "existing.lean")
            with open(target, "w") as f:
                f.write("")
            r = self._run(
                [
                    "draft",
                    "--cwd",
                    tmpdir,
                    "--",
                    '--output=file --out=existing.lean "x"',
                ]
            )
            self.assertEqual(r.returncode, 2, msg=r.stderr)
            data = json.loads(r.stdout)
            self.assertTrue(
                any(
                    "overwrite" in e.lower() or "existing" in e.lower()
                    for e in data["errors"]
                ),
                msg=f"Expected overwrite error, got: {data['errors']}",
            )

    def test_multi_arg_after_separator_rejected(self):
        """Multiple args after -- are rejected (quoting boundaries would be lost)."""
        r = self._run(["draft", "--", '"Theorem 1"', "--mode=attempt"])
        self.assertEqual(r.returncode, 1)
        self.assertIn("exactly one argument", r.stderr.lower())

    def test_unquoted_multi_word_rejected(self):
        """Common mistake: draft -- Theorem 1 (two args, not one quoted string)."""
        r = self._run(["draft", "--", "Theorem", "1"])
        self.assertEqual(r.returncode, 1)
        self.assertIn("exactly one argument", r.stderr.lower())

    def test_json_output_is_valid(self):
        r = self._run(["prove", "--", "Foo.lean"])
        self.assertEqual(r.returncode, 0, msg=r.stderr)
        data = json.loads(r.stdout)
        self.assertIn("command", data)
        self.assertIn("options", data)
        self.assertIn("positionals", data)

    def test_direct_exec(self):
        """CLI is executable directly (shebang + chmod)."""
        r = subprocess.run(
            [CLI, "draft", "--", '"x"'],
            capture_output=True,
            text=True,
            cwd=tempfile.gettempdir(),
            env={k: v for k, v in os.environ.items() if k != "PYTHONPATH"},
        )
        self.assertEqual(r.returncode, 0, msg=r.stderr)


if __name__ == "__main__":
    unittest.main()
