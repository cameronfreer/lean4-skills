"""Tests for checkpoint_mathlib_roots.py (issue #111).

Runs the script as a subprocess so the real NUL-delimited stdin path and exit
codes are exercised, with real git fixtures. Covers the reviewer's six cases:
added tracked, untracked, deletion, rename (both paths), spaces+newlines in
filenames, and an unrelated modified file excluded — plus the schema, the
--root anchoring, and the operational/usage failure codes.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from typing import Any

_SCRIPT = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    "checkpoint_mathlib_roots.py",
)


def _git(cwd: str, *args: str) -> None:
    subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True)


def _run(root: str, candidates: list[str]) -> tuple[int, Any]:
    payload = b"".join(c.encode("utf-8") + b"\x00" for c in candidates)
    proc = subprocess.run(
        [sys.executable, _SCRIPT, "--root", root],
        input=payload,
        capture_output=True,
    )
    out = proc.stdout.decode("utf-8")
    data = json.loads(out) if out.strip() else {}
    return proc.returncode, data


class CheckpointMathlibRootsTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = self._tmp.name
        self.addCleanup(self._tmp.cleanup)
        os.makedirs(os.path.join(self.root, "Mathlib"), exist_ok=True)
        _git(self.root, "init", "-q")
        _git(self.root, "config", "user.email", "t@t")
        _git(self.root, "config", "user.name", "t")
        self._write("Mathlib/Base.lean", "module\n")
        _git(self.root, "add", "-A")
        _git(self.root, "commit", "-qm", "init")

    def _write(self, rel: str, content: str) -> None:
        path = os.path.join(self.root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(content)

    def _changes(self, data: Any) -> set[tuple[str, str]]:
        return {(c["status"], c["path"]) for c in data["changes"]}

    def test_schema_and_empty(self) -> None:
        code, data = _run(self.root, [])
        self.assertEqual(code, 0)
        self.assertEqual(data["schema"], "checkpoint-mathlib-roots/v1")
        self.assertEqual(data["changes"], [])
        self.assertEqual(os.path.realpath(data["root"]), os.path.realpath(self.root))

    def test_added_tracked_file(self) -> None:
        self._write("Mathlib/Added.lean", "x\n")
        _git(self.root, "add", "Mathlib/Added.lean")
        code, data = _run(self.root, ["Mathlib/Added.lean"])
        self.assertEqual(code, 0)
        self.assertEqual(self._changes(data), {("added", "Mathlib/Added.lean")})

    def test_untracked_file(self) -> None:
        self._write("Mathlib/Untracked.lean", "x\n")
        code, data = _run(self.root, ["Mathlib/Untracked.lean"])
        self.assertEqual(code, 0)
        self.assertEqual(self._changes(data), {("added", "Mathlib/Untracked.lean")})

    def test_deletion(self) -> None:
        _git(self.root, "rm", "-q", "Mathlib/Base.lean")
        code, data = _run(self.root, ["Mathlib/Base.lean"])
        self.assertEqual(code, 0)
        self.assertEqual(self._changes(data), {("deleted", "Mathlib/Base.lean")})

    def test_rename_surfaces_both_paths(self) -> None:
        _git(self.root, "mv", "Mathlib/Base.lean", "Mathlib/Moved.lean")
        code, data = _run(self.root, ["Mathlib/Base.lean", "Mathlib/Moved.lean"])
        self.assertEqual(code, 0)
        # --no-renames means the rename is a delete of the old + add of the new.
        self.assertEqual(
            self._changes(data),
            {("deleted", "Mathlib/Base.lean"), ("added", "Mathlib/Moved.lean")},
        )

    def test_spaces_and_newlines_in_filenames(self) -> None:
        weird_add = "Mathlib/we ird\nname.lean"
        weird_del = "Mathlib/old space.lean"
        self._write(weird_del, "module\n")
        _git(self.root, "add", "-A")
        _git(self.root, "commit", "-qm", "add weird del")
        self._write(weird_add, "x\n")  # untracked, spaces + newline
        os.remove(os.path.join(self.root, weird_del))  # worktree deletion
        code, data = _run(self.root, [weird_add, weird_del])
        self.assertEqual(code, 0)
        self.assertEqual(
            self._changes(data),
            {("added", weird_add), ("deleted", weird_del)},
        )

    def test_unrelated_modified_file_excluded(self) -> None:
        # A modification (not add/delete) never affects the aggregator, and an
        # unrelated file outside the candidate set must not appear.
        self._write("Mathlib/Base.lean", "module\n-- touched\n")  # modify
        self._write("README.md", "unrelated\n")  # outside Mathlib
        _git(self.root, "add", "README.md")
        code, data = _run(self.root, ["Mathlib/Base.lean", "README.md"])
        self.assertEqual(code, 0)
        self.assertEqual(data["changes"], [])

    def test_added_outside_mathlib_excluded(self) -> None:
        self._write("Other/New.lean", "x\n")
        code, data = _run(self.root, ["Other/New.lean"])
        self.assertEqual(code, 0)
        self.assertEqual(data["changes"], [])

    def test_non_lean_under_mathlib_excluded(self) -> None:
        self._write("Mathlib/data.txt", "x\n")
        code, data = _run(self.root, ["Mathlib/data.txt"])
        self.assertEqual(code, 0)
        self.assertEqual(data["changes"], [])

    def test_deterministic_sorted_output(self) -> None:
        for name in ("Mathlib/Zeta.lean", "Mathlib/Alpha.lean", "Mathlib/Mu.lean"):
            self._write(name, "x\n")
        code, data = _run(
            self.root,
            ["Mathlib/Zeta.lean", "Mathlib/Alpha.lean", "Mathlib/Mu.lean"],
        )
        self.assertEqual(code, 0)
        paths = [c["path"] for c in data["changes"]]
        self.assertEqual(paths, sorted(paths))

    def test_missing_root_is_usage_error(self) -> None:
        proc = subprocess.run([sys.executable, _SCRIPT], input=b"", capture_output=True)
        self.assertEqual(proc.returncode, 2)

    def test_root_not_a_directory_is_usage_error(self) -> None:
        code, data = _run(os.path.join(self.root, "nope"), ["Mathlib/x.lean"])
        self.assertEqual(code, 2)
        self.assertEqual(data["error"]["code"], 2)

    def test_non_git_root_is_operational_error(self) -> None:
        with tempfile.TemporaryDirectory() as plain:
            code, data = _run(plain, ["Mathlib/x.lean"])
        self.assertEqual(code, 4)
        self.assertEqual(data["error"]["code"], 4)

    def test_root_relative_when_repo_root_differs(self) -> None:
        # Lean project root is a subdirectory of the git repo; Mathlib/ and the
        # reported paths must be relative to --root, not the git repo root.
        sub = os.path.join(self.root, "sub")
        os.makedirs(os.path.join(sub, "Mathlib"), exist_ok=True)
        self._write("sub/Mathlib/Inner.lean", "x\n")
        code, data = _run(sub, ["Mathlib/Inner.lean"])
        self.assertEqual(code, 0)
        self.assertEqual(self._changes(data), {("added", "Mathlib/Inner.lean")})

    def test_help_exits_zero(self) -> None:
        proc = subprocess.run([sys.executable, _SCRIPT, "--help"], capture_output=True)
        self.assertEqual(proc.returncode, 0)


if __name__ == "__main__":
    unittest.main()
