#!/usr/bin/env python3
"""
Regression tests for sorry_analyzer.py — the coverage-aware exit
semantics and declaration-attribution hardening (silent-pass audit
series: #145 check_axioms_inline, #146 unused_declarations).

Two layers:
  - Unit tests import the module's functions directly (comment/string
    stripping, token boundaries, declaration attribution, ScanResult
    coverage counting).
  - Subprocess tests run the script end-to-end against tempdir fixtures
    and assert EXIT CODES — the load-bearing regressions: an empty
    directory must exit 2 (pre-fix: "Found 0 sorry statement(s)" +
    exit 0), and --report-only must NOT excuse coverage failures.

Run:
    python3 tests/test_sorry_analyzer.py
    # or from repo root:
    python3 plugins/lean4/lib/scripts/tests/test_sorry_analyzer.py
"""

from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

# Allow import from parent directory
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from sorry_analyzer import (
    SORRY_TOKEN_PATTERN,
    extract_declaration_name,
    find_sorries,
    find_sorries_in_file,
    strip_lean_comments_and_strings,
)

SCRIPT = Path(__file__).resolve().parent.parent / "sorry_analyzer.py"


def run_analyzer(*args: str) -> subprocess.CompletedProcess[str]:
    """Run sorry_analyzer.py as a subprocess, capturing output."""
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        capture_output=True,
        text=True,
        check=False,
    )


class TestStripCommentsAndStrings(unittest.TestCase):
    def strip_code(self, line: str, depth: int = 0) -> str:
        code, _ = strip_lean_comments_and_strings(line, depth)
        return code

    def test_sorry_in_line_comment_removed(self) -> None:
        self.assertNotIn("sorry", self.strip_code("exact foo -- sorry later"))

    def test_sorry_in_block_comment_removed(self) -> None:
        self.assertNotIn("sorry", self.strip_code("/- sorry -/ exact foo"))

    def test_sorry_inside_open_block_comment_removed(self) -> None:
        # Entering the line already inside a block comment (depth 1).
        self.assertNotIn("sorry", self.strip_code("this sorry is commentary", depth=1))

    def test_nested_block_comment_depth_tracked(self) -> None:
        _, depth = strip_lean_comments_and_strings("/- outer /- inner", 0)
        self.assertEqual(depth, 2)

    def test_sorry_in_string_literal_removed(self) -> None:
        self.assertNotIn("sorry", self.strip_code('def msg := "say sorry now"'))

    def test_real_code_sorry_kept(self) -> None:
        self.assertIn("sorry", self.strip_code("theorem foo : True := by sorry"))


class TestSorryTokenBoundaries(unittest.TestCase):
    def test_bare_sorry_matches(self) -> None:
        self.assertIsNotNone(SORRY_TOKEN_PATTERN.search("by sorry"))

    def test_sorry_ax_does_not_match(self) -> None:
        self.assertIsNone(SORRY_TOKEN_PATTERN.search("uses sorryAx here"))

    def test_identifier_containing_sorry_does_not_match(self) -> None:
        self.assertIsNone(SORRY_TOKEN_PATTERN.search("def my_sorry := 1"))

    def test_primed_sorry_does_not_match(self) -> None:
        self.assertIsNone(SORRY_TOKEN_PATTERN.search("exact sorry'"))


class TestExtractDeclarationName(unittest.TestCase):
    def attribute(self, source: str) -> str | None:
        """Run extraction with the sorry on the LAST line of source."""
        lines = source.splitlines(keepends=True)
        return extract_declaration_name(lines, len(lines) - 1)

    def test_plain_theorem(self) -> None:
        self.assertEqual(
            self.attribute("theorem foo : True := by\n  sorry\n"),
            "theorem foo",
        )

    def test_private_theorem(self) -> None:
        self.assertEqual(
            self.attribute("private theorem hidden : True := by\n  sorry\n"),
            "theorem hidden",
        )

    def test_same_line_attribute(self) -> None:
        # @[simp] on the SAME line as the declaration — the regex handles
        # this form directly.
        self.assertEqual(
            self.attribute("@[simp] theorem simped : True := by\n  sorry\n"),
            "theorem simped",
        )

    def test_two_line_attribute(self) -> None:
        # @[simp] on its OWN line above the declaration. Works because the
        # backward search reaches the theorem line before the attribute
        # line — pin that so it stays true.
        self.assertEqual(
            self.attribute("@[simp]\ntheorem simped : True := by\n  sorry\n"),
            "theorem simped",
        )

    def test_noncomputable_def(self) -> None:
        # THE fix: modifier-prefixed decls previously returned None.
        # Note the label deliberately drops the modifier — keyword+name is
        # the declaration's identity.
        self.assertEqual(
            self.attribute("noncomputable def opaque : Nat := by\n  sorry\n"),
            "def opaque",
        )

    def test_protected_noncomputable_def(self) -> None:
        self.assertEqual(
            self.attribute("protected noncomputable def both : Nat := by\n  sorry\n"),
            "def both",
        )

    def test_local_instance(self) -> None:
        self.assertEqual(
            self.attribute("local instance inst : Inhabited Nat := by\n  sorry\n"),
            "instance inst",
        )

    def test_abbrev(self) -> None:
        self.assertEqual(
            self.attribute("abbrev shortcut : Nat := by\n  sorry\n"),
            "abbrev shortcut",
        )

    def test_inductive(self) -> None:
        self.assertEqual(
            self.attribute("inductive Tree where\n  sorry\n"),
            "inductive Tree",
        )

    def test_same_line_sorry_attributed(self) -> None:
        # Single-line declaration: header and sorry share a line. The
        # search must start AT the sorry's line, not one above.
        lines = ["def quick : Nat := by sorry\n"]
        self.assertEqual(extract_declaration_name(lines, 0), "def quick")

    def test_no_header_returns_none(self) -> None:
        lines = ["-- just a comment\n", "  sorry\n"]
        self.assertIsNone(extract_declaration_name(lines, 1))


class TestScanResultCoverage(unittest.TestCase):
    def test_directory_counts_scanned_files(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "A.lean").write_text("theorem a : False := by sorry\n")
            (root / "B.lean").write_text("theorem b : True := trivial\n")
            result = find_sorries(root)
            self.assertEqual(result.files_scanned, 2)
            self.assertEqual(result.files_failed, 0)
            self.assertEqual(len(result.sorries), 1)

    def test_empty_directory_scans_zero(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            result = find_sorries(Path(td))
            self.assertEqual(result.files_scanned, 0)
            self.assertEqual(result.files_failed, 0)
            self.assertEqual(result.sorries, [])

    def test_non_lean_files_not_counted(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "notes.txt").write_text("sorry sorry sorry\n")
            result = find_sorries(root)
            self.assertEqual(result.files_scanned, 0)

    def test_lake_excluded_by_default(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lake = root / ".lake" / "packages"
            lake.mkdir(parents=True)
            (lake / "Dep.lean").write_text("theorem dep : False := by sorry\n")
            result = find_sorries(root)
            self.assertEqual(result.files_scanned, 0)
            result_deps = find_sorries(root, include_deps=True)
            self.assertEqual(result_deps.files_scanned, 1)
            self.assertEqual(len(result_deps.sorries), 1)

    def test_unreadable_file_returns_none(self) -> None:
        # Passing a directory where a file is expected forces the open()
        # exception portably (no chmod games that break as root/CI).
        # redirect_stderr keeps the intentional "Could not read" warning
        # out of the test runner's output.
        with (
            tempfile.TemporaryDirectory() as td,
            contextlib.redirect_stderr(io.StringIO()),
        ):
            self.assertIsNone(find_sorries_in_file(Path(td)))

    def test_partial_coverage_some_scanned_some_failed(self) -> None:
        # One readable .lean + one unreadable .lean (a broken symlink,
        # which os.walk lists as a file but open() then fails on). Locks
        # in the "some scanned + some failed" case — distinct from the
        # zero-coverage case: files_scanned>0 AND files_failed>0.
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "Clean.lean").write_text("theorem ok : True := trivial\n")
            broken = root / "Broken.lean"
            try:
                broken.symlink_to(root / "does_not_exist.lean")
            except (OSError, NotImplementedError):
                self.skipTest("symlinks not supported on this platform")
            with contextlib.redirect_stderr(io.StringIO()):
                result = find_sorries(root)
            self.assertEqual(result.files_scanned, 1)
            self.assertEqual(result.files_failed, 1)


class TestExitCodes(unittest.TestCase):
    """Subprocess layer — the load-bearing exit-code regressions."""

    def test_clean_dir_exits_zero(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            Path(td, "Clean.lean").write_text("theorem ok : True := trivial\n")
            proc = run_analyzer(td)
            self.assertEqual(proc.returncode, 0)

    def test_sorry_exits_one(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            Path(td, "S.lean").write_text("theorem s : False := by sorry\n")
            self.assertEqual(run_analyzer(td).returncode, 1)
            self.assertEqual(run_analyzer(td, "--report-only").returncode, 0)

    def test_empty_dir_exits_two(self) -> None:
        # PRIMARY regression: pre-fix this reported "Found 0 sorry
        # statement(s)" and exited 0.
        with tempfile.TemporaryDirectory() as td:
            proc = run_analyzer(td)
            self.assertEqual(proc.returncode, 2)
            self.assertIn("nothing was analyzed", proc.stderr)

    def test_empty_dir_report_only_still_exits_two(self) -> None:
        # --report-only excuses findings, NOT coverage failures.
        with tempfile.TemporaryDirectory() as td:
            self.assertEqual(run_analyzer(td, "--report-only").returncode, 2)

    def test_non_lean_only_dir_exits_two(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            Path(td, "notes.txt").write_text("no lean here\n")
            self.assertEqual(run_analyzer(td).returncode, 2)

    def test_direct_lake_file_target_exits_two(self) -> None:
        # A .lake file passed directly is skipped (stderr message), so
        # zero files were scanned — one of the silent-zero paths; pre-fix
        # exit 0. With --include-deps it scans normally.
        with tempfile.TemporaryDirectory() as td:
            lake = Path(td, ".lake")
            lake.mkdir()
            dep = lake / "Dep.lean"
            dep.write_text("theorem dep : False := by sorry\n")
            proc = run_analyzer(str(dep))
            self.assertEqual(proc.returncode, 2)
            self.assertIn("Skipping dependency file", proc.stderr)
            proc_deps = run_analyzer(str(dep), "--include-deps")
            self.assertEqual(proc_deps.returncode, 1)  # the sorry is found

    def test_partial_coverage_exits_two(self) -> None:
        # A directory with one clean .lean and one unreadable .lean
        # (broken symlink) is PARTIAL coverage: something was scanned,
        # something failed. Must still exit 2 (a gate that missed part of
        # the tree can't answer), with files_scanned=1 / files_failed=1
        # visible in the JSON. stderr carries "coverage is incomplete".
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "Clean.lean").write_text("theorem ok : True := trivial\n")
            broken = root / "Broken.lean"
            try:
                broken.symlink_to(root / "does_not_exist.lean")
            except (OSError, NotImplementedError):
                self.skipTest("symlinks not supported on this platform")
            proc = run_analyzer(str(root), "--format=json")
            self.assertEqual(proc.returncode, 2)
            self.assertIn("coverage is incomplete", proc.stderr)
            data = json.loads(proc.stdout)
            self.assertEqual(data["files_scanned"], 1)
            self.assertEqual(data["files_failed"], 1)

    def test_json_on_empty_dir_is_valid_json(self) -> None:
        # Warnings go to stderr; stdout must remain parseable JSON even on
        # coverage failure.
        with tempfile.TemporaryDirectory() as td:
            proc = run_analyzer(td, "--format=json")
            self.assertEqual(proc.returncode, 2)
            data = json.loads(proc.stdout)
            self.assertEqual(data["total_count"], 0)
            self.assertEqual(data["files_scanned"], 0)

    def test_json_contract_on_findings(self) -> None:
        # Locks the additive JSON contract for normal consumers:
        # total_count, sorries, files_scanned, files_failed.
        with tempfile.TemporaryDirectory() as td:
            Path(td, "S.lean").write_text("noncomputable def stub : Nat := by sorry\n")
            proc = run_analyzer(td, "--format=json")
            self.assertEqual(proc.returncode, 1)
            data = json.loads(proc.stdout)
            self.assertEqual(data["total_count"], 1)
            self.assertEqual(data["files_scanned"], 1)
            self.assertEqual(data["files_failed"], 0)
            self.assertEqual(data["sorries"][0]["in_declaration"], "def stub")


if __name__ == "__main__":
    unittest.main()
