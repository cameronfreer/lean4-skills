#!/usr/bin/env python3
"""Tests for file_baseline.py (issue #102 drift detection).

Covers the reviewed contract: unchanged / dirty-initial / modified /
deleted / created / multiple targets / mixed drift; duplicate canonical
paths; unsupported schema versions; malformed input; symlink retargeting
(drift even with identical bytes) vs regular-file replacement with
identical bytes (not drift); --only subset explicitness; advancement
touching only the named entries; and the operational-error class being
distinct from both bad input and genuine drift.
"""

from __future__ import annotations

import io
import json
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import file_baseline


def run(argv: list[str], stdin: str = "") -> tuple[int, str, str]:
    out, err = io.StringIO(), io.StringIO()
    old_stdin = sys.stdin
    sys.stdin = io.StringIO(stdin)
    try:
        with redirect_stdout(out), redirect_stderr(err):
            try:
                code = file_baseline.main(["file_baseline.py", *argv])
            except SystemExit as exc:  # argparse or sys.exit paths
                code = int(exc.code) if exc.code is not None else 0
    finally:
        sys.stdin = old_stdin
    return code, out.getvalue(), err.getvalue()


class FileBaselineTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = self._tmp.name
        self.addCleanup(self._tmp.cleanup)
        os.chdir(self.dir)

    def path(self, name: str, content: str | None = None) -> str:
        p = os.path.join(self.dir, name)
        if content is not None:
            with open(p, "w") as f:
                f.write(content)
        return p

    def record(self, *paths: str) -> str:
        code, out, err = run(["record", *paths])
        self.assertEqual(code, 0, err)
        return out

    def check(self, baseline: str, *extra: str) -> tuple[int, dict[str, object]]:
        code, out, _ = run(["check", "--baseline", "-", *extra], stdin=baseline)
        return code, json.loads(out) if out.strip() else {}

    def statuses(self, result: dict[str, object]) -> dict[str, str]:
        entries = result["entries"]
        assert isinstance(entries, list)
        return {e["path"]: e["status"] for e in entries}

    def test_unchanged_single_and_multiple(self) -> None:
        a = self.path("a.txt", "alpha")
        b = self.path("b.txt", "beta")
        code, result = self.check(self.record(a, b))
        self.assertEqual(code, 0)
        self.assertEqual(result["result"], "match")
        self.assertEqual(self.statuses(result), {a: "unchanged", b: "unchanged"})

    def test_dirty_initial_file_is_valid_baseline(self) -> None:
        # "Dirty" relative to git is irrelevant: baseline is the bytes at
        # record time, and an unmodified dirty file stays unchanged.
        a = self.path("dirty.lean", "theorem t : True := by sorry -- WIP edit")
        code, result = self.check(self.record(a))
        self.assertEqual(code, 0)
        self.assertEqual(result["result"], "match")

    def test_modified_deleted_created_and_mixed(self) -> None:
        a = self.path("a.txt", "alpha")
        b = self.path("b.txt", "beta")
        c = os.path.join(self.dir, "c.txt")  # recorded as absent
        base = self.record(a, b, c)
        self.path("a.txt", "ALPHA")  # modified
        os.unlink(b)  # deleted
        self.path("c.txt", "new")  # created
        code, result = self.check(base)
        self.assertEqual(code, 3)
        self.assertEqual(result["result"], "drift")
        self.assertEqual(
            self.statuses(result), {a: "modified", b: "deleted", c: "created"}
        )

    def test_absent_stays_absent_is_unchanged(self) -> None:
        c = os.path.join(self.dir, "never.txt")
        code, result = self.check(self.record(c))
        self.assertEqual(code, 0)
        self.assertEqual(self.statuses(result), {c: "unchanged"})

    def test_regular_file_replacement_identical_bytes_not_drift(self) -> None:
        a = self.path("a.txt", "alpha")
        base = self.record(a)
        os.unlink(a)
        self.path("a.txt", "alpha")  # new inode, same canonical path + bytes
        code, result = self.check(base)
        self.assertEqual(code, 0, result)
        self.assertEqual(result["result"], "match")

    def test_symlink_retargeted_is_drift_even_with_identical_bytes(self) -> None:
        t1 = self.path("target1.txt", "same bytes")
        t2 = self.path("target2.txt", "same bytes")
        link = os.path.join(self.dir, "link.txt")
        os.symlink(t1, link)
        base = self.record(link)
        os.unlink(link)
        os.symlink(t2, link)  # identical content, different resolved target
        code, result = self.check(base)
        self.assertEqual(code, 3)
        self.assertEqual(self.statuses(result)[link], "retargeted")

    def test_duplicate_canonical_paths_rejected(self) -> None:
        a = self.path("a.txt", "alpha")
        link = os.path.join(self.dir, "alias.txt")
        os.symlink(a, link)
        code, _, err = run(["record", a, link])
        self.assertEqual(code, 2)
        self.assertIn("duplicate canonical path", err)

    def test_unsupported_schema_and_malformed_input(self) -> None:
        bad_schema = json.dumps({"schema": "file-baseline/v99", "files": []})
        code, _, err = run(["check", "--baseline", "-"], stdin=bad_schema)
        self.assertEqual(code, 2)
        self.assertIn("unsupported baseline schema", err)
        code, _, err = run(["check", "--baseline", "-"], stdin="not json {")
        self.assertEqual(code, 2)
        self.assertIn("malformed baseline JSON", err)

    def test_only_subset_rejects_unknown_and_reports_unchecked(self) -> None:
        a = self.path("a.txt", "alpha")
        b = self.path("b.txt", "beta")
        base = self.record(a, b)
        code, _, err = run(["check", "--baseline", "-", "--only", "/nope"], stdin=base)
        self.assertEqual(code, 2)
        self.assertIn("not in baseline", err)
        self.path("b.txt", "BETA")  # drift outside the subset
        code, result = self.check(base, "--only", a)
        self.assertEqual(code, 0)  # subset matches...
        self.assertEqual(result["unchecked"], [b])  # ...omission is explicit

    def test_advance_touches_only_named_entries(self) -> None:
        a = self.path("a.txt", "alpha")
        b = self.path("b.txt", "beta")
        base = self.record(a, b)
        self.path("a.txt", "ALPHA")  # my intentional write
        self.path("b.txt", "EXTERNAL")  # someone else's drift
        code, out, err = run(["advance", "--baseline", "-", a], stdin=base)
        self.assertEqual(code, 0, err)
        advanced = json.loads(out)
        by_path = {e["path"]: e for e in advanced["files"]}
        old_by_path = {e["path"]: e for e in json.loads(base)["files"]}
        self.assertNotEqual(by_path[a]["sha256"], old_by_path[a]["sha256"])
        # Untouched entry carried over byte-identical — external drift on b
        # is NOT blessed and still fails the next check.
        self.assertEqual(by_path[b], old_by_path[b])
        code, result = self.check(json.dumps(advanced))
        self.assertEqual(code, 3)
        self.assertEqual(self.statuses(result)[b], "modified")

    def test_advance_unknown_path_rejected(self) -> None:
        a = self.path("a.txt", "alpha")
        base = self.record(a)
        code, _, err = run(["advance", "--baseline", "-", "/elsewhere.txt"], stdin=base)
        self.assertEqual(code, 2)
        self.assertIn("not in baseline", err)

    def test_empty_baseline_rejected(self) -> None:
        empty = json.dumps({"schema": "file-baseline/v1", "files": []})
        code, _, err = run(["check", "--baseline", "-"], stdin=empty)
        self.assertEqual(code, 2)
        self.assertIn("empty baseline", err)

    def test_malformed_entry_shapes_rejected(self) -> None:
        def check_of(entry: dict[str, object]) -> tuple[int, str]:
            base = json.dumps({"schema": "file-baseline/v1", "files": [entry]})
            code, _, err = run(["check", "--baseline", "-"], stdin=base)
            return code, err

        a = self.path("a.txt", "alpha")
        good: dict[str, object] = json.loads(self.record(a))["files"][0]
        mutations: list[tuple[dict[str, object], str]] = [
            ({"path": "relative.txt"}, "must be absolute"),
            ({"exists": "yes"}, "must be a boolean"),
            ({"sha256": "abc"}, "64-hex sha256"),
            ({"size": -1}, "nonnegative integer size"),
            ({"exists": False}, "null sha256/size"),
        ]
        for mutation, needle in mutations:
            entry = dict(good)
            entry.update(mutation)
            code, err = check_of(entry)
            self.assertEqual(code, 2, (mutation, err))
            self.assertIn(needle, err)

    def test_duplicate_baseline_entries_rejected(self) -> None:
        a = self.path("a.txt", "alpha")
        entry = json.loads(self.record(a))["files"][0]
        base = json.dumps({"schema": "file-baseline/v1", "files": [entry, entry]})
        code, _, err = run(["check", "--baseline", "-"], stdin=base)
        self.assertEqual(code, 2)
        self.assertIn("duplicate path/realpath", err)

    def test_cwd_independence_with_decoy(self) -> None:
        proj = os.path.join(self.dir, "proj")
        decoy_dir = os.path.join(self.dir, "decoy")
        os.mkdir(proj)
        os.mkdir(decoy_dir)
        real_file = os.path.join(proj, "Foo.lean")
        with open(real_file, "w") as f:
            f.write("theorem real : True := trivial")
        with open(os.path.join(decoy_dir, "Foo.lean"), "w") as f:
            f.write("theorem decoy : False := sorry")
        os.chdir(proj)
        base = self.record("Foo.lean")  # relative at record time
        stored = json.loads(base)["files"][0]["path"]
        self.assertEqual(stored, real_file)  # stored absolute
        os.chdir(decoy_dir)  # cwd now contains a same-named decoy
        code, result = self.check(base)
        self.assertEqual(code, 0, result)  # checks proj/Foo.lean, not decoy
        # A stale relative selector from the decoy cwd is rejected, not
        # silently rebound to the decoy:
        code, _, err = run(
            ["check", "--baseline", "-", "--only", "Foo.lean"], stdin=base
        )
        self.assertEqual(code, 2)
        self.assertIn("not in baseline", err)
        # Advance from the decoy cwd via the stored absolute path re-records
        # the real file, untouched by the decoy:
        with open(real_file, "a") as f:
            f.write("\n-- advanced")
        code, out, err = run(["advance", "--baseline", "-", stored], stdin=base)
        self.assertEqual(code, 0, err)
        self.assertEqual(json.loads(out)["files"][0]["path"], real_file)

    def test_deleted_symlink_reports_deleted_not_retargeted(self) -> None:
        t = self.path("target.txt", "bytes")
        link = os.path.join(self.dir, "link.txt")
        os.symlink(t, link)
        base = self.record(link)
        os.unlink(link)
        code, result = self.check(base)
        self.assertEqual(code, 3)
        self.assertEqual(self.statuses(result)[link], "deleted")

    def test_error_detail_preserved_in_output(self) -> None:
        a = self.path("a.txt", "alpha")
        base = self.record(a)
        os.unlink(a)
        os.mkdir(a)
        code, result = self.check(base)
        self.assertEqual(code, 4)
        entries = result["entries"]
        assert isinstance(entries, list)
        self.assertIn("not a regular file", entries[0]["detail"])

    def test_operational_error_distinct_from_drift_and_usage(self) -> None:
        d = os.path.join(self.dir, "subdir")
        os.mkdir(d)
        code, _, err = run(["record", d])  # directory: not a regular file
        self.assertEqual(code, 4)
        self.assertIn("not a regular file", err)
        # At check time: entry becomes a directory → operational error wins
        a = self.path("a.txt", "alpha")
        base = self.record(a)
        os.unlink(a)
        os.mkdir(a)
        code, result = self.check(base)
        self.assertEqual(code, 4)
        self.assertEqual(result["result"], "error")
        self.assertEqual(self.statuses(result)[a], "error")


if __name__ == "__main__":
    unittest.main(verbosity=2)
