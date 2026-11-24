#!/usr/bin/env python3
"""Lean integration test for pair_audit.py (issue #88, formal-pair/v1).

Audits tests/fixtures/pair_audit (core Lean, no mathlib) with a real pinned
toolchain: the probe must elaborate under ``lake lean``, every declaration must
get a record, and each claim of pairs.json must get its finding (proved and
clean; sorry under ``proved``; custom axiom; moved declaration and stale file
hint; drift; missing declaration; unformalized). It also checks the auditor's
read-only promise: the probe file is removed and no source changes.

A missing ``lake`` SKIPS locally and FAILS when PAIR_AUDIT_REQUIRE_LEAN=1,
which the lean-integration workflow sets.

Run:  python3 plugins/lean4/tests/integration/test_pair_audit_lean.py -v
"""

from __future__ import annotations

import hashlib
import io
import json
import os
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

HERE = Path(__file__).resolve().parent
PLUGIN = HERE.parent.parent
sys.path.insert(0, str(PLUGIN / "lib" / "scripts"))
import pair_audit  # noqa: E402

FIXTURE = PLUGIN / "tests" / "fixtures" / "pair_audit"
REQUIRE = os.environ.get("PAIR_AUDIT_REQUIRE_LEAN") == "1"


def tree_digest(root: Path) -> dict[str, str]:
    out: dict[str, str] = {}
    for p in sorted(root.rglob("*.lean")):
        if ".lake" in p.parts:
            continue
        out[str(p.relative_to(root))] = hashlib.sha256(p.read_bytes()).hexdigest()
    return out


@unittest.skipUnless(
    shutil.which("lake") or REQUIRE,
    "lake not on PATH (CI sets PAIR_AUDIT_REQUIRE_LEAN=1)",
)
class PairAuditLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if shutil.which("lake") is None:
            raise AssertionError("PAIR_AUDIT_REQUIRE_LEAN=1 but lake is not on PATH")
        cls.tmp = tempfile.mkdtemp(prefix="pair_audit_")
        cls.project = Path(cls.tmp) / "pair_audit"
        shutil.copytree(FIXTURE, cls.project, ignore=shutil.ignore_patterns(".lake"))
        cls.before = tree_digest(cls.project)
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            cls.code = pair_audit.main(
                [
                    str(cls.project / "pairs.json"),
                    "--project",
                    str(cls.project),
                    "--json",
                ]
            )
        cls.stderr = err.getvalue()
        cls.report = json.loads(out.getvalue()) if out.getvalue().strip() else {}

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def codes(self, claim: str) -> set[str]:
        return {f["code"] for f in self.report["findings"] if f["claim"] == claim}

    def test_exit_code_and_report(self) -> None:
        self.assertEqual(self.code, pair_audit.EXIT_FINDINGS, self.stderr)
        self.assertEqual(self.report["schema"], "pair-audit/v1")
        self.assertEqual(self.report["summary"]["claims"], 7)

    def test_findings_per_claim(self) -> None:
        self.assertEqual(self.codes("c1-proved"), {"hash-missing"})
        self.assertIn("sorry-in-proved", self.codes("c2-sorry-proved"))
        self.assertIn("nonstandard-axiom", self.codes("c3-axiom"))
        self.assertTrue({"moved", "stale-path"} <= self.codes("c4-moved"))
        self.assertEqual(self.codes("c5-drift"), {"drift"})
        self.assertIn("declaration-missing", self.codes("c6-missing"))
        self.assertIn("unformalized", self.codes("c7-open"))

    def test_read_only(self) -> None:
        self.assertEqual(tree_digest(self.project), self.before)
        probe_dir = self.project / ".lake" / "pair_audit"
        self.assertEqual(list(probe_dir.glob("*.lean")), [])

    def test_update_hashes_then_clean_hashes(self) -> None:
        pairs = self.project / "pairs.json"
        backup = pairs.read_text(encoding="utf-8")
        try:
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                pair_audit.main(
                    [str(pairs), "--project", str(self.project), "--update-hashes"]
                )
            out = io.StringIO()
            with redirect_stdout(out), redirect_stderr(io.StringIO()):
                pair_audit.main([str(pairs), "--project", str(self.project), "--json"])
            codes = {f["code"] for f in json.loads(out.getvalue())["findings"]}
            self.assertFalse({"drift", "hash-missing"} & codes)
        finally:
            pairs.write_text(backup, encoding="utf-8")


if __name__ == "__main__":
    unittest.main(verbosity=2)
