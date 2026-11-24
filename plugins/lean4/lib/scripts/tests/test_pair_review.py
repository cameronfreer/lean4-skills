#!/usr/bin/env python3
"""Tests for pair_review.py (issue #88, slice 2), without Lean.

pair_review maps a pair-audit/v1 report to lean4-review-output/v2 for
/lean4:review --pairs. The reports here are built by pair_audit's own pure
``audit``/``report`` functions on the shipped fixture with synthetic probe
records, so the two scripts cannot drift apart; every output is checked
against the shipped review schema by review_validate.
"""

from __future__ import annotations

import io
import json
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from typing import Any

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import pair_audit
import pair_review
from review_validate import load_output_schema, validate_output

FIXTURE = Path(__file__).resolve().parents[3] / "tests" / "fixtures" / "pair_audit"


def load_pairs() -> dict[str, Any]:
    with open(FIXTURE / "pairs.json", encoding="utf-8") as fh:
        data: dict[str, Any] = json.load(fh)
    return data


def rec(name: str, **kw: Any) -> dict[str, Any]:
    out: dict[str, Any] = {
        "name": name,
        "found": True,
        "module": "Pairs.Basic",
        "axioms": [],
        "type": "∀ (n : Nat), n + 0 = n",
    }
    out.update(kw)
    return out


def fixture_report(pairs: dict[str, Any]) -> dict[str, Any]:
    records = {
        "Pairs.add_zero'": rec("Pairs.add_zero'"),
        "Pairs.mul_comm'": rec("Pairs.mul_comm'", axioms=["sorryAx"]),
        "Pairs.exists_gt": rec("Pairs.exists_gt", axioms=["Pairs.choice_like"]),
        "Pairs.zero_add'": rec("Pairs.zero_add'", module="Pairs.Moved"),
        "Pairs.no_such_lemma": rec("Pairs.no_such_lemma", found=False),
    }
    findings = pair_audit.audit(pairs, records, FIXTURE)
    return pair_audit.report("pairs.json", pairs, findings)


class Mapping(unittest.TestCase):
    def setUp(self) -> None:
        self.pairs = load_pairs()
        self.report = fixture_report(self.pairs)
        self.items = pair_review.suggestions(self.pairs, self.report, FIXTURE, None)
        self.by_rule = {i["rule_id"]: i for i in self.items}

    def test_one_suggestion_per_finding(self) -> None:
        self.assertEqual(len(self.items), len(self.report["findings"]))

    def test_output_validates_against_shipped_schema(self) -> None:
        out = pair_review.review_output(self.items)
        result = validate_output(out, load_output_schema())
        self.assertTrue(result.ok, result.errors)

    def test_category_and_rule_id(self) -> None:
        self.assertEqual({i["category"] for i in self.items}, {"formal-pair"})
        codes = {f["code"] for f in self.report["findings"]}
        self.assertEqual({i["rule_id"] for i in self.items}, codes)

    def test_severity_mapping(self) -> None:
        for f, i in zip(self.report["findings"], self.items, strict=True):
            self.assertEqual(
                i["severity"],
                {"error": "error", "warning": "warning", "info": "hint"}[f["severity"]],
            )

    def test_drift_asks_for_a_reread_not_a_mismatch(self) -> None:
        msg = self.by_rule["drift"]["message"]
        self.assertIn("Re-read the informal statement", msg)
        self.assertIn("--update-hashes", msg)
        self.assertNotIn("mismatch", msg.lower())

    def test_location_found_in_formal_file(self) -> None:
        # c1-proved names Pairs/Basic.lean, where add_zero' is on line 4; the
        # fixture's c1 carries no finding, so add a drift against it.
        pairs = load_pairs()
        pairs["claims"][0]["type_hash"] = {"Pairs.add_zero'": "sha256:" + "0" * 64}
        rep = fixture_report(pairs)
        items = pair_review.suggestions(pairs, rep, FIXTURE, None)
        located = [i for i in items if i["file"] == "Pairs/Basic.lean"]
        self.assertTrue(located)
        self.assertEqual(located[0]["line"], 4)

    def test_stale_path_keeps_file_without_line(self) -> None:
        item = self.by_rule["stale-path"]
        self.assertEqual(item["file"], "Pairs/Old.lean")
        self.assertIsNone(item["line"])

    def test_claims_without_file_have_null_location(self) -> None:
        item = self.by_rule["declaration-missing"]
        self.assertIsNone(item["file"])
        self.assertIsNone(item["line"])


class ScopeFilter(unittest.TestCase):
    def test_files_keeps_only_claims_in_scope(self) -> None:
        pairs = load_pairs()
        rep = fixture_report(pairs)
        items = pair_review.suggestions(pairs, rep, FIXTURE, ["./Pairs/Old.lean"])
        self.assertTrue(items)
        self.assertEqual({i["file"] for i in items}, {"Pairs/Old.lean"})

    def test_files_drops_claims_without_file(self) -> None:
        pairs = load_pairs()
        rep = fixture_report(pairs)
        items = pair_review.suggestions(pairs, rep, FIXTURE, ["Other.lean"])
        self.assertEqual(items, [])
        out = pair_review.review_output(items)
        self.assertTrue(validate_output(out, load_output_schema()).ok)


class Inputs(unittest.TestCase):
    def test_wrong_report_schema(self) -> None:
        pairs = load_pairs()
        with self.assertRaises(pair_review.InputError):
            pair_review.suggestions(
                pairs, {"schema": "x", "findings": []}, FIXTURE, None
            )

    def test_unknown_claim(self) -> None:
        pairs = load_pairs()
        rep = {
            "schema": "pair-audit/v1",
            "findings": [
                {
                    "claim": "nope",
                    "declaration": None,
                    "code": "drift",
                    "severity": "warning",
                    "message": "m",
                }
            ],
        }
        with self.assertRaises(pair_review.InputError):
            pair_review.suggestions(pairs, rep, FIXTURE, None)


class Cli(unittest.TestCase):
    def _run(self, argv: list[str]) -> tuple[int, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = pair_review.main(argv)
        return code, out.getvalue()

    def test_exit_codes(self) -> None:
        pairs = load_pairs()
        with tempfile.TemporaryDirectory() as tmp:
            rp = os.path.join(tmp, "report.json")
            with open(rp, "w", encoding="utf-8") as fh:
                json.dump(fixture_report(pairs), fh)
            bad = os.path.join(tmp, "bad.json")
            with open(bad, "w", encoding="utf-8") as fh:
                fh.write("{not json")
            other = os.path.join(tmp, "other.json")
            with open(other, "w", encoding="utf-8") as fh:
                json.dump({"schema": "x"}, fh)
            pp = str(FIXTURE / "pairs.json")
            code, out = self._run([pp, "--report", rp, "--project", str(FIXTURE)])
            self.assertEqual(code, 0)
            self.assertEqual(json.loads(out)["version"], "2.0")
            self.assertEqual(self._run([pp, "--report", bad])[0], 2)
            self.assertEqual(self._run([pp, "--report", other])[0], 3)
            self.assertEqual(self._run([])[0], 2)


if __name__ == "__main__":
    unittest.main()
