#!/usr/bin/env python3
"""Tests for pair_audit.py (issue #88, formal-pair/v1), without Lean.

The Lean side is replaced by synthetic probe records, so this suite covers
the schema and cross-field rules, the probe source, record parsing, every
finding code, the hash update, and the CLI exit codes (0/1/2/3/4). The same
fixture is audited against a real toolchain by
tests/integration/test_pair_audit_lean.py.
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
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import pair_audit

FIXTURE = Path(__file__).resolve().parents[3] / "tests" / "fixtures" / "pair_audit"


def load_fixture() -> dict[str, Any]:
    with open(FIXTURE / "pairs.json", encoding="utf-8") as fh:
        data: dict[str, Any] = json.load(fh)
    return data


def rec(
    name: str,
    found: bool = True,
    module: str = "Pairs.Basic",
    axioms: list[str] | None = None,
    type_text: str = "T",
) -> dict[str, Any]:
    if not found:
        return {"tag": pair_audit.RECORD_TAG, "name": name, "found": False}
    return {
        "tag": pair_audit.RECORD_TAG,
        "name": name,
        "found": True,
        "module": module,
        "axioms": axioms or [],
        "type": type_text,
        "pretty": type_text,
    }


FIXTURE_RECORDS = {
    "Pairs.add_zero'": rec("Pairs.add_zero'", type_text="add_zero type"),
    "Pairs.mul_comm'": rec("Pairs.mul_comm'", axioms=["sorryAx"]),
    "Pairs.exists_gt": rec("Pairs.exists_gt", axioms=["Pairs.choice_like"]),
    "Pairs.zero_add'": rec("Pairs.zero_add'", module="Pairs.Moved"),
    "Pairs.no_such_lemma": rec("Pairs.no_such_lemma", found=False),
}


def run(argv: list[str]) -> tuple[int, str, str]:
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        code = pair_audit.main(argv)
    return code, out.getvalue(), err.getvalue()


def codes(findings: list[pair_audit.Finding], claim: str) -> set[str]:
    return {f.code for f in findings if f.claim == claim}


class SchemaTests(unittest.TestCase):
    def setUp(self) -> None:
        self.schema = pair_audit.load_schema()

    def test_fixture_is_valid(self) -> None:
        self.assertEqual(pair_audit.validate_pairs(load_fixture(), self.schema), [])

    def test_wrong_schema_id(self) -> None:
        data = load_fixture()
        data["schema"] = "formal-pair/v0"
        self.assertTrue(pair_audit.validate_pairs(data, self.schema))

    def test_bad_enum_and_unknown_key(self) -> None:
        data = load_fixture()
        data["claims"][0]["status"] = "done"
        data["claims"][1]["extra"] = 1
        errors = pair_audit.validate_pairs(data, self.schema)
        self.assertTrue(any("not in enum" in e for e in errors))
        self.assertTrue(any("unexpected property 'extra'" in e for e in errors))

    def test_cross_field_rules(self) -> None:
        data = load_fixture()
        data["claims"][1]["id"] = data["claims"][0]["id"]
        del data["claims"][2]["formal"]
        data["claims"][4]["type_hash"] = {
            "Pairs.other": "sha256:00",
            "Pairs.add_zero'": "md5:1",
        }
        errors = pair_audit.validate_pairs(data, self.schema)
        self.assertTrue(any("duplicate id" in e for e in errors))
        self.assertTrue(any("needs 'formal'" in e for e in errors))
        self.assertTrue(any("is not a declaration" in e for e in errors))
        self.assertTrue(any("expected 'sha256:<hex>'" in e for e in errors))


class ProbeTests(unittest.TestCase):
    def test_probe_imports_and_one_eval_per_declaration(self) -> None:
        data = load_fixture()
        names = pair_audit.declarations_to_probe(data)
        self.assertEqual(len(names), len(set(names)))
        src = pair_audit.build_probe(pair_audit.modules_to_import(data), names)
        self.assertTrue(src.startswith("import Lean\nimport Pairs.Basic\n"))
        self.assertEqual(src.count("#eval"), len(names))
        self.assertIn('String.toName "Pairs.add_zero\'"', src)

    def test_parse_records_ignores_noise(self) -> None:
        good = json.dumps(rec("A.b"))
        stdout = "\n".join(
            [
                "warning: declaration uses 'sorry'",
                "{not json",
                json.dumps({"tag": "other", "name": "A.c"}),
                good,
            ]
        )
        self.assertEqual(list(pair_audit.parse_records(stdout)), ["A.b"])


class AuditTests(unittest.TestCase):
    def setUp(self) -> None:
        self.findings = pair_audit.audit(load_fixture(), FIXTURE_RECORDS, FIXTURE)

    def test_each_claim_gets_its_finding(self) -> None:
        f = self.findings
        self.assertEqual(codes(f, "c1-proved"), {"hash-missing"})
        self.assertIn("sorry-in-proved", codes(f, "c2-sorry-proved"))
        self.assertIn("nonstandard-axiom", codes(f, "c3-axiom"))
        self.assertTrue({"moved", "stale-path"} <= codes(f, "c4-moved"))
        self.assertEqual(codes(f, "c5-drift"), {"drift"})
        self.assertTrue(
            {"declaration-missing", "relation-unchecked"} <= codes(f, "c6-missing")
        )
        self.assertEqual(codes(f, "c7-open"), {"unformalized", "relation-unchecked"})
        self.assertEqual(pair_audit.exit_code_for(f), pair_audit.EXIT_FINDINGS)

    def test_axiomatized_custom_axiom_is_info(self) -> None:
        data = load_fixture()
        data["claims"][2]["status"] = "axiomatized"
        found = pair_audit.audit(data, FIXTURE_RECORDS, FIXTURE)
        sev = {x.severity for x in found if x.code == "nonstandard-axiom"}
        self.assertEqual(sev, {"info"})

    def test_partial_without_sorry(self) -> None:
        data = load_fixture()
        data["claims"][0]["status"] = "partial"
        self.assertIn(
            "partial-without-sorry",
            codes(pair_audit.audit(data, FIXTURE_RECORDS, FIXTURE), "c1-proved"),
        )

    def test_missing_record_is_operational(self) -> None:
        records = dict(FIXTURE_RECORDS)
        del records["Pairs.exists_gt"]
        with self.assertRaises(pair_audit.OperationalError):
            pair_audit.audit(load_fixture(), records, FIXTURE)

    def test_update_hashes_clears_drift(self) -> None:
        data = pair_audit.updated_hashes(load_fixture(), FIXTURE_RECORDS)
        self.assertNotIn(
            "type_hash", data["claims"][5]
        )  # missing decl: nothing to record
        found = pair_audit.audit(data, FIXTURE_RECORDS, FIXTURE)
        self.assertFalse({"drift", "hash-missing"} & {x.code for x in found})
        self.assertEqual(
            load_fixture()["claims"][4]["type_hash"]["Pairs.add_zero'"][:12],
            "sha256:00000",
        )  # the input was not mutated


class CliTests(unittest.TestCase):
    def write(self, tmp: str, data: object) -> str:
        path = os.path.join(tmp, "pairs.json")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(data if isinstance(data, str) else json.dumps(data))
        return path

    def test_usage_and_malformed(self) -> None:
        self.assertEqual(run([])[0], pair_audit.EXIT_USAGE)
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(run([self.write(tmp, "{")])[0], pair_audit.EXIT_USAGE)

    def test_schema_invalid(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = self.write(tmp, {"schema": "formal-pair/v1"})
            self.assertEqual(run([path])[0], pair_audit.EXIT_SCHEMA)

    def test_no_lake_is_operational(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = self.write(tmp, load_fixture())
            with mock.patch("shutil.which", return_value=None):
                code, _, err = run([path, "--project", tmp])
        self.assertEqual(code, pair_audit.EXIT_OPERATIONAL)
        self.assertIn("lake", err)

    def test_nothing_to_probe_needs_no_lean(self) -> None:
        data = {"schema": "formal-pair/v1", "claims": [load_fixture()["claims"][6]]}
        data["claims"][0]["relation"] = "matches"
        with tempfile.TemporaryDirectory() as tmp:
            path = self.write(tmp, data)
            code, out, _ = run([path, "--json"])
        self.assertEqual(code, pair_audit.EXIT_CLEAN)
        report = json.loads(out)
        self.assertEqual(report["schema"], "pair-audit/v1")
        self.assertEqual(report["summary"]["info"], 1)

    def test_update_hashes_writes_and_report(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = self.write(tmp, load_fixture())
            stdout = "\n".join(json.dumps(r) for r in FIXTURE_RECORDS.values())
            with mock.patch.object(pair_audit, "run_probe", return_value=stdout):
                code, out, _ = run([path, "--project", str(FIXTURE), "--update-hashes"])
            with open(path, encoding="utf-8") as fh:
                written = json.load(fh)
        self.assertEqual(code, pair_audit.EXIT_FINDINGS)
        self.assertIn("type hashes written", out)
        self.assertTrue(
            written["claims"][0]["type_hash"]["Pairs.add_zero'"].startswith("sha256:")
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
