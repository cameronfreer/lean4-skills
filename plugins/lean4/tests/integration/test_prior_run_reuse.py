"""#82C acceptance: explicit prior-run reuse.

A NEW invocation names a prior run; the helper's read-only `reuse` preview
selects the historical material (latest recorded handoff — finality unknown —
and its baseline), checks compatibility, and runs the content-bound drift
check; `custody` re-derives that report before a fresh baseline is recorded;
`start --prior-run --reuse-report` revalidates the observed journal prefix,
applies the shipped rerun guard against the selected handoff, creates the new
run naming `prior_run`, and records the local source-note that later Replans
cite. Refs #82; not resume, not repair, no automatic latest selection.

Stdlib only; POSIX for the store's mutation hosts (the read-only preview also
runs on the Windows portable subset).
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from typing import Any

_HERE = os.path.dirname(os.path.abspath(__file__))
_PLUGIN = os.path.dirname(os.path.dirname(_HERE))
_LIB = os.path.join(_PLUGIN, "lib", "scripts")
sys.path.insert(0, _LIB)
sys.path.insert(0, os.path.join(_PLUGIN, "tests"))
import run_contract_validate as rc  # noqa: E402
import run_persistence as rp  # noqa: E402
import run_reuse as rr  # noqa: E402
import run_store as rs  # noqa: E402
from test_run_contract import valid_dispatch, valid_handoff  # noqa: E402

PERSIST_CMD: list[str] = (
    [os.path.join(_PLUGIN, "bin", "lean4-skills-run-persist")]
    if os.name == "posix"
    else [sys.executable, os.path.join(_LIB, "run_persistence.py")]
)
POSIX = rs.platform_supported()
NOW = "2026-09-09T12:00:00Z"
FIXTURE_ROOT = os.path.join(_PLUGIN, "tests", "fixtures", "run_store")


def _sha(path: str) -> str:
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def _replan(cycle: int, cites: list[str]) -> dict[str, Any]:
    return {
        "schema": rs.REPLAN_SUMMARY_SCHEMA,
        "cycle": cycle,
        "plan": f"cycle {cycle}",
        "failed_approaches": ["exact tendsto_atTop_mono h"],
        "blockers": [
            {
                "file": "/repo/Foo.lean",
                "line": 42,
                "blocker_class": "missing-library-lemma",
                "blocker_signature": "replan-sig",
            }
        ],
        "next_steps": ["try Tendsto.comp"],
        "cites": cites,
    }


class _Env(unittest.TestCase):
    """A project with one real owned file, a store, and a PRIOR run whose
    dispatch/handoff/baseline point at that real file (so drift is real)."""

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="prior-run-")
        self.project = os.path.join(self.tmp, "proj")
        os.makedirs(self.project)
        self.foo = os.path.join(self.project, "Foo.lean")
        with open(self.foo, "w", encoding="utf-8") as f:
            f.write("theorem foo : True := by\n  sorry\n")
        self.root = os.path.join(self.project, ".lean4-skills")
        self.state = os.path.join(self.tmp, "state.json")
        self.env = dict(os.environ, LEAN4_RUN_PERSIST_STATE=self.state, TMPDIR=self.tmp)
        self.env.pop("LEAN4_RUN_STORE", None)

    def tearDown(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    def baseline(self) -> dict[str, Any]:
        p = subprocess.run(
            [
                sys.executable,
                os.path.join(_LIB, "file_baseline.py"),
                "record",
                "--",
                self.foo,
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        return json.loads(p.stdout)

    def dispatch(self, **over: Any) -> dict[str, Any]:
        d = valid_dispatch(target=f"{self.foo}:1", owned_files=[self.foo], **over)
        d["file_baseline"] = self.baseline()
        return d

    def handoff(self, **over: Any) -> dict[str, Any]:
        h = valid_handoff(target=f"{self.foo}:1", files_owned=[self.foo], **over)
        h["file_baseline"] = self.baseline()
        return h

    def make_prior(
        self,
        *,
        handoff: dict[str, Any] | None,
        intermediate: bool = False,
        now: str = NOW,
    ) -> str:
        """A prior run: dispatch(manifest) → failed-avenue note → completed
        review → replan → [handoff (final via set-handoff, or intermediate
        via append)]."""
        res = rs.op_create(
            self.dispatch(),
            storage_root=self.root,
            project_root=self.project,
            tracker_session_id=None,
            prior_run=None,
            now=now,
            event_schema=rs.EVENT_SCHEMA_V2,
        )
        rid = str(res["run_id"])
        rs.op_append(
            self.root,
            rid,
            "note",
            {
                "kind": "failed-avenue",
                "text": "exact foo_lemma: type mismatch",
                "lean": None,
            },
        )
        rs.op_append(
            self.root,
            rid,
            "note",
            {
                "kind": "candidate",
                "text": "a snippet",
                "lean": "example : True := trivial",
            },
        )
        rs.op_append(
            self.root,
            rid,
            "review",
            {
                "schema": rs.REVIEW_RECORD_SCHEMA,
                "cycle": 1,
                "mode": "batch",
                "target": f"{self.foo}:1",
                "scope": "file",
                "line": None,
                "source": "internal",
                "status": "completed",
                "output": {
                    "version": "2.0",
                    "suggestions": [],
                    "summary": {
                        "total_suggestions": 0,
                        "by_severity": {
                            "error": 0,
                            "warning": 0,
                            "advisory": 0,
                            "hint": 0,
                            "style": 0,
                        },
                    },
                    "error": None,
                },
                "triage": None,
                "mapped_handoff": None,
                "detail": None,
            },
        )
        rs.op_append(self.root, rid, "replan", _replan(1, [f"{rid}#1", f"{rid}#3"]))
        if handoff is not None:
            if intermediate:
                rs.op_append(self.root, rid, "handoff", handoff)
            else:
                rs.op_set_handoff(self.root, rid, handoff)
        return rid

    def persist(
        self, *args: str, stdin: str | None = None
    ) -> tuple[int, dict[str, Any]]:
        p = subprocess.run(
            [*PERSIST_CMD, "--root", self.root, "--project-root", self.project, *args],
            input=stdin,
            capture_output=True,
            text=True,
            env=self.env,
            check=False,
        )
        self.assertTrue(p.stdout.strip(), p.stderr)
        return p.returncode, json.loads(p.stdout)

    def preview(self, rid: str, **over: str) -> tuple[int, dict[str, Any]]:
        args = [
            "reuse",
            "--prior-run",
            rid,
            "--target",
            over.get("target", f"{self.foo}:1"),
            "--scope",
            over.get("scope", "sorry"),
            "--mode",
            over.get("mode", "prove"),
            "--owned-file",
            self.foo,
        ]
        return self.persist(*args)

    def write_report(self, report: dict[str, Any]) -> str:
        p = os.path.join(self.tmp, "reuse.json")
        with open(p, "w", encoding="utf-8") as f:
            json.dump(report, f)
        return p


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class PositiveReuse(_Env):
    def test_selected_history_reaches_the_new_run_and_work_proceeds(self) -> None:
        stuck = self.handoff(
            status="stuck",
            blocker_kind="proof",
            blocker_class="missing-library-lemma",
            blocker_signature="Foo.lean:1:unknown identifier",
            new_evidence_required_for_rerun="a lemma about foo",
        )
        prior = self.make_prior(handoff=stuck)
        rc_, rep = self.preview(prior)
        self.assertEqual((rc_, rep["action"]), (0, "preview"), rep)
        sel = rep["selection"]
        self.assertEqual(sel["handoff_finality"], "unknown")
        self.assertTrue(sel["guard_evaluable"])
        self.assertEqual(
            sel["dispatch_cite"], f"{prior}#manifest"
        )  # initial dispatch lives in the manifest
        self.assertEqual(sel["handoff_cite"], f"{prior}#5")
        self.assertEqual(sel["baseline_origin"], f"{prior}#5")
        self.assertEqual(rep["drift"]["result"], "match")
        self.assertEqual(rep["carry"]["prior_blocker"], "Foo.lean:1:unknown identifier")
        self.assertEqual(
            rep["carry"]["replan_blockers"][0]["blocker_signature"], "replan-sig"
        )  # supplement
        hist = rep["historical"]
        self.assertEqual(
            hist["failed_avenues"][0],
            {"text": "exact foo_lemma: type mismatch", "cite": f"{prior}#1"},
        )
        self.assertEqual(hist["reviews"][0]["disposition"], "unknown")
        self.assertEqual(hist["snippets"][0]["verified"], False)
        self.assertEqual(hist["plan_cite"], f"{prior}#4")
        self.assertIn("no ownership", rep["note"])
        # custody: no drift → fresh baseline without a token
        rc_, cus = self.persist(
            "custody", "--report", self.write_report(rep), "--owned-file", self.foo
        )
        self.assertEqual(
            (rc_, cus["action"], cus["result"]), (0, "custody", "match"), cus
        )
        fresh = cus["fresh_baseline"]
        # first dispatch: carries the prior blocker + a justified evidence delta
        d = self.dispatch(
            prior_blocker="Foo.lean:1:unknown identifier",
            evidence_delta=[
                "found Mathlib lemma foo_iff (Foo.lean:12) proving the missing step"
            ],
        )
        d["file_baseline"] = fresh
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            prior,
            "--reuse-report",
            self.write_report(rep),
            "--now",
            "2026-09-10T12:00:00Z",
            stdin=json.dumps(d),
        )
        self.assertEqual((rc_, res["action"]), (0, "continue"), res)
        self.assertEqual(res["prior_run"], prior)
        self.assertEqual(res["source_note_cite"], f"{res['run_id']}#1")
        self.assertTrue(res["guard"]["evaluable"])
        # proof work proceeds: a replan citing the LOCAL source-note, then a finish
        rc_, r = self.persist(
            "replan",
            "--payload",
            "-",
            stdin=json.dumps(_replan(1, [res["source_note_cite"]])),
        )
        self.assertEqual((rc_, r["seq"]), (0, 2), r)
        rc_, fin = self.persist(
            "finish", "--payload", "-", stdin=json.dumps(self.handoff())
        )
        self.assertEqual((rc_, fin["stored"]), (0, True))
        out = rs.op_load(self.root, res["run_id"])
        self.assertEqual(out["manifest"]["prior_run"], prior)
        note = json.loads(out["events"][0]["payload"]["text"])
        self.assertEqual(note["prior_run"], prior)
        self.assertEqual(note["handoff"], f"{prior}#5")
        self.assertEqual(note["historical"]["failed_avenues"][0]["cite"], f"{prior}#1")
        self.assertEqual(
            note["presentation"]["reviews"],
            "recorded as completed; not known to have been applied — reassess",
        )
        self.assertEqual(
            [e["kind"] for e in out["events"]], ["note", "replan", "handoff"]
        )

    def test_cache_state_does_not_affect_selection_or_guard(self) -> None:
        stuck = self.handoff(
            status="stuck",
            blocker_kind="proof",
            blocker_class="arithmetic",
            blocker_signature="sig",
            new_evidence_required_for_rerun="x",
        )
        prior = self.make_prior(handoff=stuck)
        _rc, a = self.preview(prior)
        os.remove(
            os.path.join(self.root, "runs", prior, rs.CACHE_NAME)
        )  # disposable cache gone
        _rc, b = self.preview(prior)
        self.assertEqual(a["selection"], b["selection"])
        self.assertEqual(a["prefix_digest"], b["prefix_digest"])
        self.assertEqual(a["carry"], b["carry"])


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class DriftRefusal(_Env):
    def test_autoprove_stops_before_custody_on_drift(self) -> None:
        prior = self.make_prior(handoff=self.handoff())
        with open(self.foo, "a", encoding="utf-8") as f:
            f.write("-- changed after the prior run\n")
        rc_, rep = self.preview(prior, mode="autoprove")
        self.assertEqual(rep["drift"]["result"], "drift")
        self.assertEqual(rep["drift"]["entries"][0]["status"], "modified")
        # autonomous: no approval token → custody refused → nothing created
        rc_, cus = self.persist(
            "custody", "--report", self.write_report(rep), "--owned-file", self.foo
        )
        self.assertEqual((rc_, cus["code"]), (rp.EXIT_STARTUP, "drift_unapproved"))
        self.assertEqual(
            len(
                [
                    d
                    for d in os.listdir(os.path.join(self.root, "runs"))
                    if rs.valid_run_id(d)
                ]
            ),
            1,
        )

    def test_approval_binds_to_content_not_the_list(self) -> None:
        prior = self.make_prior(handoff=self.handoff())
        with open(self.foo, "a", encoding="utf-8") as f:
            f.write("-- change 1\n")
        rc_, rep = self.preview(prior)
        token = rep["drift"]["approval_token"]
        # the SAME path changes again after approval: same list, different bytes
        with open(self.foo, "a", encoding="utf-8") as f:
            f.write("-- change 2\n")
        rc_, cus = self.persist(
            "custody",
            "--report",
            self.write_report(rep),
            "--owned-file",
            self.foo,
            "--approve",
            token,
        )
        self.assertEqual((rc_, cus["code"]), (rp.EXIT_STARTUP, "custody_mismatch"))
        # a wrong token never passes either
        rc_, rep2 = self.preview(prior)
        rc_, cus = self.persist(
            "custody",
            "--report",
            self.write_report(rep2),
            "--owned-file",
            self.foo,
            "--approve",
            "deadbeef",
        )
        self.assertEqual(cus["code"], "approval_mismatch")
        # the exact approved content → custody with a fresh baseline of the current bytes
        rc_, cus = self.persist(
            "custody",
            "--report",
            self.write_report(rep2),
            "--owned-file",
            self.foo,
            "--approve",
            rep2["drift"]["approval_token"],
        )
        self.assertEqual((rc_, cus["result"]), (0, "drift"))
        self.assertEqual(cus["fresh_baseline"]["files"][0]["sha256"], _sha(self.foo))


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class BlockerGuard(_Env):
    def _stuck_prior(self) -> str:
        return self.make_prior(
            handoff=self.handoff(
                status="stuck",
                blocker_kind="proof",
                blocker_class="missing-library-lemma",
                blocker_signature="Foo.lean:1:unknown identifier",
                new_evidence_required_for_rerun="a lemma about foo",
            )
        )

    def test_unchanged_blocker_is_refused_without_drift(self) -> None:
        prior = self._stuck_prior()
        rc_, rep = self.preview(prior)
        self.assertEqual(
            rep["drift"]["result"], "match"
        )  # no drift: this test is about the guard alone
        d = self.dispatch(
            prior_blocker="Foo.lean:1:unknown identifier", evidence_delta=[]
        )
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            prior,
            "--reuse-report",
            self.write_report(rep),
            "--now",
            "2026-09-10T12:00:00Z",
            stdin=json.dumps(d),
        )
        self.assertEqual((rc_, res["code"]), (rp.EXIT_STARTUP, "rerun_forbidden"), res)
        self.assertEqual(res["new_evidence_required_for_rerun"], "a lemma about foo")
        self.assertEqual(
            len(
                [
                    x
                    for x in os.listdir(os.path.join(self.root, "runs"))
                    if rs.valid_run_id(x)
                ]
            ),
            1,
        )

    def test_blocker_may_not_be_cleared(self) -> None:
        prior = self._stuck_prior()
        rc_, rep = self.preview(prior)
        d = self.dispatch(prior_blocker=None, evidence_delta=["something"])
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            prior,
            "--reuse-report",
            self.write_report(rep),
            "--now",
            "2026-09-10T12:00:00Z",
            stdin=json.dumps(d),
        )
        self.assertEqual((rc_, res["code"]), (rp.EXIT_STARTUP, "blocker_cleared"))

    def test_operational_prior_stop_needs_a_specific_justification(self) -> None:
        prior = self.make_prior(
            handoff=self.handoff(
                status="stopped",
                stop_reason="operational-error",
                stop_detail="run-store journal_damaged",
            )
        )
        rc_, rep = self.preview(prior)
        d = self.dispatch(prior_blocker=None, evidence_delta=["new run"])
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            prior,
            "--reuse-report",
            self.write_report(rep),
            "--now",
            "2026-09-10T12:00:00Z",
            "--evidence-justification",
            "new run",
            stdin=json.dumps(d),
        )
        self.assertEqual(
            (rc_, res["code"]), (rp.EXIT_STARTUP, "justification_required")
        )
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            prior,
            "--reuse-report",
            self.write_report(rep),
            "--now",
            "2026-09-10T12:00:00Z",
            "--evidence-justification",
            "the damaged journal was archived and a fresh store root is used",
            stdin=json.dumps(d),
        )
        self.assertEqual((rc_, res["action"]), (0, "continue"), res)


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class HandoffSelection(_Env):
    def test_intermediate_handoff_keeps_its_blocker_and_baseline(self) -> None:
        with open(self.foo, "a", encoding="utf-8") as f:
            f.write("-- worker edit\n")
        inter = self.handoff(
            status="stuck",
            blocker_kind="proof",
            blocker_class="arithmetic",
            blocker_signature="worker-sig",
            new_evidence_required_for_rerun="x",
            files_changed=[self.foo],
        )
        prior = self.make_prior(handoff=inter, intermediate=True)
        _rc, rep = self.preview(prior)
        sel, carry = rep["selection"], rep["carry"]
        self.assertEqual(
            (sel["handoff_finality"], sel["guard_evaluable"]), ("unknown", True)
        )
        self.assertEqual(sel["baseline_origin"], f"{prior}#5")
        self.assertEqual(
            carry["prior_blocker"], "worker-sig"
        )  # the newest diagnosis, not the replan's
        self.assertEqual(carry["replan_blockers"][0]["blocker_signature"], "replan-sig")
        self.assertEqual(
            rep["drift"]["result"], "match"
        )  # baseline taken from the handoff matches the edited file

    def test_missing_handoff_uses_the_dispatch_baseline_and_guard_is_not_evaluable(
        self,
    ) -> None:
        prior = self.make_prior(handoff=None)
        rc_, rep = self.preview(prior)
        self.assertIsNone(rep["selection"]["handoff_cite"])
        self.assertFalse(rep["selection"]["guard_evaluable"])
        self.assertEqual(rep["selection"]["baseline_origin"], f"{prior}#manifest")
        self.assertIsNone(rep["carry"]["prior_blocker"])
        d = self.dispatch(prior_blocker=None, evidence_delta=[])
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            prior,
            "--reuse-report",
            self.write_report(rep),
            "--now",
            "2026-09-10T12:00:00Z",
            stdin=json.dumps(d),
        )
        self.assertEqual((rc_, res["action"]), (0, "continue"), res)
        self.assertFalse(res["guard"]["evaluable"])
        self.assertIn("cannot be evaluated", res["guard"]["reason"])

    def test_neither_baseline_is_unusable(self) -> None:
        # a v1 fixture-style run whose dispatch baseline points at /repo (no real file): still a baseline
        # → construct a run with NO baseline anywhere by hand-editing the manifest dispatch
        prior = self.make_prior(handoff=None)
        mp = os.path.join(self.root, "runs", prior, rs.MANIFEST_NAME)
        with open(mp, encoding="utf-8") as f:
            m = json.load(f)
        m["dispatch"]["file_baseline"] = None
        with open(mp, "w", encoding="utf-8") as f:
            json.dump(m, f)
        rc_, rep = self.preview(prior)
        self.assertEqual(rc_, rp.EXIT_STARTUP)
        self.assertIn(rep["code"], {"incomplete_run", "no_usable_baseline"})


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class UnusablePriorRuns(_Env):
    def test_cases(self) -> None:
        prior = self.make_prior(handoff=self.handoff())
        # cross-run citation is refused by the store; the local note is the bridge
        rc_, rep = self.preview(prior)
        d = self.dispatch()
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            prior,
            "--reuse-report",
            self.write_report(rep),
            "--now",
            "2026-09-10T12:00:00Z",
            stdin=json.dumps(d),
        )
        self.assertEqual(res["action"], "continue", res)
        rc_, r = self.persist(
            "replan", "--payload", "-", stdin=json.dumps(_replan(1, [f"{prior}#1"]))
        )
        self.assertEqual((rc_, r["outcome"]), (rp.EXIT_STOP, "refused:invalid_payload"))
        os.remove(self.state)
        # changed prior run since the preview
        rs.op_append(
            self.root,
            prior,
            "note",
            {"kind": "candidate", "text": "later", "lean": None},
        )
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            prior,
            "--reuse-report",
            self.write_report(rep),
            "--now",
            "2026-09-11T12:00:00Z",
            stdin=json.dumps(d),
        )
        self.assertEqual((rc_, res["code"]), (rp.EXIT_STARTUP, "prior_run_changed"))
        # lock present → refused, never broken
        lock = os.path.join(self.root, "runs", prior, rs.LOCK_NAME)
        open(lock, "w").close()
        rc_, rep2 = self.preview(prior)
        self.assertEqual((rc_, rep2["code"]), (rp.EXIT_STARTUP, "prior_run_active"))
        self.assertTrue(os.path.exists(lock))
        os.remove(lock)
        # incompatible target / mode
        rc_, rep3 = self.preview(prior, target="/elsewhere/Bar.lean:3")
        self.assertEqual(rep3["code"], "incompatible_target")
        rc_, rep4 = self.preview(prior, mode="golf")
        self.assertEqual(rep4["code"], "incompatible_mode")
        # damaged journal
        with open(os.path.join(self.root, "runs", prior, rs.JOURNAL_NAME), "ab") as f:
            f.write(b"garbage\n")
        rc_, rep5 = self.preview(prior)
        self.assertEqual(rep5["code"], "prior_run_damaged")
        # unknown run / bad id
        rc_, rep6 = self.preview("20260909T120000Z-00000000")
        self.assertEqual(rep6["code"], "no_such_run")
        rc_, rep7 = self.preview("../x")
        self.assertEqual(rep7["code"], "bad_prior_run")
        # reuse without the report → startup error before anything is created
        os.remove(self.state) if os.path.exists(self.state) else None
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            "20260909T120000Z-00000000",
            "--now",
            "2026-09-12T12:00:00Z",
            stdin=json.dumps(d),
        )
        self.assertEqual((rc_, res["code"]), (rp.EXIT_STARTUP, "reuse_report_required"))


class PortablePreview(unittest.TestCase):
    """The read-only selection runs on any host against the tracked v2 fixture."""

    def test_select_from_fixture(self) -> None:
        runs = os.path.join(FIXTURE_ROOT, "runs")
        v2 = [
            d
            for d in os.listdir(runs)
            if rs.valid_run_id(d) and d.startswith("20260910")
        ]
        self.assertEqual(len(v2), 1)
        loaded = rs.op_load(FIXTURE_ROOT, v2[0])
        sel = rr.select(loaded)
        self.assertEqual(sel["dispatch_cite"], f"{v2[0]}#manifest")
        self.assertEqual(sel["handoff_finality"], "unknown")
        self.assertTrue(sel["guard_evaluable"])
        self.assertEqual(sel["historical"]["failed_avenues"][0]["cite"], f"{v2[0]}#1")
        n, digest = rr.prefix_digest(loaded)
        self.assertEqual(n, 4)
        self.assertEqual(len(digest), 64)
        self.assertEqual(rc.validate_handoff(sel["handoff"]), [])


if __name__ == "__main__":
    unittest.main()
