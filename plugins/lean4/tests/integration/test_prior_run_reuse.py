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
from itertools import pairwise
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

    def preview(self, rid: str, **over: Any) -> tuple[int, dict[str, Any]]:
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
        ]
        for f in over.get("owned", [self.foo]):
            args += ["--owned-file", f]
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
        self.assertEqual(sel["baseline_origins"], {self.foo: f"{prior}#5"})
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
        self.assertEqual(sel["baseline_origins"], {self.foo: f"{prior}#5"})
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
        self.assertEqual(
            rep["selection"]["baseline_origins"], {self.foo: f"{prior}#manifest"}
        )
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


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class ReviewRound1(_Env):
    """PR #206 review round 1: the four correction areas + two hardenings."""

    def _start(
        self, prior: str, rep: dict[str, Any], d: dict[str, Any], **env: str
    ) -> tuple[int, dict[str, Any]]:
        e = dict(self.env, **env)
        p = subprocess.run(
            [
                *PERSIST_CMD,
                "--root",
                self.root,
                "--project-root",
                self.project,
                "start",
                "--dispatch",
                "-",
                "--prior-run",
                prior,
                "--reuse-report",
                self.write_report(rep),
                "--now",
                "2026-09-10T12:00:00Z",
            ],
            input=json.dumps(d),
            capture_output=True,
            text=True,
            env=e,
            check=False,
        )
        self.assertTrue(p.stdout.strip(), p.stderr)
        return p.returncode, json.loads(p.stdout)

    def _fake_store(self, on_append: str) -> dict[str, str]:
        """A real store whose `append` (only) is preceded by `on_append`;
        `create` stays real, so the run is created and the source-note is the
        write under test."""
        fake = os.path.join(self.tmp, "fake_store.py")
        with open(fake, "w", encoding="utf-8") as f:
            f.write(
                "import json, os, sys\nargs = sys.argv[1:]\n"
                + f"sys.path.insert(0, {_LIB!r})\n"
                + "import run_store as rs\n"
                + "if 'append' in args:\n"
                + "".join("    " + line + "\n" for line in on_append.splitlines())
                + "sys.exit(rs.main(args))\n"
            )
        return {"LEAN4_RUN_STORE_ARGV": json.dumps([sys.executable, fake])}

    def _frozen_state_dir(self) -> str:
        d = os.path.join(self.tmp, "st")
        os.makedirs(d)
        self.state = os.path.join(d, "state.json")
        self.env["LEAN4_RUN_PERSIST_STATE"] = self.state
        return d

    # --- 1. the source-note write's outcome is reported, whatever the bookkeeping

    def test_committed_source_note_with_failed_bookkeeping_reports_the_cite(
        self,
    ) -> None:
        prior = self.make_prior(handoff=self.handoff())
        _rc, rep = self.preview(prior)
        state_dir = self._frozen_state_dir()
        env = self._fake_store(f"os.chmod({state_dir!r}, 0o500)")
        try:
            code, res = self._start(prior, rep, self.dispatch(), **env)
        finally:
            os.chmod(state_dir, 0o700)
        # the note WAS committed: its citation is reported, with the fallback
        # handoff, and the invocation is told to stop now — no exception, no silence
        self.assertEqual(
            (code, res["action"], res["outcome"]),
            (rp.EXIT_STOP, "stop", "state_unwritable"),
            res,
        )
        self.assertEqual(res["committed"]["cite"], f"{res['run_id']}#1")
        self.assertTrue(res["run_created"])
        self.assertEqual(res["prior_run"], prior)
        self.assertEqual(res["handoff"]["stop_reason"], "operational-error")
        out = rs.op_load(self.root, res["run_id"])
        self.assertEqual([e["kind"] for e in out["events"]], ["note"])
        with open(self.state, encoding="utf-8") as f:
            st = json.load(f)
        self.assertIsNotNone(st["inflight"])  # unresolved on disk → next call stops
        rc_, nxt = self.persist(
            "note", "--kind", "candidate", "--text", "after the failed bookkeeping"
        )
        self.assertEqual((rc_, nxt["outcome"]), (rp.EXIT_STOP, "terminal"))
        self.assertEqual(len(rs.op_load(self.root, res["run_id"])["events"]), 1)

    def test_refused_source_note_is_a_stop_with_the_fallback_handoff(self) -> None:
        prior = self.make_prior(handoff=self.handoff())
        _rc, rep = self.preview(prior)
        env = self._fake_store(
            "def bad_fsync(fd):\n"
            "    import os as _os, stat as _stat\n"
            "    if _stat.S_ISDIR(_os.fstat(fd).st_mode): raise OSError(5, 'injected barrier failure')\n"
            "    _os.fsync(fd)\n"
            "rs._fsync = bad_fsync"
        )
        code, res = self._start(prior, rep, self.dispatch(), **env)
        self.assertEqual(
            (code, res["action"], res["outcome"]),
            (rp.EXIT_STOP, "stop", "refused:publish_unsynced"),
            res,
        )
        self.assertTrue(res["run_created"])
        self.assertEqual(res["unpersisted"]["status"], "not-stored")
        self.assertEqual(res["handoff"]["stop_reason"], "operational-error")
        self.assertEqual(rs.op_load(self.root, res["run_id"])["events"], [])

    def test_indeterminate_source_note_with_failed_bookkeeping_is_reported(
        self,
    ) -> None:
        prior = self.make_prior(handoff=self.handoff())
        _rc, rep = self.preview(prior)
        state_dir = self._frozen_state_dir()
        env = self._fake_store(
            "def _journal_ino():\n"
            "    root = args[args.index('--root') + 1]\n"
            "    rid = args[args.index('--run-id') + 1]\n"
            "    st = os.stat(os.path.join(root, 'runs', rid, 'events.jsonl'))\n"
            "    return (st.st_dev, st.st_ino)\n"
            "def bad_fsync(fd):\n"
            "    st = os.fstat(fd)\n"
            "    if (st.st_dev, st.st_ino) == _journal_ino(): raise OSError(5, 'injected journal fsync failure')\n"
            "    os.fsync(fd)\n"
            "rs._fsync = bad_fsync\n" + f"os.chmod({state_dir!r}, 0o500)"
        )
        try:
            code, res = self._start(prior, rep, self.dispatch(), **env)
        finally:
            os.chmod(state_dir, 0o700)
        self.assertEqual(
            (code, res["action"], res["outcome"]),
            (rp.EXIT_STOP, "stop", "indeterminate"),
            res,
        )
        self.assertEqual(res["unpersisted"]["status"], "unconfirmed")
        self.assertIn("invocation state could not be updated", res["warning"])
        self.assertEqual(res["handoff"]["stop_reason"], "operational-error")

    # --- 2. per-file baselines: a partial worker baseline cannot hide drift

    def test_partial_worker_baseline_does_not_hide_drift_in_uncovered_file(
        self,
    ) -> None:
        prior = self.make_prior(handoff=None)
        other = os.path.join(self.project, "Other.txt")
        with open(other, "w", encoding="utf-8") as f:
            f.write("original accepted bytes\n")
        _c, both, _e = rr._baseline_cmd(["record", "--", self.foo, other], None)
        d = self.dispatch()
        d["owned_files"] = [self.foo, other]
        d["file_baseline"] = both
        rs.op_append(self.root, prior, "dispatch", d)
        rs.op_append(self.root, prior, "handoff", self.handoff())  # Foo only
        with open(other, "w", encoding="utf-8") as f:
            f.write("external change after dispatch and worker handoff\n")
        _rc, rep = self.preview(prior, owned=[self.foo, other])
        self.assertEqual(rep["action"], "preview", rep)
        # the handoff's entry supersedes the dispatch's for Foo; Other keeps
        # the dispatch's entry (recorded at #5) — and it drifted
        self.assertEqual(
            rep["selection"]["baseline_origins"],
            {self.foo: f"{prior}#6", other: f"{prior}#5"},
        )
        self.assertEqual(rep["drift"]["result"], "drift")
        self.assertEqual(
            [e["status"] for e in rep["drift"]["entries"] if e["path"] == other],
            ["modified"],
        )
        rc_, cus = self.persist(
            "custody",
            "--report",
            self.write_report(rep),
            "--owned-file",
            self.foo,
            "--owned-file",
            other,
        )
        self.assertEqual((rc_, cus["code"]), (rp.EXIT_STARTUP, "drift_unapproved"))

    def test_intended_file_without_any_prior_baseline_is_an_explicit_outcome(
        self,
    ) -> None:
        prior = self.make_prior(handoff=self.handoff())
        other = os.path.join(self.project, "Other.txt")
        with open(other, "w", encoding="utf-8") as f:
            f.write("never baselined by the prior run\n")
        _rc, rep = self.preview(prior, owned=[self.foo, other])
        self.assertEqual(rep["drift"]["result"], "uncovered", rep)
        self.assertEqual(rep["drift"]["uncovered"], [other])
        tok = rep["drift"]["approval_token"]
        # never an implicit match: custody needs the content-bound approval
        rc_, cus = self.persist(
            "custody",
            "--report",
            self.write_report(rep),
            "--owned-file",
            self.foo,
            "--owned-file",
            other,
        )
        self.assertEqual((rc_, cus["code"]), (rp.EXIT_STARTUP, "drift_unapproved"))
        rc_, cus = self.persist(
            "custody",
            "--report",
            self.write_report(rep),
            "--owned-file",
            self.foo,
            "--owned-file",
            other,
            "--approve",
            tok,
        )
        self.assertEqual(
            (rc_, cus["result"], cus["uncovered"]), (0, "uncovered", [other])
        )
        self.assertEqual(
            sorted(e["path"] for e in cus["fresh_baseline"]["files"]),
            sorted([self.foo, other]),
        )
        # ... and the token binds the uncovered file's content too
        with open(other, "a", encoding="utf-8") as f:
            f.write("changed again\n")
        rc_, cus = self.persist(
            "custody",
            "--report",
            self.write_report(rep),
            "--owned-file",
            self.foo,
            "--owned-file",
            other,
            "--approve",
            tok,
        )
        self.assertEqual((rc_, cus["code"]), (rp.EXIT_STARTUP, "custody_mismatch"))

    # --- 3. the preview is bound to the invocation and re-checked at start

    def test_current_owned_file_outside_the_project_is_refused(self) -> None:
        prior = self.make_prior(handoff=self.handoff())
        outside = os.path.join(self.tmp, "outside-project.txt")
        with open(outside, "w", encoding="utf-8") as f:
            f.write("not inside the selected project\n")
        rc_, rep = self.preview(prior, owned=[outside])
        self.assertEqual(
            (rc_, rep["code"]), (rp.EXIT_STARTUP, "incompatible_owned_files")
        )
        # a valid report cannot be re-pointed at it either
        _rc, good = self.preview(prior)
        rc_, cus = self.persist(
            "custody", "--report", self.write_report(good), "--owned-file", outside
        )
        self.assertEqual((rc_, cus["code"]), (rp.EXIT_STARTUP, "reuse_report_mismatch"))
        d = self.dispatch()
        d["owned_files"] = [outside]
        code, res = self._start(prior, good, d)
        self.assertEqual((code, res["code"]), (rp.EXIT_STARTUP, "invalid_dispatch"))

    def test_preview_for_one_target_cannot_start_another(self) -> None:
        prior = self.make_prior(handoff=self.handoff())
        _rc, rep = self.preview(prior)
        d = self.dispatch()
        d["target"] = "/another-project/Unrelated.lean:99"
        self.assertEqual(rc.validate_dispatch(d), [])
        code, res = self._start(prior, rep, d)
        self.assertEqual(
            (code, res["code"]), (rp.EXIT_STARTUP, "reuse_report_mismatch")
        )
        self.assertIn("target", res["detail"])
        self.assertEqual(
            [
                r
                for r in os.listdir(os.path.join(self.root, "runs"))
                if rs.valid_run_id(r)
            ],
            [prior],
        )
        # a mode switch within the family is a different invocation too
        d = self.dispatch(mode="autoprove")
        code, res = self._start(prior, rep, d)
        self.assertEqual(
            (code, res["code"]), (rp.EXIT_STARTUP, "reuse_report_mismatch")
        )
        # and a report forged for a task the prior run does not cover is still
        # re-checked against the ACTUAL dispatch at start (bind passes; compat fails)
        forged = json.loads(json.dumps(rep))
        forged["invocation"]["target"] = f"{self.foo}:7"
        d = self.dispatch()
        d["target"] = f"{self.foo}:7"
        code, res = self._start(prior, forged, d)
        self.assertEqual((code, res["code"]), (rp.EXIT_STARTUP, "incompatible_target"))

    # --- 4. the historical material itself reaches the new run

    def test_recommendations_search_results_and_snippets_reach_the_new_run(
        self,
    ) -> None:
        prior = self.make_prior(handoff=self.handoff())
        record = json.loads(
            json.dumps(rs.op_load(self.root, prior)["events"][2]["payload"])
        )
        record["output"]["suggestions"] = [
            {
                "file": self.foo,
                "line": 1,
                "column": None,
                "severity": "warning",
                "category": "api",
                "rule_id": None,
                "message": "UNIQUE_RECOMMENDATION: generalize the quantified input",
                "fix": None,
            }
        ]
        record["output"]["summary"]["total_suggestions"] = 1
        record["output"]["summary"]["by_severity"]["warning"] = 1
        rs.op_append(self.root, prior, "review", record)
        rs.op_append(
            self.root,
            prior,
            "note",
            {
                "kind": "search-result",
                "text": "UNIQUE_SEARCH_RESULT: use lemma foo_iff",
                "lean": None,
            },
        )
        _rc, rep = self.preview(prior)
        hist = rep["historical"]
        self.assertEqual(
            hist["reviews"][1]["recommendations"][0]["message"],
            "UNIQUE_RECOMMENDATION: generalize the quantified input",
        )
        self.assertEqual(hist["reviews"][1]["disposition"], "unknown")
        self.assertEqual(
            [n["text"] for n in hist["notes"] if n["kind"] == "search-result"],
            ["UNIQUE_SEARCH_RESULT: use lemma foo_iff"],
        )
        self.assertEqual(hist["snippets"][0]["lean"], "example : True := trivial")
        self.assertEqual(hist["snippets"][0]["verified"], False)
        code, res = self._start(prior, rep, self.dispatch())
        self.assertEqual((code, res["action"]), (0, "continue"), res)
        note = json.loads(
            rs.op_load(self.root, res["run_id"])["events"][0]["payload"]["text"]
        )
        text = json.dumps(note)
        self.assertIn("UNIQUE_RECOMMENDATION", text)
        self.assertIn("UNIQUE_SEARCH_RESULT", text)
        self.assertIn("example : True := trivial", text)
        self.assertEqual(note["historical"]["reviews"][1]["cite"], f"{prior}#6")

    # --- hardening: report shape; manifest in the observation digest

    def test_malformed_report_is_a_structured_refusal(self) -> None:
        prior = self.make_prior(handoff=self.handoff())
        _rc, rep = self.preview(prior)
        for mutate in (
            lambda r: r.pop("source_note_text"),
            lambda r: r.pop("invocation"),
            lambda r: r.pop("drift"),
            lambda r: r["drift"].pop("approval_token"),
            lambda r: r.__setitem__("prefix_digest", "nope"),
            lambda r: r["invocation"].__setitem__("owned_files", []),
        ):
            broken = json.loads(json.dumps(rep))
            mutate(broken)
            code, res = self._start(prior, broken, self.dispatch())
            if "source_note_text" not in broken:
                # not needed: the note is rebuilt from the validated records
                self.assertEqual((code, res["action"]), (0, "continue"), res)
                os.remove(self.state)
                continue
            self.assertEqual(
                (code, res["code"]), (rp.EXIT_STARTUP, "bad_reuse_report"), res
            )
            rc_, cus = self.persist(
                "custody",
                "--report",
                self.write_report(broken),
                "--owned-file",
                self.foo,
            )
            self.assertEqual((rc_, cus["code"]), (rp.EXIT_STARTUP, "bad_reuse_report"))

    def test_changed_manifest_dispatch_changes_the_observed_prefix(self) -> None:
        prior = self.make_prior(handoff=None)
        _rc, rep = self.preview(prior)
        mpath = os.path.join(self.root, "runs", prior, "manifest.json")
        with open(mpath, encoding="utf-8") as f:
            m = json.load(f)
        m["dispatch"]["target"] = f"{self.foo}:9"
        with open(mpath, "w", encoding="utf-8") as f:
            json.dump(m, f)
        rc_, cus = self.persist(
            "custody", "--report", self.write_report(rep), "--owned-file", self.foo
        )
        self.assertEqual((rc_, cus["code"]), (rp.EXIT_STARTUP, "prior_run_changed"))
        code, res = self._start(prior, rep, self.dispatch())
        self.assertEqual((code, res["code"]), (rp.EXIT_STARTUP, "prior_run_changed"))


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class ReviewRound2(_Env):
    """PR #206 review round 2: journal-order baseline merge; scope binding."""

    _start = ReviewRound1._start

    def _redispatched_prior(self) -> tuple[str, bytes, dict[str, Any]]:
        """handoff at #5 records revision A; a NEWER dispatch at #6 records the
        accepted revision B."""
        with open(self.foo, "rb") as f:
            rev_a = f.read()
        prior = self.make_prior(handoff=self.handoff())
        with open(self.foo, "wb") as f:
            f.write(rev_a + b"-- accepted revision for redispatch\n")
        d = self.dispatch()
        rs.op_append(self.root, prior, "dispatch", d)
        return prior, rev_a, d

    def test_newer_dispatch_baseline_wins_and_unchanged_revision_matches(
        self,
    ) -> None:
        prior, _rev_a, _d = self._redispatched_prior()
        _rc, rep = self.preview(prior)
        self.assertEqual(rep["action"], "preview", rep)
        self.assertEqual(rep["selection"]["dispatch_cite"], f"{prior}#6")
        self.assertEqual(rep["selection"]["baseline_origins"], {self.foo: f"{prior}#6"})
        self.assertEqual(rep["drift"]["result"], "match")
        rc_, cus = self.persist(
            "custody", "--report", self.write_report(rep), "--owned-file", self.foo
        )
        self.assertEqual((rc_, cus["result"]), (0, "match"), cus)

    def test_rollback_to_the_older_handoff_revision_is_drift(self) -> None:
        prior, rev_a, d = self._redispatched_prior()
        with open(self.foo, "wb") as f:
            f.write(rev_a)  # external rollback to the OLDER handoff's bytes
        _rc, rep = self.preview(prior)
        self.assertEqual(rep["selection"]["baseline_origins"], {self.foo: f"{prior}#6"})
        self.assertEqual(rep["drift"]["result"], "drift", rep["drift"])
        rc_, cus = self.persist(
            "custody", "--report", self.write_report(rep), "--owned-file", self.foo
        )
        self.assertEqual((rc_, cus["code"]), (rp.EXIT_STARTUP, "drift_unapproved"))
        # the older handoff's baseline alone would have matched — that is the hole
        _c, old, _e = rr._baseline_cmd(
            ["check", "--baseline", "-"],
            rr._canon(
                rs.op_load(self.root, prior)["events"][4]["payload"]["file_baseline"]
            ),
        )
        self.assertEqual(old["result"], "match")
        _c, new, _e = rr._baseline_cmd(
            ["check", "--baseline", "-"], rr._canon(d["file_baseline"])
        )
        self.assertEqual(new["result"], "drift")

    def test_older_records_fill_paths_a_newer_one_does_not_cover(self) -> None:
        # dispatch(manifest) covers Foo; a later worker handoff covers Foo only;
        # a still later dispatch covers Foo + Other → Other from #6, Foo from #6;
        # then a handoff covering Foo only at #7 → Foo from #7, Other stays #6
        prior = self.make_prior(handoff=self.handoff())
        other = os.path.join(self.project, "Other.txt")
        with open(other, "w", encoding="utf-8") as f:
            f.write("accepted\n")
        _c, both, _e = rr._baseline_cmd(["record", "--", self.foo, other], None)
        d = self.dispatch()
        d["owned_files"] = [self.foo, other]
        d["file_baseline"] = both
        rs.op_append(self.root, prior, "dispatch", d)
        rs.op_append(self.root, prior, "handoff", self.handoff())
        _rc, rep = self.preview(prior, owned=[self.foo, other])
        self.assertEqual(
            rep["selection"]["baseline_origins"],
            {self.foo: f"{prior}#7", other: f"{prior}#6"},
        )
        self.assertEqual(rep["drift"]["result"], "match")

    def test_scope_is_part_of_the_binding(self) -> None:
        prior = self.make_prior(
            handoff=self.handoff(
                status="stuck",
                blocker_kind="proof",
                blocker_class="arithmetic",
                blocker_signature="unchanged-proof-blocker",
                new_evidence_required_for_rerun="a new arithmetic lemma",
            )
        )
        _rc, rep = self.preview(prior)  # scope sorry
        d = self.dispatch(
            scope="file", prior_blocker="unchanged-proof-blocker", evidence_delta=[]
        )
        self.assertEqual(rc.validate_dispatch(d), [])
        code, res = self._start(prior, rep, d)
        self.assertEqual(
            (code, res["code"]), (rp.EXIT_STARTUP, "reuse_report_mismatch")
        )
        self.assertIn("scope", res["detail"])
        self.assertEqual(
            [
                r
                for r in os.listdir(os.path.join(self.root, "runs"))
                if rs.valid_run_id(r)
            ],
            [prior],
        )
        # the matching scope is the guarded path: same task, same blocker,
        # empty delta → rerun_forbidden, still nothing created
        d = self.dispatch(prior_blocker="unchanged-proof-blocker", evidence_delta=[])
        code, res = self._start(prior, rep, d)
        self.assertEqual((code, res["code"]), (rp.EXIT_STARTUP, "rerun_forbidden"))


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class SmokeFollowups(_Env):
    """Live-smoke follow-ups: previews need no invocation state; a handoff's
    citation-form failed_avenues are not repeated as text."""

    def test_reuse_and_custody_need_no_invocation_state(self) -> None:
        prior = self.make_prior(handoff=self.handoff())
        self.env.pop("LEAN4_RUN_PERSIST_STATE", None)
        rc_, rep = self.preview(prior)
        self.assertEqual((rc_, rep["action"]), (0, "preview"), rep)
        rc_, cus = self.persist(
            "custody", "--report", self.write_report(rep), "--owned-file", self.foo
        )
        self.assertEqual((rc_, cus["action"]), (0, "custody"), cus)
        self.assertFalse(os.path.exists(self.state))
        # start still requires it
        rc_, res = self.persist(
            "start", "--dispatch", "-", stdin=json.dumps(self.dispatch())
        )
        self.assertEqual((rc_, res["action"]), (rp.EXIT_USAGE, "usage"), res)

    def test_handoff_citations_of_listed_notes_are_not_repeated(self) -> None:
        prior = self.make_prior(handoff=None)
        h = self.handoff()
        h["failed_avenues"] = [f"{prior}#1", "prose: tried ring_nf; no progress"]
        rs.op_set_handoff(self.root, prior, h)
        _rc, rep = self.preview(prior)
        fa = rep["historical"]["failed_avenues"]
        self.assertEqual(
            fa,
            [
                {"text": "exact foo_lemma: type mismatch", "cite": f"{prior}#1"},
                {"text": "exact tendsto_atTop_mono h", "cite": f"{prior}#4"},  # Replan
                {"text": "prose: tried ring_nf; no progress", "cite": f"{prior}#5"},
            ],
        )


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class ReviewRound3(_Env):
    """PR #206 review round 3: start re-derives custody; Replan failed
    approaches and handoff candidates delivered; path-semantic targets."""

    def _start(
        self,
        prior: str,
        rep: dict[str, Any],
        d: dict[str, Any],
        approve: str | None = None,
    ) -> tuple[int, dict[str, Any]]:
        args = [
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            prior,
            "--reuse-report",
            self.write_report(rep),
            "--now",
            "2026-09-10T12:00:00Z",
        ]
        if approve is not None:
            args += ["--approve", approve]
        return self.persist(*args, stdin=json.dumps(d))

    def _drifted_prior(self) -> str:
        prior = self.make_prior(handoff=self.handoff())
        with open(self.foo, "a", encoding="utf-8") as f:
            f.write("-- external change\n")
        return prior

    # --- 1. start cannot bypass drift reconciliation

    def test_autonomous_start_cannot_bypass_drift_reconciliation(self) -> None:
        prior = self._drifted_prior()
        _rc, rep = self.preview(prior, mode="autoprove")
        self.assertEqual(rep["drift"]["result"], "drift")
        # custody deliberately skipped; dispatch() records the CURRENT bytes
        code, res = self._start(prior, rep, self.dispatch(mode="autoprove"))
        self.assertEqual(
            (code, res["action"], res["code"]),
            (rp.EXIT_STARTUP, "startup-error", "drift_unreconciled"),
            res,
        )
        # not even with a token: autonomous mode never accepts drift
        code, res = self._start(
            prior, rep, self.dispatch(mode="autoprove"), rep["drift"]["approval_token"]
        )
        self.assertEqual((code, res["code"]), (rp.EXIT_STARTUP, "drift_unreconciled"))
        self.assertEqual(
            [
                r
                for r in os.listdir(os.path.join(self.root, "runs"))
                if rs.valid_run_id(r)
            ],
            [prior],
        )
        self.assertFalse(os.path.exists(self.state))

    def test_guided_start_requires_the_token_and_the_fresh_baseline(self) -> None:
        prior = self._drifted_prior()
        _rc, rep = self.preview(prior)
        tok = rep["drift"]["approval_token"]
        code, res = self._start(prior, rep, self.dispatch())
        self.assertEqual((code, res["code"]), (rp.EXIT_STARTUP, "drift_unapproved"))
        code, res = self._start(prior, rep, self.dispatch(), "0" * 64)
        self.assertEqual((code, res["code"]), (rp.EXIT_STARTUP, "approval_mismatch"))
        # approved, but the dispatch carries the PRIOR baseline (pre-change bytes)
        stale = self.dispatch()
        stale["file_baseline"] = rr.select(rs.op_load(self.root, prior))["baseline"]
        code, res = self._start(prior, rep, stale, tok)
        self.assertEqual((code, res["code"]), (rp.EXIT_STARTUP, "baseline_mismatch"))
        # approved with the fresh baseline: the run starts and its source-note
        # records the reconciled drift
        code, res = self._start(prior, rep, self.dispatch(), tok)
        self.assertEqual((code, res["action"]), (0, "continue"), res)
        note = json.loads(
            rs.op_load(self.root, res["run_id"])["events"][0]["payload"]["text"]
        )
        self.assertEqual(note["drift"], {"result": "drift", "approval_token": tok})

    def test_start_refuses_a_file_changed_again_after_approval(self) -> None:
        prior = self._drifted_prior()
        _rc, rep = self.preview(prior)
        tok = rep["drift"]["approval_token"]
        with open(self.foo, "a", encoding="utf-8") as f:
            f.write("-- changed again\n")
        code, res = self._start(prior, rep, self.dispatch(), tok)
        self.assertEqual((code, res["code"]), (rp.EXIT_STARTUP, "custody_mismatch"))

    # --- 2. Replan failed approaches and handoff candidates reach the new run

    def test_replan_failed_approaches_and_handoff_candidates_are_delivered(
        self,
    ) -> None:
        h = self.handoff()
        h["best_candidates"] = [
            {
                "candidate": "UNIQUE_CANDIDATE: nlinarith [sq_nonneg x]",
                "outcome": "compiles but 8 s; not adopted",
            }
        ]
        prior = self.make_prior(handoff=h)  # the fixture Replan (#4) carries
        _rc, rep = self.preview(prior)  # "exact tendsto_atTop_mono h"
        hist = rep["historical"]
        self.assertIn(
            {"text": "exact tendsto_atTop_mono h", "cite": f"{prior}#4"},
            hist["failed_avenues"],
        )
        self.assertEqual(
            hist["candidates"],
            [
                {
                    "candidate": "UNIQUE_CANDIDATE: nlinarith [sq_nonneg x]",
                    "outcome": "compiles but 8 s; not adopted",
                    "cite": f"{prior}#5",
                    "verified": False,
                }
            ],
        )
        code, res = self._start(prior, rep, self.dispatch())
        self.assertEqual((code, res["action"]), (0, "continue"), res)
        text = rs.op_load(self.root, res["run_id"])["events"][0]["payload"]["text"]
        self.assertIn("exact tendsto_atTop_mono h", text)
        self.assertIn("UNIQUE_CANDIDATE: nlinarith [sq_nonneg x]", text)
        self.assertIn(
            "historical, unverified", json.loads(text)["presentation"]["candidates"]
        )

    # --- 3. target compatibility has path semantics

    def _compat(self, prior_target: str, target: str, scope: str) -> str | None:
        sel = {
            "dispatch": {"mode": "prove", "target": prior_target, "owned_files": []},
            "baseline_origins": {},
        }
        try:
            rr.check_compat(
                sel,
                target=target,
                scope=scope,
                mode="prove",
                project_root=self.project,
                owned_files=[self.foo],
            )
        except rr.ReuseError as ex:
            return ex.code
        return None

    def test_target_compatibility_uses_path_semantics(self) -> None:
        # intended widening: a line task reused for the whole file
        self.assertIsNone(self._compat("/repo/Foo.lean:42", "/repo/Foo.lean", "file"))
        self.assertIsNone(self._compat("/repo/Foo.lean:42", "/repo/Foo.lean:7", "file"))
        # neighbouring names are different files
        self.assertEqual(
            self._compat("/repo/Foo.lean.extra.lean:1", "/repo/Foo.lean", "file"),
            "incompatible_target",
        )
        # directory targets contain by whole components
        self.assertIsNone(self._compat("/repo/Foo/X.lean:1", "/repo/Foo", "project"))
        self.assertIsNone(self._compat("/repo/Foo/X.lean:1", "/repo/Foo/", "changed"))
        self.assertEqual(
            self._compat("/repo/Foobar/X.lean:1", "/repo/Foo", "project"),
            "incompatible_target",
        )
        # sorry scope: the identical target only
        self.assertEqual(
            self._compat("/repo/Foo.lean:42", "/repo/Foo.lean:43", "sorry"),
            "incompatible_target",
        )
        # only a trailing :<line> is a location suffix
        self.assertEqual(
            rr._target_path("C:/repo/Foo.lean:3"), rr._target_path("C:/repo/Foo.lean")
        )


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class ReviewRound4(_Env):
    """PR #206 review round 4: the dispatch/custody baseline comparison keeps
    resolved-path identity (a symlink retargeted to identical bytes)."""

    _start = ReviewRound3._start

    def setUp(self) -> None:
        super().setUp()
        # Foo.lean becomes a symlink to A; B has identical bytes
        with open(self.foo, "rb") as f:
            data = f.read()
        self.a = os.path.join(self.project, "A.lean")
        self.b = os.path.join(self.project, "B.lean")
        for p in (self.a, self.b):
            with open(p, "wb") as f:
                f.write(data)
        os.remove(self.foo)
        os.symlink(self.a, self.foo)

    def _retarget(self, to: str) -> None:
        os.remove(self.foo)
        os.symlink(to, self.foo)

    def test_stale_entry_with_identical_bytes_but_other_realpath_is_refused(
        self,
    ) -> None:
        prior = self.make_prior(handoff=self.handoff())  # baseline records A
        stale = self.dispatch()  # its baseline still names A
        self._retarget(self.b)
        _rc, rep = self.preview(prior)
        self.assertEqual(rep["drift"]["entries"][0]["status"], "retargeted")
        tok = rep["drift"]["approval_token"]
        # the user approves B; the dispatch mistakenly keeps the entry naming A
        self.assertEqual(
            stale["file_baseline"]["files"][0]["realpath"], os.path.realpath(self.a)
        )
        code, res = self._start(prior, rep, stale, tok)
        self.assertEqual((code, res["code"]), (rp.EXIT_STARTUP, "baseline_mismatch"))
        self.assertEqual(
            [
                r
                for r in os.listdir(os.path.join(self.root, "runs"))
                if rs.valid_run_id(r)
            ],
            [prior],
        )
        self.assertFalse(os.path.exists(self.state))
        # the ACTUAL fresh baseline (naming B) starts the run ...
        fresh = self.dispatch()
        self.assertEqual(
            fresh["file_baseline"]["files"][0]["realpath"], os.path.realpath(self.b)
        )
        code, res = self._start(prior, rep, fresh, tok)
        self.assertEqual((code, res["action"]), (0, "continue"), res)
        # ... and a later retarget back to A is detected against it
        self._retarget(self.a)
        _c, chk, _e = rr._baseline_cmd(
            ["check", "--baseline", "-"], rr._canon(fresh["file_baseline"])
        )
        self.assertEqual(
            (chk["result"], chk["entries"][0]["status"]), ("drift", "retargeted")
        )
        _c, stale_chk, _e = rr._baseline_cmd(
            ["check", "--baseline", "-"], rr._canon(stale["file_baseline"])
        )
        self.assertEqual(stale_chk["result"], "match")  # what the bug would have hidden

    def test_baseline_digest_is_order_independent_and_identity_complete(self) -> None:
        e1 = {
            "path": "/p/a",
            "realpath": "/r/a",
            "exists": True,
            "sha256": "x",
            "size": 1,
        }
        e2 = {
            "path": "/p/b",
            "realpath": "/r/b",
            "exists": True,
            "sha256": "y",
            "size": 2,
        }
        base = {"schema": "file-baseline/v1", "files": [e1, e2]}
        swapped = {"schema": "file-baseline/v1", "files": [e2, e1]}
        self.assertEqual(rr.baseline_digest(base), rr.baseline_digest(swapped))
        for k, v in (
            ("realpath", "/r/z"),
            ("size", 9),
            ("exists", False),
            ("sha256", "q"),
        ):
            other = {"schema": "file-baseline/v1", "files": [dict(e1, **{k: v}), e2]}
            self.assertNotEqual(rr.baseline_digest(base), rr.baseline_digest(other), k)
        self.assertIsNone(rr.baseline_digest({"files": [{"nope": 1}]}))


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class ChainedReuse(_Env):
    """PR #206 review round 5: successive reuses A → B → C → … must not nest
    serialized history; the earliest evidence survives with its citation."""

    GENERATIONS = 12

    def _finish(self) -> None:
        rc_, fin = self.persist(
            "finish", "--payload", "-", stdin=json.dumps(self.handoff())
        )
        self.assertEqual((rc_, fin["stored"]), (0, True), fin)

    def _reuse_once(self, prior: str, gen: int) -> tuple[str, str]:
        """A fresh invocation reusing `prior`; returns (run_id, source-note text)."""
        self.state = os.path.join(self.tmp, f"state-{gen}.json")
        self.env["LEAN4_RUN_PERSIST_STATE"] = self.state
        rc_, rep = self.preview(prior)
        self.assertEqual((rc_, rep["action"]), (0, "preview"), rep)
        self.assertEqual(rep["drift"]["result"], "match")
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--prior-run",
            prior,
            "--reuse-report",
            self.write_report(rep),
            "--now",
            f"2026-09-{10 + gen:02d}T12:00:00Z",
            stdin=json.dumps(self.dispatch()),
        )
        self.assertEqual((rc_, res["action"]), (0, "continue"), res)
        self._finish()
        text = str(rs.op_load(self.root, res["run_id"])["events"][0]["payload"]["text"])
        return str(res["run_id"]), text

    def test_chained_reuse_is_flat_and_keeps_the_earliest_evidence(self) -> None:
        a = self.make_prior(handoff=self.handoff())  # one failed-avenue note at #1
        sizes: list[int] = []
        prior = a
        last = ""
        for gen in range(1, self.GENERATIONS + 1):
            prior, last = self._reuse_once(prior, gen)
            sizes.append(len(last))
            self.assertLess(last.count("\\\\"), 10, f"gen {gen}: nested escaping")
        # linear, not exponential: every generation adds about one link record
        increments = [b - a_ for a_, b in pairwise(sizes)]
        self.assertLess(max(increments), 3 * min(increments) + 200, sizes)
        self.assertLess(sizes[-1], 4 * sizes[0] + 20 * self.GENERATIONS * 60, sizes)
        note = json.loads(last)
        hist = note["historical"]
        # the earliest substantive evidence and its ORIGINAL citation survive
        first = [f for f in hist["failed_avenues"] if f["cite"] == f"{a}#1"]
        self.assertEqual(first[0]["text"], "exact foo_lemma: type mismatch")
        self.assertIn("inherited_via", first[0])
        # one flattened link per earlier reuse, oldest included, none nested
        self.assertEqual(len(hist["inherited"]), self.GENERATIONS - 1)
        oldest = hist["inherited"][-1]
        self.assertEqual(oldest["prior_run"], a)
        # A's next steps and Replan blocker survive in the oldest link, as
        # HISTORICAL data — the current carry is B's own, not an ancestor's
        self.assertEqual(oldest["next_steps"], ["try Tendsto.comp"])
        self.assertEqual(oldest["plan_cite"], f"{a}#4")
        self.assertEqual(
            oldest["carry"]["replan_blockers"][0]["blocker_signature"], "replan-sig"
        )
        self.assertEqual(note["carry"]["replan_blockers"], [])
        self.assertIsNone(note["carry"]["prior_blocker"])
        self.assertNotIn("historical", json.dumps(hist["inherited"]))
        self.assertFalse(
            any(n["kind"] == "source-note" for n in hist["notes"]),
            "a reuse note must not be carried as text",
        )
        self.assertIn(
            "nothing inherited is current certification",
            note["presentation"]["inherited"],
        )
        # a USER-written source-note stays ordinary text
        rs.op_append(
            self.root,
            prior,
            "note",
            {
                "kind": "source-note",
                "text": "see Mathlib PR #1234 for the lemma",
                "lean": None,
            },
        )
        _rc, rep = self.preview(prior)
        self.assertIn(
            "see Mathlib PR #1234 for the lemma",
            [
                n["text"]
                for n in rep["historical"]["notes"]
                if n["kind"] == "source-note"
            ],
        )


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class JsonShapedUserNotes(_Env):
    """PR #206 review round 6: only a helper-generated reuse note (explicit
    schema, valid shape) is flattened; JSON-shaped user notes stay text."""

    def _note_and_preview(self, text: str) -> tuple[dict[str, Any], list[str]]:
        prior = self.make_prior(handoff=self.handoff())
        rs.op_append(
            self.root,
            prior,
            "note",
            {"kind": "source-note", "text": text, "lean": None},
        )
        rc_, rep = self.preview(prior)
        self.assertEqual((rc_, rep["action"]), (0, "preview"), rep)
        texts = [
            n["text"] for n in rep["historical"]["notes"] if n["kind"] == "source-note"
        ]
        return rep, texts

    def test_json_shaped_user_notes_stay_ordinary_text(self) -> None:
        rid = "20260101T000000Z-0badc0de"
        for text in (
            json.dumps(
                {
                    "prior_run": rid,
                    "prefix_digest": "x",
                    "presentation": {},
                    "historical": {"notes": None},
                }
            ),
            json.dumps(
                {
                    "prior_run": rid,
                    "prefix_digest": "x",
                    "presentation": {},
                    "historical": {},
                }
            ),
            json.dumps(
                {
                    "schema": "run-persist-source-note/v1",
                    "prior_run": "not-a-run-id",
                    "historical": {},
                }
            ),
            json.dumps(
                {
                    "schema": "run-persist-source-note/v1",
                    "prior_run": rid,
                    "historical": {"failed_avenues": "nope"},
                }
            ),
            json.dumps(
                {
                    "schema": "run-persist-source-note/v1",
                    "prior_run": rid,
                    "historical": {"notes": [1, 2]},
                }
            ),
            json.dumps(
                {
                    "schema": "run-persist-source-note/v1",
                    "prior_run": rid,
                    "historical": {},
                    "carry": "x",
                }
            ),
            "{not json",
            "see Mathlib PR #1234 for the lemma",
        ):
            rep, texts = self._note_and_preview(text)
            self.assertEqual(texts, [text])  # kept verbatim, never discarded
            self.assertEqual(rep["historical"]["inherited"], [])
            shutil.rmtree(self.root)

    def test_only_the_helper_schema_is_flattened(self) -> None:
        rid = "20260101T000000Z-0badc0de"
        text = json.dumps(
            {
                "schema": "run-persist-source-note/v1",
                "prior_run": rid,
                "prefix_digest": "d" * 64,
                "historical": {
                    "plan": "ancestor plan",
                    "next_steps": ["ancestor step"],
                    "failed_avenues": [
                        {"text": "ANCESTOR_DEAD_END", "cite": f"{rid}#1"}
                    ],
                },
                "carry": {"prior_blocker": "ancestor-blocker", "replan_blockers": []},
            }
        )
        rep, texts = self._note_and_preview(text)
        self.assertEqual(texts, [])
        link = rep["historical"]["inherited"][0]
        self.assertEqual(
            (link["prior_run"], link["next_steps"]), (rid, ["ancestor step"])
        )
        self.assertEqual(link["carry"]["prior_blocker"], "ancestor-blocker")
        self.assertIn(
            {
                "text": "ANCESTOR_DEAD_END",
                "cite": f"{rid}#1",
                "inherited_via": link["cite"],
            },
            rep["historical"]["failed_avenues"],
        )
        # historical only: the current carry is the selected handoff's
        self.assertNotEqual(rep["carry"]["prior_blocker"], "ancestor-blocker")


if __name__ == "__main__":
    unittest.main()
