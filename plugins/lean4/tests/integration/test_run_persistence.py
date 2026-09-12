"""#82B acceptance: the proving commands' persistence protocol, end to end.

The LLM-driven parts of prove/autoprove are prose; what CAN be executed is the
protocol that prose prescribes (references/cycle-engine.md § Run Persistence):
start → notes → review → replan → tick → dispatch/handoff → review → replan →
tick → finish, through the real `lean4-skills-run-persist` helper, the real
`lean4-skills-run-store` and the real `lean4-skills-cycle-tracker`. Check 44
binds the prose to this protocol; this file establishes the wiring works.

Failure-path cases drive the helper against a FAKE store CLI that returns
chosen outcomes, so the policy (journal_only → no re-append; indeterminate →
stop; refusal → stop; busy → one retry; final-handoff failure → visible
fallback, never claimed stored) is exercised deterministically.

Stdlib only; POSIX (the store's mutation hosts). Windows runs the
startup-refusal case only.
"""

from __future__ import annotations

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
import run_persistence as rp  # noqa: E402
import run_store as rs  # noqa: E402
from test_run_contract import valid_dispatch, valid_handoff  # noqa: E402

PERSIST = os.path.join(_PLUGIN, "bin", "lean4-skills-run-persist")
TRACKER = os.path.join(_PLUGIN, "bin", "lean4-skills-cycle-tracker")
POSIX = rs.platform_supported()
NOW = "2026-09-09T12:00:00Z"


def _review_output() -> dict[str, Any]:
    return {
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
    }


def _triage() -> dict[str, Any]:
    return {
        "blocker_class": "missing-library-lemma",
        "blocker_kind": "proof",
        "blocker_signature": "Foo.lean:42:unknown identifier",
        "next_action": "continue",
        "statement_may_be_false": False,
        "evidence": {
            "queries": ["tendsto atTop of monotone"],
            "top_candidates": ["tendsto_atTop_mono"],
            "attempts": [
                {"snippet": "exact tendsto_atTop_mono h", "result": "type mismatch"}
            ],
            "goal_delta": None,
            "diagnostic_delta": None,
        },
    }


def _review(cycle: int, **over: Any) -> dict[str, Any]:
    r: dict[str, Any] = {
        "schema": rs.REVIEW_RECORD_SCHEMA,
        "cycle": cycle,
        "mode": "batch",
        "target": "/repo/Foo.lean",
        "scope": "file",
        "line": None,
        "source": "internal",
        "status": "completed",
        "output": _review_output(),
        "triage": None,
        "mapped_handoff": None,
        "detail": None,
    }
    r.update(over)
    return r


def _stuck_review(cycle: int) -> dict[str, Any]:
    return _review(
        cycle,
        mode="stuck",
        scope="sorry",
        line=42,
        output=None,
        triage=_triage(),
        mapped_handoff=valid_handoff(
            status="stuck",
            blocker_kind="proof",
            blocker_class="missing-library-lemma",
            blocker_signature="Foo.lean:42:unknown identifier",
            new_evidence_required_for_rerun="a tendsto lemma for monotone sequences",
        ),
    )


def _replan(cycle: int, cites: list[str]) -> dict[str, Any]:
    return {
        "schema": rs.REPLAN_SUMMARY_SCHEMA,
        "cycle": cycle,
        "plan": f"cycle {cycle}: search Topology/Order for tendsto variants",
        "failed_approaches": ["exact tendsto_atTop_mono h"],
        "blockers": [
            {
                "file": "/repo/Foo.lean",
                "line": 42,
                "blocker_class": "missing-library-lemma",
                "blocker_signature": "Foo.lean:42:unknown identifier",
            }
        ],
        "next_steps": ["try Tendsto.comp"],
        "cites": cites,
    }


class _Env(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="run-persist-")
        self.project = os.path.join(self.tmp, "proj")
        os.makedirs(self.project)
        self.root = os.path.join(self.project, ".lean4-skills")
        self.state = os.path.join(self.tmp, "persist-state.json")
        self.env = dict(
            os.environ,
            LEAN4_RUN_PERSIST_STATE=self.state,
            TMPDIR=self.tmp,
            LEAN4_SESSION_DIR=self.tmp,
        )
        self.env.pop("LEAN4_RUN_STORE", None)
        self.env.pop("LEAN4_SESSION_ID", None)

    def tearDown(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    def persist(
        self, *args: str, stdin: str | None = None
    ) -> tuple[int, dict[str, Any]]:
        p = subprocess.run(
            [PERSIST, "--root", self.root, "--project-root", self.project, *args],
            input=stdin,
            capture_output=True,
            text=True,
            env=self.env,
            check=False,
        )
        self.assertTrue(p.stdout.strip(), p.stderr)
        return p.returncode, json.loads(p.stdout)

    def tracker(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [TRACKER, *args], capture_output=True, text=True, env=self.env, check=False
        )


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class TwoCycleRun(_Env):
    """The happy path: a two-cycle run through the real helper, store and tracker."""

    def test_two_cycles_then_load(self) -> None:
        init = self.tracker(
            "init",
            "--max-cycles=5",
            "--max-stuck=3",
            "--max-runtime=10m",
            "--max-deep-per-cycle=1",
            "--max-consecutive-deep=2",
        )
        self.assertEqual(init.returncode, 0, init.stderr)
        session_id = init.stdout.strip().splitlines()[-1]
        self.env["LEAN4_SESSION_ID"] = session_id

        # startup: after inputs + capability checks + a valid first dispatch
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--tracker-session-id",
            session_id,
            "--now",
            NOW,
            stdin=json.dumps(valid_dispatch()),
        )
        self.assertEqual((rc_, res["action"]), (0, "continue"), res)
        rid = res["run_id"]

        # cycle 1
        rc_, n1 = self.persist(
            "note",
            "--kind",
            "failed-avenue",
            "--text",
            "exact tendsto_atTop_mono h: type mismatch",
        )
        self.assertEqual((rc_, n1["action"], n1["seq"]), (0, "continue", 1))
        rc_, r1 = self.persist("review", "--payload", "-", stdin=json.dumps(_review(1)))
        self.assertEqual((rc_, r1["seq"]), (0, 2))
        rc_, p1 = self.persist(
            "replan",
            "--payload",
            "-",
            stdin=json.dumps(_replan(1, [n1["cite"], r1["cite"]])),
        )
        self.assertEqual((rc_, p1["seq"]), (0, 3))
        tick = self.tracker("tick", "--stuck=no")
        self.assertEqual(tick.returncode, 0, tick.stderr)

        # cycle 2: a redispatch, a worker handoff, a stuck review, a replan
        d2 = valid_dispatch(
            prior_blocker="Foo.lean:42:unknown identifier", evidence_delta=[r1["cite"]]
        )
        rc_, ev = self.persist("dispatch", "--payload", "-", stdin=json.dumps(d2))
        self.assertEqual((rc_, ev["seq"]), (0, 4))
        rc_, ev = self.persist(
            "handoff", "--payload", "-", stdin=json.dumps(valid_handoff())
        )
        self.assertEqual((rc_, ev["seq"]), (0, 5))
        rc_, r2 = self.persist(
            "review", "--payload", "-", stdin=json.dumps(_stuck_review(2))
        )
        self.assertEqual((rc_, r2["seq"]), (0, 6))
        rc_, p2 = self.persist(
            "replan",
            "--payload",
            "-",
            stdin=json.dumps(_replan(2, [r2["cite"], p1["cite"]])),
        )
        self.assertEqual((rc_, p2["seq"]), (0, 7))
        tick = self.tracker("tick", "--stuck=yes")
        self.assertEqual(tick.returncode, 0, tick.stderr)

        # stop: the final handoff cites stored items
        final = valid_handoff(failed_avenues=[n1["cite"], "exact tendsto_atTop_mono h"])
        final["evidence"]["top_candidates"] = [r2["cite"]]
        rc_, done = self.persist("finish", "--payload", "-", stdin=json.dumps(final))
        self.assertEqual(
            (rc_, done["action"], done["stored"], done["seq"]),
            (0, "done", True, 8),
            done,
        )
        self.tracker("stop")

        # what a later session finds
        out = rs.op_load(self.root, rid)
        self.assertEqual(out["event_schema"], rs.EVENT_SCHEMA_V2)
        self.assertEqual(out["manifest"]["tracker_session_id"], session_id)
        self.assertEqual(out["manifest"]["dispatch"], valid_dispatch())
        self.assertEqual(
            [e["kind"] for e in out["events"]],
            [
                "note",
                "review",
                "replan",
                "dispatch",
                "handoff",
                "review",
                "replan",
                "handoff",
            ],
        )
        reviews = [e for e in out["events"] if e["kind"] == "review"]
        self.assertEqual([r["payload"]["mode"] for r in reviews], ["batch", "stuck"])
        self.assertIsNotNone(reviews[1]["payload"]["triage"])
        self.assertIsNotNone(reviews[1]["payload"]["mapped_handoff"])
        replans = [e for e in out["events"] if e["kind"] == "replan"]
        self.assertEqual([r["payload"]["cycle"] for r in replans], [1, 2])
        self.assertEqual(out["effective_handoff"]["payload"], final)
        self.assertEqual(out["handoff_cache"], "current")
        self.assertEqual(out["warnings"], [])
        # every citation resolves to an EARLIER stored event of this run
        by_seq = {e["seq"]: e for e in out["events"]}
        for cite in (
            replans[1]["payload"]["cites"] + final["evidence"]["top_candidates"]
        ):
            run, seq = cite.split("#")
            self.assertEqual(run, rid)
            self.assertIn(int(seq), by_seq)
            self.assertLess(int(seq), 8)


class PersistenceOff(_Env):
    def test_off_means_no_storage_activity(self) -> None:
        # With persistence off the command never invokes the helper; the only
        # thing to establish is that neither configuration source creates
        # anything by itself — the store is only ever touched by an explicit
        # start. Simulate a full command run that never calls `start`.
        env = dict(self.env, LEAN4_RUN_STORE=os.path.join(self.tmp, "elsewhere"))
        p = subprocess.run(
            [PERSIST, "status"], capture_output=True, text=True, env=env, check=False
        )
        self.assertEqual(
            p.returncode, rp.EXIT_USAGE
        )  # no state → nothing was ever started
        self.assertFalse(os.path.exists(self.root))
        self.assertFalse(os.path.exists(os.path.join(self.tmp, "elsewhere")))


class UnsupportedPlatform(_Env):
    def test_start_refuses_before_any_proof_edit(self) -> None:
        saved = rs.platform_supported
        # the helper spawns the real store; force the refusal through the store CLI
        fake = os.path.join(self.tmp, "fake_store.py")
        with open(fake, "w", encoding="utf-8") as f:
            f.write(
                "import json,sys\n"
                "print(json.dumps({'schema':'run-store-result/v1','outcome':'nothing_written',"
                "'code':'unsupported_platform','detail':'run-store mutations need a POSIX host'}))\n"
                "sys.exit(3)\n"
            )
        rp._STORE_ARGV = [sys.executable, fake]
        try:
            import io

            buf = io.TextIOWrapper(io.BytesIO(), encoding="utf-8")
            sys_stdout = sys.stdout
            sys.stdout = buf
            try:
                with open(os.path.join(self.tmp, "d.json"), "w") as f:
                    json.dump(valid_dispatch(), f)
                rc_ = rp.main(
                    [
                        "--root",
                        self.root,
                        "--state",
                        self.state,
                        "start",
                        "--dispatch",
                        os.path.join(self.tmp, "d.json"),
                    ]
                )
            finally:
                sys.stdout = sys_stdout
            buf.flush()
            res = json.loads(buf.buffer.getvalue().decode("utf-8"))
        finally:
            rp._STORE_ARGV = None
            rs.platform_supported = saved
        self.assertEqual(rc_, rp.EXIT_STARTUP)
        self.assertEqual(
            (res["action"], res["code"]), ("startup-error", "unsupported_platform")
        )
        self.assertFalse(os.path.exists(self.state))
        self.assertFalse(os.path.exists(self.root))


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class FailurePolicy(_Env):
    """Each store outcome, injected through a fake store CLI, and what the
    helper tells the command to do."""

    def _fake_store(self, script: str) -> str:
        fake = os.path.join(self.tmp, "fake_store.py")
        with open(fake, "w", encoding="utf-8") as f:
            f.write("import json, os, sys\nargs = sys.argv[1:]\n" + script)
        return fake

    def _run(
        self, fake: str | None, argv: list[str], stdin: str | None = None
    ) -> tuple[int, dict[str, Any]]:
        env = dict(self.env)
        if fake:
            env["LEAN4_RUN_STORE_ARGV"] = json.dumps([sys.executable, fake])
        p = subprocess.run(
            [PERSIST, "--root", self.root, "--project-root", self.project, *argv],
            input=stdin,
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        self.assertTrue(p.stdout.strip(), p.stderr)
        return p.returncode, json.loads(p.stdout)

    def _started(self) -> str:
        rc_, res = self._run(
            None,
            ["start", "--dispatch", "-", "--now", NOW],
            json.dumps(valid_dispatch()),
        )
        self.assertEqual(rc_, 0, res)
        return str(res["run_id"])

    def _events(self, rid: str) -> list[dict[str, Any]]:
        return list(rs.op_load(self.root, rid)["events"])

    def test_refusal_before_replan_stops_the_run_no_next_cycle(self) -> None:
        rid = self._started()
        fake = self._fake_store(
            "print(json.dumps({'schema':'run-store-result/v1','outcome':'nothing_written','code':'journal_damaged','detail':'truncated_tail@line 3'})); sys.exit(3)\n"
        )
        rc_, res = self._run(
            fake, ["replan", "--payload", "-"], json.dumps(_replan(1, []))
        )
        self.assertEqual((rc_, res["action"]), (rp.EXIT_STOP, "stop"))
        self.assertEqual(res["handoff"]["stop_reason"], "operational-error")
        self.assertIn("journal_damaged", res["handoff"]["stop_detail"])
        # every later mutation is refused by the helper WITHOUT touching the store
        rc_, res2 = self._run(None, ["note", "--kind", "candidate", "--text", "x"])
        self.assertEqual((rc_, res2["action"]), (rp.EXIT_STOP, "stop"))
        self.assertEqual(self._events(rid), [])  # nothing reached the real journal

    def test_journal_only_continues_without_duplicate(self) -> None:
        rid = self._started()
        # the REAL store, with the cache rename failing: journal_only on finish
        real = os.path.join(_LIB, "run_store.py")
        fake = self._fake_store(
            "import runpy\n"  # noqa: UP031
            "sys.path.insert(0, %r)\n"
            "import run_store as rs\n"
            "def bad_rename(*a, **k): raise OSError(5, 'injected rename failure')\n"
            "rs._rename = bad_rename\n"
            "sys.exit(rs.main(args))\n" % _LIB
        )
        rc_, res = self._run(
            fake, ["finish", "--payload", "-"], json.dumps(valid_handoff())
        )
        self.assertEqual(
            (rc_, res["action"], res["stored"], res["seq"]), (0, "done", True, 1), res
        )
        self.assertIn("handoff cache not confirmed", res["warning"])
        events = self._events(rid)
        self.assertEqual(len(events), 1)  # exactly one handoff event, never re-appended
        self.assertEqual(rs.op_load(self.root, rid)["handoff_cache"], "stale")
        self.assertTrue(os.path.exists(real))

    def test_visible_but_unsynced_event_stops_not_continues(self) -> None:
        rid = self._started()
        fake = self._fake_store(
            "sys.path.insert(0, %r)\n"  # noqa: UP031
            "import run_store as rs\n"
            "def bad_fsync(fd):\n"
            "    import os as _os\n"
            "    if not _os.path.isdir('/proc/self/fd/%%d' %% fd) and 'events' in _os.readlink('/proc/self/fd/%%d' %% fd): raise OSError(5, 'injected journal fsync failure')\n"
            "    _os.fsync(fd)\n"
            "rs._fsync = bad_fsync\n"
            "sys.exit(rs.main(args))\n" % _LIB
        )
        rc_, res = self._run(
            fake, ["note", "--kind", "candidate", "--text", "try simp"]
        )
        self.assertEqual(
            (rc_, res["action"], res["outcome"]),
            (rp.EXIT_STOP, "stop", "indeterminate"),
            res,
        )
        # the line IS visible in the observed prefix — and that is not commitment
        self.assertEqual(len(self._events(rid)), 1)
        rc_, res2 = self._run(None, ["note", "--kind", "candidate", "--text", "again"])
        self.assertEqual(res2["action"], "stop")
        self.assertEqual(len(self._events(rid)), 1)  # no duplicate, no continuation

    def test_busy_retries_once_then_continues(self) -> None:
        rid = self._started()
        marker = os.path.join(self.tmp, "busy-once")
        fake = self._fake_store(
            "sys.path.insert(0, %r)\n"  # noqa: UP031
            "import run_store as rs\n"
            "if not os.path.exists(%r):\n"
            "    open(%r, 'w').close()\n"
            "    print(json.dumps({'schema':'run-store-result/v1','outcome':'nothing_written','code':'busy','detail':'another store process holds .lock'})); sys.exit(3)\n"
            "sys.exit(rs.main(args))\n" % (_LIB, marker, marker)
        )
        rc_, res = self._run(
            fake, ["note", "--kind", "candidate", "--text", "try simp"]
        )
        self.assertEqual((rc_, res["action"], res["seq"]), (0, "continue", 1), res)
        self.assertEqual(len(self._events(rid)), 1)

    def test_final_handoff_failure_is_a_visible_fallback_never_claimed_stored(
        self,
    ) -> None:
        rid = self._started()
        fake = self._fake_store(
            "print(json.dumps({'schema':'run-store-result/v1','outcome':'nothing_written','code':'publish_unsynced','detail':'fsync failed'})); sys.exit(3)\n"
        )
        final = valid_handoff()
        rc_, res = self._run(fake, ["finish", "--payload", "-"], json.dumps(final))
        self.assertEqual(
            (rc_, res["action"], res["stored"]), (rp.EXIT_STOP, "done", False), res
        )
        self.assertEqual(res["fallback_handoff"], final)
        self.assertNotIn("cite", res)
        self.assertNotIn("seq", res)
        self.assertEqual(self._events(rid), [])

    def test_no_result_from_store_stops(self) -> None:
        self._started()
        fake = self._fake_store("sys.exit(1)\n")
        rc_, res = self._run(fake, ["note", "--kind", "candidate", "--text", "x"])
        self.assertEqual(
            (rc_, res["action"], res["outcome"]), (rp.EXIT_STOP, "stop", "no_result")
        )


if __name__ == "__main__":
    unittest.main()
