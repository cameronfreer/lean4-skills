# ruff: noqa: UP031  (fake-store scripts use %-formatting: they contain literal braces)
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
import run_contract_validate as rc  # noqa: E402
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
    mapped = valid_handoff(
        status="stuck",
        blocker_kind="proof",
        blocker_class="missing-library-lemma",
        blocker_signature="Foo.lean:42:unknown identifier",
        new_evidence_required_for_rerun="a tendsto lemma for monotone sequences",
    )
    # the mapped handoff wraps THIS triage of THIS target (cross-field rules)
    mapped["next_action"] = _triage()["next_action"]
    return _review(
        cycle,
        mode="stuck",
        target=mapped["target"],
        scope="sorry",
        line=42,
        output=None,
        triage=_triage(),
        mapped_handoff=mapped,
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
            "import runpy\n"
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
            "sys.path.insert(0, %r)\n"
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
            "sys.path.insert(0, %r)\n"
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
            (rc_, res["action"], res["outcome"]), (rp.EXIT_STOP, "stop", "malformed")
        )


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class ControlState(_Env):
    """Review round 1: the state file is control state. Bookkeeping failures
    never suppress the store's outcome and never let the run continue."""

    def _started(self) -> str:
        rc_, res = self.persist(
            "start", "--dispatch", "-", "--now", NOW, stdin=json.dumps(valid_dispatch())
        )
        self.assertEqual(rc_, 0, res)
        return str(res["run_id"])

    def _events(self, rid: str) -> list[dict[str, Any]]:
        return list(rs.op_load(self.root, rid)["events"])

    def _fake_store(self, script: str) -> dict[str, str]:
        fake = os.path.join(self.tmp, "fake_store.py")
        with open(fake, "w", encoding="utf-8") as f:
            f.write("import json, os, sys\nargs = sys.argv[1:]\n" + script)
        return {"LEAN4_RUN_STORE_ARGV": json.dumps([sys.executable, fake])}

    def _run(
        self, env_extra: dict[str, str], argv: list[str], stdin: str | None = None
    ) -> tuple[int, dict[str, Any]]:
        env = dict(self.env, **env_extra)
        p = subprocess.run(
            [PERSIST, "--project-root", self.project, *argv],
            input=stdin,
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        self.assertTrue(p.stdout.strip(), p.stderr)
        return p.returncode, json.loads(p.stdout)

    def test_state_save_failure_after_indeterminate_keeps_the_stop(self) -> None:
        rid = self._started()
        # make the state file's directory unwritable AFTER the in-flight record
        # is written: the store runs, returns indeterminate, and the helper
        # cannot record the stop
        state_dir = os.path.join(self.tmp, "st")
        os.makedirs(state_dir)
        state = os.path.join(state_dir, "state.json")
        shutil.move(self.state, state)
        self.env["LEAN4_RUN_PERSIST_STATE"] = state
        with open(state, encoding="utf-8") as f:
            before = json.load(f)
        # the in-flight record must be written first; then the directory is
        # frozen so the resolution cannot be — simulate with a wrapper store
        # that freezes the directory before returning
        script = (
            "sys.path.insert(0, %r)\n"
            "import run_store as rs, stat\n"
            "def bad_fsync(fd):\n"
            "    import os as _os\n"
            "    if 'events' in _os.readlink('/proc/self/fd/%%d' %% fd): raise OSError(5, 'injected journal fsync failure')\n"
            "    _os.fsync(fd)\n"
            "rs._fsync = bad_fsync\n"
            "os.chmod(%r, 0o500)\n"
            "sys.exit(rs.main(args))\n" % (_LIB, state_dir)
        )
        env = self._fake_store(script)
        try:
            rc_, res = self._run(
                env, ["note", "--kind", "candidate", "--text", "try simp"]
            )
            # the store's outcome is reported, with the handoff, despite the failed bookkeeping
            self.assertEqual(
                (rc_, res["action"], res["outcome"]),
                (rp.EXIT_STOP, "stop", "indeterminate"),
                res,
            )
            self.assertEqual(res["handoff"]["stop_reason"], "operational-error")
            self.assertIn("invocation state could not be updated", res["warning"])
        finally:
            os.chmod(state_dir, 0o700)
        # the state still carries the unresolved in-flight record, not stopped
        with open(state, encoding="utf-8") as f:
            st = json.load(f)
        self.assertIsNone(st["stopped"])
        self.assertIsNotNone(st["inflight"])
        self.assertEqual(st["run_id"], before["run_id"])
        # ... so the NEXT call stops without touching the store
        n_before = len(self._events(rid))
        rc_, res2 = self._run({}, ["note", "--kind", "candidate", "--text", "again"])
        self.assertEqual(
            (rc_, res2["action"], res2["outcome"]),
            (rp.EXIT_STOP, "stop", "terminal"),
            res2,
        )
        self.assertIn("left unresolved", res2["detail"])
        self.assertEqual(len(self._events(rid)), n_before)
        rc_, res3 = self._run(
            {}, ["finish", "--payload", "-"], json.dumps(valid_handoff())
        )
        self.assertEqual((rc_, res3["stored"]), (rp.EXIT_STOP, False))

    def test_state_unwritable_before_the_store_is_a_stop_with_nothing_attempted(
        self,
    ) -> None:
        rid = self._started()
        state_dir = os.path.join(self.tmp, "st2")
        os.makedirs(state_dir)
        state = os.path.join(state_dir, "state.json")
        shutil.move(self.state, state)
        self.env["LEAN4_RUN_PERSIST_STATE"] = state
        os.chmod(state_dir, 0o500)
        try:
            rc_, res = self._run({}, ["note", "--kind", "candidate", "--text", "x"])
        finally:
            os.chmod(state_dir, 0o700)
        self.assertEqual(
            (rc_, res["action"], res["outcome"]),
            (rp.EXIT_STOP, "stop", "state_unwritable"),
        )
        self.assertEqual(self._events(rid), [])

    def test_start_refuses_an_existing_state_file(self) -> None:
        self._started()
        rc_, res = self.persist(
            "start",
            "--dispatch",
            "-",
            "--now",
            "2026-09-09T13:00:00Z",
            stdin=json.dumps(valid_dispatch()),
        )
        self.assertEqual(
            (rc_, res["action"], res["code"]),
            (rp.EXIT_STARTUP, "startup-error", "state_exists"),
        )
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

    def test_finish_is_terminal(self) -> None:
        rid = self._started()
        rc_, res = self.persist(
            "finish", "--payload", "-", stdin=json.dumps(valid_handoff())
        )
        self.assertEqual((rc_, res["stored"]), (0, True))
        rc_, res = self.persist("note", "--kind", "candidate", "--text", "after finish")
        self.assertEqual(
            (rc_, res["action"], res["outcome"]), (rp.EXIT_STOP, "stop", "terminal")
        )
        self.assertEqual(len(self._events(rid)), 1)
        rc_, res = self.persist(
            "finish", "--payload", "-", stdin=json.dumps(valid_handoff())
        )
        self.assertEqual((rc_, res["stored"]), (rp.EXIT_STOP, False))

    def test_root_is_bound_by_start(self) -> None:
        custom = os.path.join(self.tmp, "custom-root")
        os.makedirs(os.path.dirname(custom), exist_ok=True)
        rc_, res = self._run(
            {},
            ["--root", custom, "start", "--dispatch", "-", "--now", NOW],
            json.dumps(valid_dispatch()),
        )
        self.assertEqual(rc_, 0, res)
        rid = res["run_id"]
        # later calls without --root use the bound root
        rc_, res = self._run({}, ["note", "--kind", "candidate", "--text", "x"])
        self.assertEqual((rc_, res["action"], res["seq"]), (0, "continue", 1), res)
        self.assertEqual(len(rs.op_load(custom, rid)["events"]), 1)
        # a different --root is refused, nothing written anywhere
        rc_, res = self._run(
            {},
            [
                "--root",
                os.path.join(self.tmp, "other"),
                "note",
                "--kind",
                "candidate",
                "--text",
                "y",
            ],
        )
        self.assertEqual((rc_, res["action"]), (rp.EXIT_USAGE, "usage"))
        self.assertIn("bound storage root", res["detail"])
        self.assertEqual(len(rs.op_load(custom, rid)["events"]), 1)
        self.assertFalse(os.path.exists(os.path.join(self.tmp, "other")))

    def test_malformed_acknowledgment_is_uncertain_never_a_citation(self) -> None:
        cases = {
            "wrong_schema_exit6": "print(json.dumps({'schema':'wrong','outcome':'committed','seq':99,'run_id':RID})); sys.exit(6)\n",
            "exit_contradicts": "print(json.dumps({'schema':'run-store-result/v1','outcome':'committed','seq':99,'run_id':RID})); sys.exit(6)\n",
            "wrong_run_id": "print(json.dumps({'schema':'run-store-result/v1','outcome':'committed','seq':1,'run_id':'20260909T120000Z-00000000'})); sys.exit(0)\n",
            "bad_seq": "print(json.dumps({'schema':'run-store-result/v1','outcome':'committed','seq':'1','run_id':RID})); sys.exit(0)\n",
            "not_json": "print('committed'); sys.exit(0)\n",
        }
        for n, (name, script) in enumerate(cases.items()):
            with self.subTest(name):
                # a fresh run + state per case
                if os.path.exists(self.state):
                    os.remove(self.state)
                rc_, res = self.persist(
                    "start",
                    "--dispatch",
                    "-",
                    "--now",
                    f"2026-09-09T12:00:{n:02d}Z",
                    stdin=json.dumps(valid_dispatch()),
                )
                self.assertEqual(rc_, 0, res)
                rid = res["run_id"]
                env = self._fake_store("RID = %r\n" % rid + script)
                rc_, res = self._run(
                    env, ["note", "--kind", "candidate", "--text", name]
                )
                self.assertEqual(
                    (rc_, res.get("action"), res.get("outcome")),
                    (rp.EXIT_STOP, "stop", "malformed"),
                    (name, res),
                )
                self.assertNotIn("cite", res)
                self.assertIn("uncertain", res["detail"])
                self.assertEqual(self._events(rid), [])


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class TruthfulFallback(_Env):
    """The operational-error handoff reports the CURRENT work."""

    def _started(self) -> str:
        rc_, res = self.persist(
            "start", "--dispatch", "-", "--now", NOW, stdin=json.dumps(valid_dispatch())
        )
        self.assertEqual(rc_, 0, res)
        return str(res["run_id"])

    def _fake_refusal(self) -> dict[str, str]:
        fake = os.path.join(self.tmp, "fake_store.py")
        with open(fake, "w", encoding="utf-8") as f:
            f.write(
                "import json, sys\n"
                "print(json.dumps({'schema':'run-store-result/v1','outcome':'nothing_written','code':'publish_unsynced','detail':'fsync failed'})); sys.exit(3)\n"
            )
        return {"LEAN4_RUN_STORE_ARGV": json.dumps([sys.executable, fake])}

    def test_fallback_reflects_latest_dispatch_changes_baseline_and_evidence(
        self,
    ) -> None:
        self._started()
        # redispatch to ANOTHER target with a different ownership set
        d2 = valid_dispatch(target="/repo/Bar.lean:7", owned_files=["/repo/Bar.lean"])
        d2["file_baseline"] = {
            "schema": "file-baseline/v1",
            "files": [
                {
                    "path": "/repo/Bar.lean",
                    "realpath": "/repo/Bar.lean",
                    "exists": True,
                    "sha256": "a" * 64,
                    "size": 10,
                }
            ],
        }
        rc_, res = self.persist("dispatch", "--payload", "-", stdin=json.dumps(d2))
        self.assertEqual(rc_, 0, res)
        # a worker handoff recording changed files, a newer baseline and evidence
        h = valid_handoff(
            target="/repo/Bar.lean:7",
            files_owned=["/repo/Bar.lean"],
            files_changed=["/repo/Bar.lean"],
            failed_avenues=["simp only [foo]"],
            attempted_tools=["lean_leansearch"],
        )
        h["file_baseline"] = {
            "schema": "file-baseline/v1",
            "files": [
                {
                    "path": "/repo/Bar.lean",
                    "realpath": "/repo/Bar.lean",
                    "exists": True,
                    "sha256": "b" * 64,
                    "size": 12,
                }
            ],
        }
        h["evidence"]["queries"] = ["tendsto atTop"]
        rc_, res = self.persist("handoff", "--payload", "-", stdin=json.dumps(h))
        self.assertEqual(rc_, 0, res)
        rc_, res = self.persist(
            "note", "--kind", "failed-avenue", "--text", "exact foo: type mismatch"
        )
        self.assertEqual(rc_, 0, res)
        # now the store refuses
        env = dict(self.env, **self._fake_refusal())
        p = subprocess.run(
            [
                PERSIST,
                "--project-root",
                self.project,
                "note",
                "--kind",
                "candidate",
                "--text",
                "x",
            ],
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        res = json.loads(p.stdout)
        self.assertEqual((p.returncode, res["action"]), (rp.EXIT_STOP, "stop"), res)
        fb = res["handoff"]
        self.assertEqual(fb["target"], "/repo/Bar.lean:7")
        self.assertEqual(fb["files_owned"], ["/repo/Bar.lean"])
        self.assertEqual(fb["files_changed"], ["/repo/Bar.lean"])
        self.assertEqual(fb["file_baseline"]["files"][0]["sha256"], "b" * 64)
        self.assertEqual(
            fb["failed_avenues"], ["simp only [foo]", "exact foo: type mismatch"]
        )
        self.assertEqual(fb["attempted_tools"], ["lean_leansearch"])
        self.assertEqual(fb["evidence"]["queries"], ["tendsto atTop"])
        self.assertEqual(rc.validate_handoff(fb), [])

    def test_invalid_finish_submission_yields_a_valid_fallback(self) -> None:
        rid = self._started()
        rc_, res = self.persist("finish", "--payload", "-", stdin="{}")
        self.assertEqual(
            (rc_, res["action"], res["stored"], res["outcome"]),
            (rp.EXIT_STOP, "done", False, "invalid_submission"),
        )
        self.assertEqual(rc.validate_handoff(res["fallback_handoff"]), [])
        self.assertEqual(res["fallback_handoff"]["stop_reason"], "operational-error")
        self.assertNotIn("cite", res)
        self.assertEqual(rs.op_load(self.root, rid)["events"], [])


@unittest.skipUnless(POSIX, "the store's mutation hosts")
class Round2(_Env):
    """Review round 2: a committed write with failed bookkeeping stops NOW;
    a worker handoff whose own write fails still informs the fallback."""

    def _started(self) -> str:
        rc_, res = self.persist(
            "start", "--dispatch", "-", "--now", NOW, stdin=json.dumps(valid_dispatch())
        )
        self.assertEqual(rc_, 0, res)
        return str(res["run_id"])

    def _events(self, rid: str) -> list[dict[str, Any]]:
        return list(rs.op_load(self.root, rid)["events"])

    def _move_state_into(self, dirname: str) -> str:
        d = os.path.join(self.tmp, dirname)
        os.makedirs(d)
        state = os.path.join(d, "state.json")
        shutil.move(self.state, state)
        self.env["LEAN4_RUN_PERSIST_STATE"] = state
        return d

    def _store_that_freezes(self, state_dir: str, extra: str = "") -> dict[str, str]:
        fake = os.path.join(self.tmp, "fake_store.py")
        with open(fake, "w", encoding="utf-8") as f:
            f.write(
                "import json, os, sys\nargs = sys.argv[1:]\n"
                "sys.path.insert(0, %r)\n"
                "import run_store as rs\n"
                "%s"
                "os.chmod(%r, 0o500)\n"
                "sys.exit(rs.main(args))\n" % (_LIB, extra, state_dir)
            )
        return {"LEAN4_RUN_STORE_ARGV": json.dumps([sys.executable, fake])}

    def _run(
        self, env_extra: dict[str, str], argv: list[str], stdin: str | None = None
    ) -> tuple[int, dict[str, Any]]:
        env = dict(self.env, **env_extra)
        p = subprocess.run(
            [PERSIST, "--project-root", self.project, *argv],
            input=stdin,
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        self.assertTrue(p.stdout.strip(), p.stderr)
        return p.returncode, json.loads(p.stdout)

    def test_committed_write_with_failed_bookkeeping_stops_now(self) -> None:
        rid = self._started()
        state_dir = self._move_state_into("st-commit")
        env = self._store_that_freezes(
            state_dir
        )  # real store commits, then the state dir is frozen
        try:
            rc_, res = self._run(
                env, ["note", "--kind", "candidate", "--text", "try simp"]
            )
        finally:
            os.chmod(state_dir, 0o700)
        # the journal DID commit — the result says so, with its citation …
        self.assertEqual(len(self._events(rid)), 1)
        self.assertEqual(res["committed"], {"seq": 1, "cite": f"{rid}#1"})
        # … but the current response is a STOP, not a continue
        self.assertEqual(
            (rc_, res["action"], res["outcome"]),
            (rp.EXIT_STOP, "stop", "state_unwritable"),
            res,
        )
        self.assertEqual(res["handoff"]["stop_reason"], "operational-error")
        self.assertNotIn("unpersisted", res)
        # and the next call stops too
        rc_, res2 = self._run({}, ["note", "--kind", "candidate", "--text", "again"])
        self.assertEqual((rc_, res2["action"]), (rp.EXIT_STOP, "stop"))
        self.assertEqual(len(self._events(rid)), 1)

    def _worker_handoff(self) -> dict[str, Any]:
        h = valid_handoff(
            files_changed=["/repo/Foo.lean"],
            failed_avenues=["simp only [foo]"],
            attempted_tools=["lean_leansearch"],
        )
        h["file_baseline"] = {
            "schema": "file-baseline/v1",
            "files": [
                {
                    "path": "/repo/Foo.lean",
                    "realpath": "/repo/Foo.lean",
                    "exists": True,
                    "sha256": "c" * 64,
                    "size": 99,
                }
            ],
        }
        h["evidence"]["queries"] = ["tendsto atTop"]
        h["artifacts"] = [
            {"kind": "unified-diff", "content": "--- a/Foo.lean\n+++ b/Foo.lean\n"}
        ]
        return h

    def _assert_fallback_reflects_handoff(self, fb: dict[str, Any]) -> None:
        self.assertEqual(fb["files_changed"], ["/repo/Foo.lean"])
        self.assertEqual(fb["file_baseline"]["files"][0]["sha256"], "c" * 64)
        self.assertEqual(fb["failed_avenues"], ["simp only [foo]"])
        self.assertEqual(fb["attempted_tools"], ["lean_leansearch"])
        self.assertEqual(fb["evidence"]["queries"], ["tendsto atTop"])
        self.assertEqual(fb["artifacts"][0]["kind"], "unified-diff")
        self.assertEqual(rc.validate_handoff(fb), [])

    def test_refused_worker_handoff_still_informs_the_fallback(self) -> None:
        rid = self._started()
        # a real pre-write refusal: the publication barrier (run dir fsync) fails
        fake = os.path.join(self.tmp, "fake_store.py")
        with open(fake, "w", encoding="utf-8") as f:
            f.write(
                "import json, os, sys\nargs = sys.argv[1:]\n"
                "sys.path.insert(0, %r)\n"
                "import run_store as rs\n"
                "def bad_fsync(fd):\n"
                "    import os as _os, stat as _stat\n"
                "    if _stat.S_ISDIR(_os.fstat(fd).st_mode): raise OSError(5, 'injected barrier failure')\n"
                "    _os.fsync(fd)\n"
                "rs._fsync = bad_fsync\n"
                "sys.exit(rs.main(args))\n" % _LIB
            )
        env = {"LEAN4_RUN_STORE_ARGV": json.dumps([sys.executable, fake])}
        rc_, res = self._run(
            env, ["handoff", "--payload", "-"], json.dumps(self._worker_handoff())
        )
        self.assertEqual(
            (rc_, res["action"], res["outcome"]),
            (rp.EXIT_STOP, "stop", "refused:publish_unsynced"),
            res,
        )
        self.assertEqual(self._events(rid), [])  # nothing reached the journal
        self._assert_fallback_reflects_handoff(res["handoff"])
        self.assertEqual(res["unpersisted"]["kind"], "handoff")
        self.assertIsNone(res["unpersisted"]["seq"])
        # a later call (e.g. the command's finish) still sees that knowledge
        rc_, res2 = self._run(
            {}, ["finish", "--payload", "-"], json.dumps(valid_handoff())
        )
        self.assertEqual((rc_, res2["stored"]), (rp.EXIT_STOP, False))

    def test_indeterminate_worker_handoff_write_still_informs_the_fallback(
        self,
    ) -> None:
        rid = self._started()
        fake = os.path.join(self.tmp, "fake_store.py")
        with open(fake, "w", encoding="utf-8") as f:
            f.write(
                "import json, os, sys\nargs = sys.argv[1:]\n"
                "sys.path.insert(0, %r)\n"
                "import run_store as rs\n"
                "def bad_fsync(fd):\n"
                "    import os as _os\n"
                "    if 'events' in _os.readlink('/proc/self/fd/%%d' %% fd): raise OSError(5, 'injected journal fsync failure')\n"
                "    _os.fsync(fd)\n"
                "rs._fsync = bad_fsync\n"
                "sys.exit(rs.main(args))\n" % _LIB
            )
        env = {"LEAN4_RUN_STORE_ARGV": json.dumps([sys.executable, fake])}
        rc_, res = self._run(
            env, ["handoff", "--payload", "-"], json.dumps(self._worker_handoff())
        )
        self.assertEqual(
            (rc_, res["action"], res["outcome"]),
            (rp.EXIT_STOP, "stop", "indeterminate"),
            res,
        )
        self._assert_fallback_reflects_handoff(res["handoff"])
        self.assertEqual(res["unpersisted"]["kind"], "handoff")
        self.assertNotIn("cite", res)
        self.assertEqual(
            len(self._events(rid)), 1
        )  # visible, but never claimed committed

    def test_invalid_handoff_submission_is_still_rejected(self) -> None:
        rid = self._started()
        rc_, res = self._run(
            {}, ["handoff", "--payload", "-"], json.dumps({"schema": "x"})
        )
        self.assertEqual((rc_, res["action"]), (rp.EXIT_STOP, "stop"), res)
        self.assertEqual(res["outcome"], "refused:invalid_payload")
        self.assertEqual(res["handoff"]["files_changed"], [])  # nothing valid to absorb
        self.assertEqual(self._events(rid), [])


if __name__ == "__main__":
    unittest.main()
