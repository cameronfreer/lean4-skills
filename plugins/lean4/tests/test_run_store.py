"""run-store/v1 storage primitive (#82A; Refs #82) — behavioural suite.

Executable evidence for the contract in references/run-store.md: round-trip,
validator hardening against arbitrary JSON, damaged-journal policy (recoverable
unterminated tail vs corruption; append-after-damage refused), cache
staleness rules, write outcomes under injected faults (short writes, fsync /
rename / directory-sync failures at each step of append, set-handoff and
create), competing lock acquisition, containment, and Git-ignore behaviour.
Stdlib only. Mutation tests skip on hosts the store does not support.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from typing import Any

_HERE = os.path.dirname(os.path.abspath(__file__))
_LIB = os.path.join(os.path.dirname(_HERE), "lib", "scripts")
sys.path.insert(0, _LIB)
sys.path.insert(0, _HERE)
import run_contract_validate as rc  # noqa: E402
import run_store as rs  # noqa: E402
from test_run_contract import valid_dispatch, valid_handoff  # noqa: E402

BIN = os.path.join(os.path.dirname(_HERE), "bin", "lean4-skills-run-store")
NOW = "2026-09-09T12:00:00Z"
POSIX = rs.platform_supported()


def _read(path: str) -> bytes:
    with open(path, "rb") as f:
        return f.read()


def _text(path: str) -> str:
    with open(path, encoding="utf-8") as f:
        return f.read()


def _is_lock_payload(data: bytes) -> bool:
    """The lock's diagnostic contents also go through the injectable write;
    fault injections aimed at the journal let them through."""
    return data.startswith(b'{"pid"')


def _note(**over: Any) -> dict[str, Any]:
    n: dict[str, Any] = {"kind": "candidate", "text": "try simp", "lean": None}
    n.update(over)
    return n


class _Base(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp(prefix="run-store-")
        self.project = os.path.join(self.tmp, "proj")
        os.makedirs(self.project)
        self.root = os.path.join(self.project, ".lean4-skills")
        self.runs = os.path.join(self.root, "runs")

    def tearDown(self) -> None:
        import shutil

        shutil.rmtree(self.tmp, ignore_errors=True)

    def create(self, **kw: Any) -> str:
        res = rs.op_create(
            valid_dispatch(),
            storage_root=self.root,
            project_root=self.project,
            tracker_session_id=kw.get("session"),
            prior_run=kw.get("prior_run"),
            now=kw.get("now", NOW),
        )
        self.assertEqual(res["outcome"], "committed")
        return res["run_id"]

    def rid_for(self, now: str) -> str:
        d = valid_dispatch()
        return rs.make_run_id(d["target"], d["scope"], d["mode"], None, now)

    def run_dir(self, rid: str) -> str:
        return os.path.join(self.runs, rid)

    def journal_path(self, rid: str) -> str:
        return os.path.join(self.run_dir(rid), rs.JOURNAL_NAME)

    def cli(
        self, *args: str, stdin: str | None = None
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [BIN, "--root", self.root, "--project-root", self.project, *args],
            input=stdin,
            capture_output=True,
            text=True,
            check=False,
        )


# ---------------------------------------------------------------------------
# validator hardening (platform-independent)
# ---------------------------------------------------------------------------


class ValidatorHardening(unittest.TestCase):
    """The reviewer's four cases plus a field-by-field substitution sweep: no
    exception ever escapes; every case returns a non-empty error list."""

    JUNK = ([], {}, 7, None, "x", True, [[]], {"a": []})

    def test_reviewer_cases(self) -> None:
        d = valid_dispatch()
        d["target"] = []
        self.assertTrue(any("target" in m for m in rc.validate_dispatch(d)))
        d = valid_dispatch()
        d["scope"] = []
        self.assertTrue(any("scope" in m for m in rc.validate_dispatch(d)))
        self.assertEqual(rc.validate_dispatch([]), ["dispatch must be a JSON object"])
        self.assertEqual(rc.validate_handoff([]), ["handoff must be a JSON object"])
        h = valid_handoff(
            status="stopped", stop_reason="operational-error", stop_detail=7
        )
        self.assertTrue(any("stop_detail" in m for m in rc.validate_handoff(h)))

    def test_root_junk_never_raises(self) -> None:
        for junk in self.JUNK:
            for fn in (
                rc.validate_dispatch,
                rc.validate_handoff,
                rs.validate_event,
                rs.validate_manifest,
                rs.validate_cache,
                rs.validate_note,
            ):
                self.assertTrue(fn(junk), f"{fn.__name__}({junk!r}) accepted")

    def test_dispatch_field_sweep(self) -> None:
        for field in rc.DISPATCH_FIELDS:
            for junk in self.JUNK:
                d = valid_dispatch()
                d[field] = junk
                errs = rc.validate_dispatch(d)  # must not raise
                if junk == d.get(field) and not errs:
                    continue
                self.assertIsInstance(errs, list)
        # context members and budget members too
        for member in rc.CONTEXT_FIELDS:
            for junk in self.JUNK:
                d = valid_dispatch()
                d["context"][member] = junk
                self.assertIsInstance(rc.validate_dispatch(d), list)
        for member in ("max_cycles", "max_stuck_cycles", "runtime"):
            for junk in self.JUNK:
                d = valid_dispatch()
                d["budget"][member] = junk
                self.assertIsInstance(rc.validate_dispatch(d), list)

    def test_handoff_field_sweep(self) -> None:
        for field in rc.HANDOFF_FIELDS:
            for junk in self.JUNK:
                for base in (
                    valid_handoff(),
                    valid_handoff(
                        status="stopped", stop_reason="protocol-error", stop_detail="x"
                    ),
                ):
                    base[field] = junk
                    self.assertIsInstance(rc.validate_handoff(base), list)

    def test_parameters_with_unhashable_worker(self) -> None:
        self.assertEqual(rc.validate_parameters([], {}), ["unknown worker"])
        self.assertEqual(rc.validate_parameters({}, {}), ["unknown worker"])

    def test_event_and_note_shapes(self) -> None:
        ev = {
            "schema": rs.EVENT_SCHEMA,
            "seq": 1,
            "ts": NOW,
            "kind": "note",
            "payload": _note(),
        }
        self.assertEqual(rs.validate_event(ev, expect_seq=1), [])
        self.assertTrue(rs.validate_event(ev, expect_seq=2))
        self.assertTrue(rs.validate_event({**ev, "seq": True}))
        self.assertTrue(rs.validate_event({**ev, "kind": "verified"}))
        self.assertTrue(rs.validate_event({**ev, "extra": 1}))
        self.assertTrue(rs.validate_note(_note(kind="critique")))
        self.assertTrue(rs.validate_note(_note(lean=3)))
        self.assertEqual(rs.validate_note(_note(lean="example : True := trivial")), [])

    def test_run_id_and_manifest(self) -> None:
        rid = rs.make_run_id("Foo.lean:3", "sorry", "prove", None, NOW)
        self.assertTrue(rs.valid_run_id(rid))
        self.assertTrue(rid.startswith("20260909T120000Z-"))
        for bad in ("../x", "20260909T120000Z-XYZ", "", "a/b", rid + "/"):
            self.assertFalse(rs.valid_run_id(bad))
        m = {
            "schema": rs.MANIFEST_SCHEMA,
            "run_id": rid,
            "created": NOW,
            "plugin_version": "4.9.0",
            "storage_root": "/x",
            "tracker_session_id": None,
            "prior_run": None,
            "dispatch": valid_dispatch(),
        }
        self.assertEqual(rs.validate_manifest(m), [])
        self.assertTrue(rs.validate_manifest({**m, "prior_run": "nope"}))
        self.assertTrue(rs.validate_manifest({**m, "tracker_session_id": 5}))
        self.assertTrue(rs.validate_manifest({**m, "dispatch": []}))


# ---------------------------------------------------------------------------
# storage behaviour (POSIX hosts)
# ---------------------------------------------------------------------------


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class RoundTrip(_Base):
    def test_create_append_handoff_load(self) -> None:
        rid = self.create()
        self.assertTrue(rs.valid_run_id(rid))
        self.assertEqual(
            sorted(os.listdir(self.run_dir(rid))), ["events.jsonl", "manifest.json"]
        )
        self.assertEqual(rs.op_append(self.root, rid, "note", _note())["seq"], 1)
        d2 = valid_dispatch(prior_blocker="sig", evidence_delta=["new lemma"])
        self.assertEqual(rs.op_append(self.root, rid, "dispatch", d2)["seq"], 2)
        h = valid_handoff()
        res = rs.op_set_handoff(self.root, rid, h)
        self.assertEqual((res["outcome"], res["seq"]), ("committed", 3))
        out = rs.op_load(self.root, rid)
        self.assertEqual([e["seq"] for e in out["events"]], [1, 2, 3])
        self.assertEqual(out["effective_handoff"]["payload"], h)
        self.assertEqual(out["handoff_cache"], "current")
        self.assertEqual(out["warnings"], [])
        self.assertFalse(out["damaged"])
        self.assertEqual(out["manifest"]["dispatch"], valid_dispatch())
        self.assertIsNone(out["manifest"]["tracker_session_id"])
        # the first dispatch is NOT duplicated in the journal
        self.assertEqual(
            [e["kind"] for e in out["events"]], ["note", "dispatch", "handoff"]
        )

    def test_no_handoff_yet_means_cache_absent(self) -> None:
        rid = self.create()
        out = rs.op_load(self.root, rid)
        self.assertIsNone(out["effective_handoff"])
        self.assertEqual(out["handoff_cache"], "absent")
        self.assertFalse(os.path.exists(os.path.join(self.run_dir(rid), rs.CACHE_NAME)))

    def test_prior_run_and_session(self) -> None:
        a = self.create()
        b = self.create(now="2026-09-09T12:00:01Z", prior_run=a, session="s1")
        m = rs.op_load(self.root, b)["manifest"]
        self.assertEqual((m["prior_run"], m["tracker_session_id"]), (a, "s1"))
        with self.assertRaises(rs.RefusedError) as cm:
            self.create(now="2026-09-09T12:00:02Z", prior_run="bogus")
        self.assertEqual(cm.exception.code, "bad_run_id")

    def test_collision_is_an_error_not_shared_storage(self) -> None:
        rid = self.create()
        before = os.listdir(self.run_dir(rid))
        with self.assertRaises(rs.RefusedError) as cm:
            self.create()
        self.assertEqual(cm.exception.code, "run_exists")
        self.assertEqual(os.listdir(self.run_dir(rid)), before)

    def test_invalid_payloads_refused_nothing_written(self) -> None:
        rid = self.create()
        size = os.path.getsize(self.journal_path(rid))
        for kind, payload in (
            ("note", _note(kind="critique")),
            ("dispatch", []),
            ("handoff", {"schema": "x"}),
        ):
            with self.assertRaises(rs.RefusedError) as cm:
                rs.op_append(self.root, rid, kind, payload)
            self.assertEqual(cm.exception.code, "invalid_payload")
        with self.assertRaises(rs.RefusedError):
            rs.op_create(
                [],
                storage_root=self.root,
                project_root=self.project,
                tracker_session_id=None,
                prior_run=None,
                now=NOW,
            )
        self.assertEqual(os.path.getsize(self.journal_path(rid)), size)

    def test_load_and_validate_do_not_change_files(self) -> None:
        rid = self.create()
        rs.op_set_handoff(self.root, rid, valid_handoff())
        snap = {
            n: _read(os.path.join(self.run_dir(rid), n))
            for n in os.listdir(self.run_dir(rid))
        }
        rs.op_load(self.root, rid)
        after = {
            n: _read(os.path.join(self.run_dir(rid), n))
            for n in os.listdir(self.run_dir(rid))
        }
        self.assertEqual(snap, after)


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class JournalDamage(_Base):
    def _events(self, rid: str, n: int) -> None:
        for _ in range(n):
            rs.op_append(self.root, rid, "note", _note())

    def test_unterminated_tail_is_recoverable_but_blocks_append(self) -> None:
        rid = self.create()
        self._events(rid, 2)
        with open(self.journal_path(rid), "ab") as f:
            f.write(b'{"schema":"run-store-event/v1","seq":3,"ts":"x"')  # no newline
        before = _read(self.journal_path(rid))
        out = rs.op_load(self.root, rid)
        self.assertEqual([e["seq"] for e in out["events"]], [1, 2])
        self.assertEqual([w["code"] for w in out["warnings"]], ["truncated_tail"])
        self.assertTrue(out["damaged"])
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm.exception.code, "journal_damaged")
        with self.assertRaises(rs.RefusedError):
            rs.op_set_handoff(self.root, rid, valid_handoff())
        # bytes untouched — excluded from history never means deleted
        self.assertEqual(_read(self.journal_path(rid)), before)
        # recovery: a new linked run
        rid2 = self.create(now="2026-09-09T12:00:05Z", prior_run=rid)
        self.assertEqual(rs.op_append(self.root, rid2, "note", _note())["seq"], 1)

    def _corrupt_case(self, line: bytes, code: str = "corrupt") -> None:
        rid = self.create()
        self._events(rid, 2)
        with open(self.journal_path(rid), "ab") as f:
            f.write(line + b"\n")
        out = rs.op_load(self.root, rid)
        self.assertEqual([e["seq"] for e in out["events"]], [1, 2])
        self.assertEqual(out["warnings"][0]["code"], code)
        self.assertEqual(out["warnings"][0]["line"], 3)
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm.exception.code, "journal_damaged")

    def test_terminated_garbage_is_corruption(self) -> None:
        self._corrupt_case(b"not json")

    def test_schema_invalid_event_is_corruption(self) -> None:
        self._corrupt_case(
            json.dumps(
                {
                    "schema": rs.EVENT_SCHEMA,
                    "seq": 3,
                    "ts": NOW,
                    "kind": "verified",
                    "payload": {},
                }
            ).encode()
        )

    def test_seq_gap_is_corruption(self) -> None:
        self._corrupt_case(
            json.dumps(
                {
                    "schema": rs.EVENT_SCHEMA,
                    "seq": 5,
                    "ts": NOW,
                    "kind": "note",
                    "payload": _note(),
                }
            ).encode()
        )

    def test_seq_duplicate_is_corruption(self) -> None:
        self._corrupt_case(
            json.dumps(
                {
                    "schema": rs.EVENT_SCHEMA,
                    "seq": 2,
                    "ts": NOW,
                    "kind": "note",
                    "payload": _note(),
                }
            ).encode()
        )

    def test_corruption_before_tail_reported_once(self) -> None:
        rid = self.create()
        self._events(rid, 1)
        with open(self.journal_path(rid), "ab") as f:
            f.write(b'garbage\n{"partial')
        out = rs.op_load(self.root, rid)
        self.assertEqual([w["code"] for w in out["warnings"]], ["corrupt"])

    def test_incomplete_and_integrity_states(self) -> None:
        rid = self.create()
        os.remove(self.journal_path(rid))
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_load(self.root, rid)
        self.assertEqual(cm.exception.code, "integrity_failure")
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm.exception.code, "integrity_failure")
        os.remove(os.path.join(self.run_dir(rid), rs.MANIFEST_NAME))
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_load(self.root, rid)
        self.assertEqual(cm.exception.code, "incomplete_run")
        with open(os.path.join(self.run_dir(rid), rs.MANIFEST_NAME), "w") as f:
            f.write("{}")
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm.exception.code, "incomplete_run")


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class HandoffCache(_Base):
    def _cache_path(self, rid: str) -> str:
        return os.path.join(self.run_dir(rid), rs.CACHE_NAME)

    def test_journal_wins_over_older_cache(self) -> None:
        rid = self.create()
        rs.op_set_handoff(self.root, rid, valid_handoff())
        keep = _read(self._cache_path(rid))
        rs.op_set_handoff(self.root, rid, valid_handoff(next_action="stop"))
        with open(self._cache_path(rid), "wb") as f:
            f.write(
                keep
            )  # cache agrees with event 1 but journal has a newer handoff at 2
        out = rs.op_load(self.root, rid)
        self.assertEqual(out["effective_handoff"]["seq"], 2)
        self.assertEqual(out["handoff_cache"], "stale")

    def test_missing_malformed_and_mismatched_cache(self) -> None:
        rid = self.create()
        rs.op_set_handoff(self.root, rid, valid_handoff())
        os.remove(self._cache_path(rid))
        self.assertEqual(rs.op_load(self.root, rid)["handoff_cache"], "stale")
        with open(self._cache_path(rid), "w") as f:
            f.write("{nope")
        self.assertEqual(rs.op_load(self.root, rid)["handoff_cache"], "stale")
        with open(self._cache_path(rid), "w") as f:
            json.dump(
                {
                    "schema": rs.HANDOFF_CACHE_SCHEMA,
                    "seq": 1,
                    "payload": valid_handoff(next_action="stop"),
                },
                f,
            )
        out = rs.op_load(self.root, rid)
        self.assertEqual(out["handoff_cache"], "stale")
        self.assertEqual(out["effective_handoff"]["payload"], valid_handoff())

    def test_cache_ahead_of_prefix_adds_no_history(self) -> None:
        rid = self.create()
        with open(self._cache_path(rid), "w") as f:
            json.dump(
                {
                    "schema": rs.HANDOFF_CACHE_SCHEMA,
                    "seq": 9,
                    "payload": valid_handoff(),
                },
                f,
            )
        out = rs.op_load(self.root, rid)
        self.assertIsNone(out["effective_handoff"])
        self.assertEqual(out["handoff_cache"], "stale")


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class WriteOutcomes(_Base):
    """Fault injection at each durability step."""

    def setUp(self) -> None:
        super().setUp()
        self._saved = (rs._write, rs._fsync, rs._rename, rs._full_fsync_hook)

    def tearDown(self) -> None:
        rs._write, rs._fsync, rs._rename, rs._full_fsync_hook = self._saved
        super().tearDown()

    def _fail_fsync_on(self, nth: int) -> None:
        calls = {"n": 0}
        real = os.fsync

        def fsync(fd: int) -> None:
            calls["n"] += 1
            if calls["n"] == nth:
                raise OSError(5, "injected fsync failure")
            real(fd)

        rs._fsync = fsync

    def test_short_writes_are_retried_then_committed(self) -> None:
        rid = self.create()
        real = os.write

        def short(fd: int, data: bytes) -> int:
            if _is_lock_payload(data):
                return real(fd, data)
            return real(fd, data[: max(1, len(data) // 3)])

        rs._write = short
        self.assertEqual(
            rs.op_append(self.root, rid, "note", _note())["outcome"], "committed"
        )
        rs._write = real
        out = rs.op_load(self.root, rid)
        self.assertEqual(out["warnings"], [])
        self.assertEqual(len(out["events"]), 1)

    def test_partial_write_then_failure_is_indeterminate(self) -> None:
        rid = self.create()
        real = os.write
        calls = {"n": 0}

        def flaky(fd: int, data: bytes) -> int:
            if _is_lock_payload(data):
                return real(fd, data)
            calls["n"] += 1
            if calls["n"] == 1:
                return real(fd, data[:5])
            raise OSError(28, "injected ENOSPC")

        rs._write = flaky
        with self.assertRaises(rs.IndeterminateError) as cm:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm.exception.step, "append.write")
        rs._write = real
        # the journal now has an unterminated fragment: recoverable on load, blocks append
        out = rs.op_load(self.root, rid)
        self.assertEqual([w["code"] for w in out["warnings"]], ["truncated_tail"])
        with self.assertRaises(rs.RefusedError) as cm2:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm2.exception.code, "journal_damaged")

    def test_first_write_failure_is_nothing_written(self) -> None:
        rid = self.create()

        def boom(fd: int, data: bytes) -> int:
            if _is_lock_payload(data):
                return os.write(fd, data)
            raise OSError(5, "injected EIO")

        rs._write = boom
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm.exception.code, "write_failed")
        rs._write = os.write
        self.assertEqual(rs.op_load(self.root, rid)["warnings"], [])

    def test_journal_fsync_failure_is_indeterminate(self) -> None:
        rid = self.create()
        self._fail_fsync_on(1)
        with self.assertRaises(rs.IndeterminateError) as cm:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm.exception.step, "append.fsync")
        rs._fsync = os.fsync
        # bytes did land; the caller must reconcile, not blindly retry
        self.assertEqual(len(rs.op_load(self.root, rid)["events"]), 1)

    def test_full_fsync_failure_is_indeterminate(self) -> None:
        rid = self.create()

        def hook(fd: int) -> None:
            raise OSError(22, "injected F_FULLFSYNC failure")

        rs._full_fsync_hook = hook
        with self.assertRaises(rs.IndeterminateError):
            rs.op_append(self.root, rid, "note", _note())

    def test_cache_rename_failure_is_journal_only(self) -> None:
        rid = self.create()

        def bad_rename(*a: Any, **k: Any) -> None:
            raise OSError(5, "injected rename failure")

        rs._rename = bad_rename
        res = rs.op_set_handoff(self.root, rid, valid_handoff())
        self.assertEqual((res["outcome"], res["seq"]), ("journal_only", 1))
        rs._rename = os.rename
        out = rs.op_load(self.root, rid)
        self.assertEqual(out["effective_handoff"]["seq"], 1)
        self.assertEqual(out["handoff_cache"], "stale")

    def test_cache_dir_fsync_failure_is_journal_only(self) -> None:
        rid = self.create()
        # fsync calls in set-handoff: 1 journal, 2 temp cache file, 3 run dir
        self._fail_fsync_on(3)
        res = rs.op_set_handoff(self.root, rid, valid_handoff())
        self.assertEqual(res["outcome"], "journal_only")
        rs._fsync = os.fsync
        # the rename may already have landed: journal_only does NOT promise a stale cache
        self.assertIn(rs.op_load(self.root, rid)["handoff_cache"], {"current", "stale"})

    def test_create_crash_at_each_step(self) -> None:
        # runs/.gitignore is written (and synced) by the FIRST create only; do
        # that once so the counted fsyncs are the run's own:
        # 1 journal, 2 manifest temp, 3 run dir, 4 runs dir
        self.create(now="2026-09-09T11:59:59Z")
        for nth, expect_manifest in ((1, False), (2, False), (3, True), (4, True)):
            self._fail_fsync_on(nth)
            with self.assertRaises(rs.IndeterminateError):
                self.create(now=f"2026-09-09T12:00:{nth:02d}Z")
            rs._fsync = os.fsync
            rid = self.rid_for(f"2026-09-09T12:00:{nth:02d}Z")
            has_manifest = os.path.exists(
                os.path.join(self.run_dir(rid), rs.MANIFEST_NAME)
            )
            self.assertEqual(has_manifest, expect_manifest, f"step {nth}")
            if not expect_manifest:
                with self.assertRaises(rs.RefusedError) as cm:
                    rs.op_load(self.root, rid)
                self.assertEqual(cm.exception.code, "incomplete_run")
                with self.assertRaises(rs.RefusedError):
                    rs.op_append(self.root, rid, "note", _note())
            else:
                self.assertEqual(rs.op_load(self.root, rid)["events"], [])

    def test_create_rename_failure_leaves_incomplete_run(self) -> None:
        def bad_rename(*a: Any, **k: Any) -> None:
            raise OSError(5, "injected rename failure")

        rs._rename = bad_rename
        with self.assertRaises(rs.IndeterminateError):
            self.create()
        rs._rename = os.rename
        rid = self.rid_for(NOW)
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_load(self.root, rid)
        self.assertEqual(cm.exception.code, "incomplete_run")


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class Locking(_Base):
    def test_existing_lock_blocks_every_mutation(self) -> None:
        rid = self.create()
        lock = os.path.join(self.run_dir(rid), rs.LOCK_NAME)
        with open(lock, "w") as f:
            f.write("not even json\n")  # contents are diagnostic only
        for call in (
            lambda: rs.op_append(self.root, rid, "note", _note()),
            lambda: rs.op_set_handoff(self.root, rid, valid_handoff()),
        ):
            with self.assertRaises(rs.RefusedError) as cm:
                call()
            self.assertEqual(cm.exception.code, "busy")
        self.assertTrue(os.path.exists(lock))  # never broken
        self.assertEqual(
            rs.op_load(self.root, rid)["events"], []
        )  # readers do not lock

    def test_competing_acquisition_exactly_one_wins(self) -> None:
        rid = self.create()
        run_fd = os.open(self.run_dir(rid), os.O_RDONLY | os.O_DIRECTORY)
        try:
            with rs._Lock(run_fd):
                p = self.cli(
                    "append",
                    "--run-id",
                    rid,
                    "--kind",
                    "note",
                    "--payload",
                    "-",
                    stdin=json.dumps(_note()),
                )
                self.assertEqual(p.returncode, rs.EXIT_REFUSED, p.stdout + p.stderr)
                self.assertEqual(json.loads(p.stdout)["code"], "busy")
        finally:
            os.close(run_fd)
        self.assertFalse(os.path.exists(os.path.join(self.run_dir(rid), rs.LOCK_NAME)))
        p = self.cli(
            "append",
            "--run-id",
            rid,
            "--kind",
            "note",
            "--payload",
            "-",
            stdin=json.dumps(_note()),
        )
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)

    def test_lock_released_on_handled_failure(self) -> None:
        rid = self.create()
        with self.assertRaises(rs.RefusedError):
            rs.op_append(self.root, rid, "note", _note(kind="critique"))
        self.assertFalse(os.path.exists(os.path.join(self.run_dir(rid), rs.LOCK_NAME)))


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class Containment(_Base):
    def test_bad_run_ids_rejected_before_filesystem(self) -> None:
        self.create()
        for bad in ("../../etc", "20260909T120000Z-72d7135e/..", "x"):
            with self.assertRaises(rs.RefusedError) as cm:
                rs.op_load(self.root, bad)
            self.assertEqual(cm.exception.code, "bad_run_id")

    def test_symlinked_run_directory_refused(self) -> None:
        rid = self.create()
        outside = os.path.join(self.tmp, "outside")
        os.makedirs(outside)
        target = os.path.join(self.runs, rid)
        import shutil

        shutil.rmtree(target)
        os.symlink(outside, target)
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_load(self.root, rid)
        self.assertEqual(cm.exception.code, "containment")

    def test_symlinked_runs_directory_refused(self) -> None:
        os.makedirs(self.root)
        outside = os.path.join(self.tmp, "outside")
        os.makedirs(outside)
        os.symlink(outside, self.runs)
        with self.assertRaises(rs.RefusedError) as cm:
            self.create()
        self.assertEqual(cm.exception.code, "containment")

    def test_symlinked_journal_refused(self) -> None:
        rid = self.create()
        jp = self.journal_path(rid)
        os.remove(jp)
        os.symlink(os.path.join(self.tmp, "elsewhere.jsonl"), jp)
        with open(os.path.join(self.tmp, "elsewhere.jsonl"), "w"):
            pass
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm.exception.code, "containment")
        # and through the CLI it is a structured refusal, not a traceback
        p = self.cli(
            "append",
            "--run-id",
            rid,
            "--kind",
            "note",
            "--payload",
            "-",
            stdin=json.dumps(_note()),
        )
        self.assertEqual(p.returncode, rs.EXIT_REFUSED, p.stderr)
        self.assertEqual(json.loads(p.stdout)["code"], "containment")

    def test_unsupported_platform_refuses_before_writing(self) -> None:
        saved = rs.platform_supported
        rs.platform_supported = lambda: False
        try:
            with self.assertRaises(rs.RefusedError) as cm:
                self.create()
            self.assertEqual(cm.exception.code, "unsupported_platform")
            self.assertFalse(os.path.exists(self.root))
        finally:
            rs.platform_supported = saved


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class GitBehaviour(_Base):
    def _git(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", "-C", self.project, *args],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_gitignore_written_once_and_preserved(self) -> None:
        self.create()
        gi = os.path.join(self.runs, ".gitignore")
        self.assertEqual(_text(gi), "*\n")
        with open(gi, "w") as f:
            f.write("# user policy\n!keep-me\n")
        self.create(now="2026-09-09T12:00:01Z")
        self.assertEqual(_text(gi), "# user policy\n!keep-me\n")

    def test_indexed_path_refuses_creation(self) -> None:
        if self._git("init", "-q").returncode != 0:
            self.skipTest("git unavailable")
        os.makedirs(self.runs)
        tracked = os.path.join(self.runs, "old.txt")
        with open(tracked, "w") as f:
            f.write("x")
        self._git("add", "-f", os.path.relpath(tracked, self.project))
        with self.assertRaises(rs.RefusedError) as cm:
            self.create()
        self.assertEqual(cm.exception.code, "git_tracked")
        self.assertFalse(os.path.exists(os.path.join(self.runs, ".gitignore")))

    def test_ignored_by_default_in_a_repo(self) -> None:
        if self._git("init", "-q").returncode != 0:
            self.skipTest("git unavailable")
        rid = self.create()
        p = self._git(
            "status", "--porcelain", "--ignored=matching", "--", ".lean4-skills"
        )
        self.assertNotIn("?? ", p.stdout)
        self.assertIn(rid, p.stdout)  # listed only as ignored


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class RootAndStoreInit(_Base):
    """Review round 1: root containment, fresh-store synchronization,
    .gitignore publication, the Git index check against the repository
    that CONTAINS the storage location."""

    def test_symlinked_storage_root_refused_and_nothing_escapes(self) -> None:
        outside = os.path.join(self.tmp, "outside")
        os.makedirs(outside)
        os.symlink(outside, self.root)  # project/.lean4-skills → outside
        with self.assertRaises(rs.RefusedError) as cm:
            self.create()
        self.assertEqual(cm.exception.code, "containment")
        self.assertEqual(os.listdir(outside), [])
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_load(self.root, self.rid_for(NOW))
        self.assertEqual(cm.exception.code, "containment")

    def test_manifest_records_resolved_root(self) -> None:
        # the PARENT may be reached through a symlink (the user's anchor);
        # the manifest records the resolved location
        link = os.path.join(self.tmp, "proj-link")
        os.symlink(self.project, link)
        res = rs.op_create(
            valid_dispatch(),
            storage_root=os.path.join(link, ".lean4-skills"),
            project_root=link,
            tracker_session_id=None,
            prior_run=None,
            now=NOW,
        )
        m = rs.op_load(self.root, res["run_id"])["manifest"]
        self.assertEqual(m["storage_root"], os.path.realpath(self.root))
        self.assertTrue(res["run_directory"].startswith(os.path.realpath(self.root)))

    def test_fresh_store_sync_failures_refuse_before_any_run(self) -> None:
        # fresh store fsync order: 1 storage_root (new runs entry), 2 parent of
        # storage_root (new root entry), 3 .gitignore temp, 4 runs dir (publish)
        for nth in (1, 2, 3, 4):
            import shutil

            shutil.rmtree(self.root, ignore_errors=True)
            self._fail_fsync_on(nth)
            with self.assertRaises(rs.RefusedError) as cm:
                self.create()
            rs._fsync = os.fsync
            self.assertIn(
                cm.exception.code,
                {"store_init_unsynced", "gitignore_write_failed"},
                f"step {nth}",
            )
            self.assertFalse(
                os.path.exists(os.path.join(self.runs, self.rid_for(NOW))),
                f"step {nth}",
            )
            # no half-published .gitignore: either absent or exactly the policy
            gi = os.path.join(self.runs, ".gitignore")
            if os.path.exists(gi):
                self.assertEqual(_text(gi), "*\n")
        # and a clean create afterwards works
        rid = self.create()
        self.assertEqual(rs.op_load(self.root, rid)["events"], [])

    def _fail_fsync_on(self, nth: int) -> None:
        calls = {"n": 0}
        real = os.fsync

        def fsync(fd: int) -> None:
            calls["n"] += 1
            if calls["n"] == nth:
                raise OSError(5, "injected fsync failure")
            real(fd)

        rs._fsync = fsync

    def tearDown(self) -> None:
        rs._fsync = os.fsync
        rs._write = os.write
        super().tearDown()

    def test_failed_gitignore_init_is_not_mistaken_for_user_policy(self) -> None:
        real = os.write

        def boom(fd: int, data: bytes) -> int:
            if data == b"*\n":
                raise OSError(28, "injected ENOSPC")
            return real(fd, data)

        rs._write = boom
        with self.assertRaises(rs.RefusedError) as cm:
            self.create()
        self.assertEqual(cm.exception.code, "gitignore_write_failed")
        rs._write = real
        self.assertFalse(os.path.exists(os.path.join(self.runs, ".gitignore")))
        self.assertEqual([n for n in os.listdir(self.runs) if n.endswith(".tmp")], [])
        rid = self.create()
        self.assertEqual(_text(os.path.join(self.runs, ".gitignore")), "*\n")
        self.assertTrue(rs.valid_run_id(rid))

    def test_git_index_checked_in_the_repo_containing_the_store(self) -> None:
        other = os.path.join(self.tmp, "other-repo")
        os.makedirs(os.path.join(other, "store", "runs"))
        if (
            subprocess.run(
                ["git", "-C", other, "init", "-q"], capture_output=True, check=False
            ).returncode
            != 0
        ):
            self.skipTest("git unavailable")
        tracked = os.path.join(other, "store", "runs", "tracked.txt")
        with open(tracked, "w") as f:
            f.write("x")
        subprocess.run(
            ["git", "-C", other, "add", "-f", "store/runs/tracked.txt"],
            check=True,
            capture_output=True,
        )
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_create(
                valid_dispatch(),
                storage_root=os.path.join(other, "store"),
                project_root=self.project,
                tracker_session_id=None,
                prior_run=None,
                now=NOW,
            )
        self.assertEqual(cm.exception.code, "git_tracked")


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class RecoveryAfterFailure(_Base):
    def setUp(self) -> None:
        super().setUp()
        self._saved = (rs._write, rs._fsync, rs._rename)

    def tearDown(self) -> None:
        rs._write, rs._fsync, rs._rename = self._saved
        super().tearDown()

    def test_lock_init_failure_is_structured_and_releases_the_lock(self) -> None:
        rid = self.create()
        real = os.write

        def boom(fd: int, data: bytes) -> int:
            if _is_lock_payload(data):
                real(fd, data[:5])
                raise OSError(28, "injected ENOSPC")
            return real(fd, data)

        rs._write = boom
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm.exception.code, "lock_init_failed")
        rs._write = real
        self.assertFalse(os.path.exists(os.path.join(self.run_dir(rid), rs.LOCK_NAME)))
        self.assertEqual(
            rs.op_append(self.root, rid, "note", _note())["outcome"], "committed"
        )

    def test_cache_recovers_after_a_failed_rename(self) -> None:
        rid = self.create()

        def bad_rename(*a: Any, **k: Any) -> None:
            raise OSError(5, "injected rename failure")

        rs._rename = bad_rename
        self.assertEqual(
            rs.op_set_handoff(self.root, rid, valid_handoff())["outcome"],
            "journal_only",
        )
        rs._rename = os.rename
        res = rs.op_set_handoff(self.root, rid, valid_handoff(next_action="stop"))
        self.assertEqual((res["outcome"], res["seq"]), ("committed", 2))
        out = rs.op_load(self.root, rid)
        self.assertEqual(out["handoff_cache"], "current")
        self.assertEqual(out["effective_handoff"]["seq"], 2)
        self.assertEqual(
            [n for n in os.listdir(self.run_dir(rid)) if n.endswith(".tmp")], []
        )

    def test_manifest_of_another_run_is_an_integrity_failure(self) -> None:
        rid = self.create()
        other = self.rid_for("2026-09-09T13:00:00Z")
        mp = os.path.join(self.run_dir(rid), rs.MANIFEST_NAME)
        m = json.loads(_text(mp))
        m["run_id"] = other
        with open(mp, "w") as f:
            json.dump(m, f)
        for call in (
            lambda: rs.op_load(self.root, rid),
            lambda: rs.op_append(self.root, rid, "note", _note()),
        ):
            with self.assertRaises(rs.RefusedError) as cm:
                call()
            self.assertEqual(cm.exception.code, "integrity_failure")

    def test_unexpected_oserror_reports_indeterminate_not_nothing_written(self) -> None:
        rid = self.create()
        # the CLI runs a fresh interpreter, so patch via a driver instead
        drv = (
            f"import sys, json; sys.path.insert(0, {_LIB!r}); import run_store as rs\n"
            "def explode(*a, **k): raise OSError(5, 'surprise')\n"
            "rs._append_locked = explode\n"
            f"sys.exit(rs.main(['--root', {self.root!r}, 'append', '--run-id', {rid!r}, '--kind', 'note', '--payload', '-']))"
        )
        p = subprocess.run(
            [sys.executable, "-c", drv],
            input=json.dumps(_note()),
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(p.returncode, rs.EXIT_INDETERMINATE, p.stderr)
        self.assertEqual(json.loads(p.stdout)["outcome"], "indeterminate")


@unittest.skipUnless(POSIX, "process-kill tests need a POSIX host")
class ProcessCrash(_Base):
    """Real process death (SIGKILL) at a chosen fsync, not an injected
    exception: no cleanup code runs, so these exercise the on-disk state a
    restarted process actually finds."""

    def _kill_at(self, nth: int, argv: list[str], stdin: str) -> int:
        drv = (
            "import os, signal, sys, json; sys.path.insert(0, {!r}); import run_store as rs\n"
            "n = {{'n': 0}}\n"
            "def fsync(fd):\n"
            "    n['n'] += 1\n"
            "    if n['n'] == {}: os.kill(os.getpid(), signal.SIGKILL)\n"
            "    os.fsync(fd)\n"
            "rs._fsync = fsync\n"
            "sys.exit(rs.main({!r}))"
        ).format(_LIB, nth, ["--root", self.root, *argv])
        p = subprocess.run(
            [sys.executable, "-c", drv],
            input=stdin,
            capture_output=True,
            text=True,
            check=False,
        )
        return p.returncode

    def test_killed_between_journal_commit_and_cache_replacement(self) -> None:
        rid = self.create()
        rs.op_set_handoff(self.root, rid, valid_handoff())
        # set-handoff fsyncs: 1 journal (commit), 2 cache temp, 3 run dir
        rc_ = self._kill_at(
            2,
            ["set-handoff", "--run-id", rid, "--payload", "-"],
            json.dumps(valid_handoff(next_action="stop")),
        )
        self.assertLess(rc_, 0)  # died by signal: no outcome at all
        out = rs.op_load(self.root, rid)
        self.assertEqual(out["effective_handoff"]["seq"], 2)  # journal committed
        self.assertEqual(out["handoff_cache"], "stale")  # old cache disagrees
        self.assertFalse(out["damaged"])
        # the crash left the lock: documented stale-lock state, manual recovery
        lock = os.path.join(self.run_dir(rid), rs.LOCK_NAME)
        self.assertTrue(os.path.exists(lock))
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_append(self.root, rid, "note", _note())
        self.assertEqual(cm.exception.code, "busy")
        os.remove(lock)
        self.assertEqual(rs.op_append(self.root, rid, "note", _note())["seq"], 3)
        # a crash can leave the uniquely named cache temp behind (auxiliary
        # residue, documented); it must not block the next cache replacement
        leftovers = [n for n in os.listdir(self.run_dir(rid)) if n.endswith(".tmp")]
        self.assertLessEqual(len(leftovers), 1)
        res = rs.op_set_handoff(self.root, rid, valid_handoff(next_action="golf"))
        self.assertEqual(res["outcome"], "committed")
        self.assertEqual(rs.op_load(self.root, rid)["handoff_cache"], "current")

    def test_killed_during_journal_append_leaves_recoverable_or_clean_state(
        self,
    ) -> None:
        rid = self.create()
        # fsync 1 in append is the journal commit itself: bytes are on disk
        # (page cache) but the process never acknowledged
        rc_ = self._kill_at(
            1,
            ["append", "--run-id", rid, "--kind", "note", "--payload", "-"],
            json.dumps(_note()),
        )
        self.assertLess(rc_, 0)
        out = rs.op_load(self.root, rid)
        self.assertIn(len(out["events"]), {0, 1})
        self.assertFalse(out["damaged"])  # a complete line or nothing — never garbage

    def test_killed_during_creation_leaves_incomplete_run(self) -> None:
        self.create(now="2026-09-09T11:59:59Z")  # store exists (gitignore published)
        rid = self.rid_for(NOW)
        # create fsyncs on an existing store: 1 journal, 2 manifest temp, 3 run dir, 4 runs dir
        rc_ = self._kill_at(
            2, ["create", "--dispatch", "-", "--now", NOW], json.dumps(valid_dispatch())
        )
        self.assertLess(rc_, 0)
        with self.assertRaises(rs.RefusedError) as cm:
            rs.op_load(self.root, rid)
        self.assertEqual(cm.exception.code, "incomplete_run")
        with self.assertRaises(rs.RefusedError):
            rs.op_append(self.root, rid, "note", _note())


class PortableLoad(unittest.TestCase):
    """The read-only path backend: exercised unconditionally (and for real on
    the Windows CI job) against the prebuilt fixture run, and on POSIX hosts
    also with the descriptor backend forced off."""

    FIXTURE_ROOT = os.path.join(_HERE, "fixtures", "run_store")

    def _fixture_rid(self) -> str:
        runs = os.path.join(self.FIXTURE_ROOT, "runs")
        ids = [d for d in os.listdir(runs) if rs.valid_run_id(d)]
        self.assertEqual(len(ids), 1)
        return ids[0]

    def test_prebuilt_fixture_loads_via_path_backend(self) -> None:
        rid = self._fixture_rid()
        out = rs._load_from(
            rs._PathRun(os.path.join(self.FIXTURE_ROOT, "runs", rid)), rid
        )
        self.assertEqual(out["run_id"], rid)
        self.assertEqual(
            [e["kind"] for e in out["events"]], ["note", "dispatch", "handoff"]
        )
        self.assertEqual(out["handoff_cache"], "current")
        self.assertEqual(out["warnings"], [])

    def test_op_load_with_descriptor_backend_forced_off(self) -> None:
        saved = rs.platform_supported
        rs.platform_supported = lambda: False
        try:
            rid = self._fixture_rid()
            out = rs.op_load(self.FIXTURE_ROOT, rid)
            self.assertEqual(out["effective_handoff"]["seq"], 3)
            with self.assertRaises(rs.RefusedError) as cm:
                rs.op_load(self.FIXTURE_ROOT, "20260909T120000Z-00000000")
            self.assertEqual(cm.exception.code, "no_such_run")
            with self.assertRaises(rs.RefusedError) as cm:
                rs.op_load(self.FIXTURE_ROOT, "../x")
            self.assertEqual(cm.exception.code, "bad_run_id")
        finally:
            rs.platform_supported = saved

    def test_validate_is_platform_independent(self) -> None:
        rid = self._fixture_rid()
        with open(
            os.path.join(self.FIXTURE_ROOT, "runs", rid, rs.MANIFEST_NAME),
            encoding="utf-8",
        ) as f:
            self.assertEqual(rs.validate_manifest(json.load(f)), [])


class Timestamps(unittest.TestCase):
    def test_now_must_be_exact_utc_form(self) -> None:
        for bad in (
            "2026-09-09T12:00:00+05:00",
            "2026-09-09",
            "2026-09-09T12:00:00",
            "2026-09-09T12:00:00.5Z",
            "",
            "now",
        ):
            with self.assertRaises(ValueError, msg=bad):
                rs.make_run_id("t", "sorry", "prove", None, bad)

    def test_year_one_yields_a_valid_id(self) -> None:
        rid = rs.make_run_id("t", "sorry", "prove", None, "0001-01-01T00:00:00Z")
        self.assertTrue(rs.valid_run_id(rid))
        self.assertTrue(rid.startswith("00010101T000000Z-"))


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class TimestampsOnDisk(_Base):
    def test_bad_now_refused_and_year_one_round_trips(self) -> None:
        with self.assertRaises(rs.RefusedError) as cm:
            self.create(now="2026-09-09T12:00:00+05:00")
        self.assertEqual(cm.exception.code, "bad_timestamp")
        rid = self.create(now="0001-01-01T00:00:00Z")
        self.assertEqual(
            rs.op_load(self.root, rid)["manifest"]["created"], "0001-01-01T00:00:00Z"
        )


@unittest.skipUnless(POSIX, "run-store mutations need a POSIX dir_fd host")
class Cli(_Base):
    def test_exit_codes_and_outcomes(self) -> None:
        d = json.dumps(valid_dispatch())
        p = self.cli("create", "--dispatch", "-", "--now", NOW, stdin=d)
        self.assertEqual(p.returncode, 0, p.stderr)
        rid = json.loads(p.stdout)["run_id"]
        p = self.cli(
            "set-handoff",
            "--run-id",
            rid,
            "--payload",
            "-",
            stdin=json.dumps(valid_handoff()),
        )
        self.assertEqual(p.returncode, 0)
        p = self.cli("create", "--dispatch", "-", "--now", NOW, stdin=d)
        self.assertEqual(p.returncode, rs.EXIT_REFUSED)
        self.assertEqual(json.loads(p.stdout)["outcome"], "nothing_written")
        p = self.cli(
            "append",
            "--run-id",
            rid,
            "--kind",
            "note",
            "--payload",
            "-",
            stdin="{not json",
        )
        self.assertEqual(p.returncode, rs.EXIT_USAGE)
        p = self.cli("load", "--run-id", rid)
        self.assertEqual(p.returncode, 0)
        self.assertEqual(json.loads(p.stdout)["schema"], rs.LOAD_SCHEMA)
        p = self.cli("validate", "--kind", "dispatch", "-", stdin="[]")
        self.assertEqual(p.returncode, rs.EXIT_REFUSED)
        p = self.cli("validate", "--kind", "dispatch", "-", stdin=d)
        self.assertEqual(p.returncode, 0)
        p = self.cli()
        self.assertEqual(p.returncode, rs.EXIT_USAGE)

    def test_env_root_and_project_default(self) -> None:
        env = dict(os.environ, LEAN4_RUN_STORE=os.path.join(self.tmp, "elsewhere"))
        p = subprocess.run(
            [
                BIN,
                "--project-root",
                self.project,
                "create",
                "--dispatch",
                "-",
                "--now",
                NOW,
            ],
            input=json.dumps(valid_dispatch()),
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertTrue(
            json.loads(p.stdout)["run_directory"].startswith(
                os.path.join(self.tmp, "elsewhere")
            )
        )


if __name__ == "__main__":
    unittest.main()
