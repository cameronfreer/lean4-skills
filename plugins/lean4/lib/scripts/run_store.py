#!/usr/bin/env python3
"""run-store/v1 — durable storage primitive for proving runs (#82A; Refs #82).

One directory per run:

    storage_root  = $LEAN4_RUN_STORE  or  <project-root>/.lean4-skills
    run_directory = storage_root/runs/<run-id>
        manifest.json   run-store-manifest/v1 — written once, immutable
        events.jsonl    run-store-event/v1 per line — append-only journal
        handoff.json    run-store-handoff/v1 — disposable latest-handoff cache
        .lock           writer lock (auxiliary); *.tmp temp files (auxiliary)

Manifest + journal are authoritative; the cache is a convenience view that the
journal always overrides. Payloads of `dispatch` / `handoff` events are the
unchanged run-contract/v1 records (validated by run_contract_validate.py);
storing a dispatch is NOT controller enforcement — the rerun guard is never
evaluated here. Stored snippets, handoffs and baselines are historical
evidence, never current certification: `load` changes no trust status.

Storage only. Command wiring, Replan updates, restart reconciliation,
/inspect, /resume are later work against #82.

Platform boundary (v3 spec): mutations (`create`, `append`, `set-handoff`)
are implemented for POSIX hosts whose `os` supports dir_fd on open/rename/
mkdir/unlink/stat/link (Linux, macOS). Elsewhere they exit 3
`unsupported_platform` BEFORE touching the filesystem. `load` and `validate`
work everywhere: on supported hosts `load` uses the same descriptor-relative
path as mutations; elsewhere it uses a portable READ-ONLY path-based backend
(best-effort symlink refusal by inspection, not race-proof — documented).

Containment (supported hosts): the storage root's PARENT is the user's
anchor (resolved with realpath, opened as given); the storage-root entry,
`runs`, `<run-id>` and every file are then opened relative to the already-open
parent descriptor with O_NOFOLLOW — which guards only the final component of
one open, hence one open per component — so a symlink swapped in after any
check is still refused.

Durability, per operation (fsync = fsync; F_FULLFSYNC on macOS for FILE
descriptors only):
  fresh store   mkdir storage_root → mkdir runs → fsync(storage_root) →
                fsync(parent of storage_root); then publish runs/.gitignore
                via temp + link (never overwriting an existing file).
  append        write loop until every byte is written (short writes
                retried), then fsync(journal); ack only after fsync.
  set-handoff   append (as above) → write+fsync unique temp → rename(dir_fd)
                → fsync(run dir).
  create        mkdir(run dir, exclusive) → create+fsync empty journal →
                write+fsync unique temp manifest → rename → fsync(run dir) →
                fsync(runs dir).

Write outcomes (exit codes): committed 0; refused/nothing_written 3;
journal_only 5; indeterminate 6. `journal_only` does not guarantee the next
`load` sees a stale cache (the rename may have landed before the directory
sync failed); a process killed after commit but before returning yields no
outcome at all; an unexpected OSError is reported as `indeterminate` (step
`unexpected`) rather than guessed at. Callers reconcile with `load` before
retrying — these are honest outcomes, not exactly-once delivery.

Stdlib only; Python 3.10+.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
import re
import secrets
import stat
import subprocess
import sys
from collections.abc import Callable
from datetime import datetime, timezone
from typing import Any

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_contract_validate as rc

MANIFEST_SCHEMA = "run-store-manifest/v1"
MANIFEST_SCHEMA_V2 = "run-store-manifest/v2"
EVENT_SCHEMA = "run-store-event/v1"
EVENT_SCHEMA_V2 = "run-store-event/v2"
REVIEW_RECORD_SCHEMA = "review-record/v1"
REPLAN_SUMMARY_SCHEMA = "replan-summary/v1"
HANDOFF_CACHE_SCHEMA = "run-store-handoff/v1"
LOAD_SCHEMA = "run-store-load/v1"
RESULT_SCHEMA = "run-store-result/v1"

EVENT_KINDS = {"dispatch", "handoff", "note"}
# run-store-event/v2 (#82B): the envelope is unchanged; the kind enum grows.
# A run is single-version — its manifest selects the event schema; a v2 kind
# in a v1 run is refused before writing and is corruption if found on disk.
EVENT_KINDS_V2 = EVENT_KINDS | {"review", "replan"}
EVENT_SCHEMAS = {EVENT_SCHEMA: EVENT_KINDS, EVENT_SCHEMA_V2: EVENT_KINDS_V2}
REVIEW_MODES = {"batch", "stuck"}
REVIEW_SOURCES = {"internal", "external", "both"}
REVIEW_STATUSES = {"completed", "skipped", "failed"}
CITE_RE = re.compile(r"^([0-9]{8}T[0-9]{6}Z-[0-9a-f]{8})#([1-9][0-9]*)$")
NOTE_KINDS = {
    "candidate",
    "failed-avenue",
    "search-result",
    "blocker-diagnosis",
    "definition-gap",
    "source-note",
}

RUN_ID_RE = re.compile(r"^[0-9]{8}T[0-9]{6}Z-[0-9a-f]{8}$")
TIMESTAMP_RE = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$")

MANIFEST_NAME = "manifest.json"
JOURNAL_NAME = "events.jsonl"
CACHE_NAME = "handoff.json"
LOCK_NAME = ".lock"
GITIGNORE_NAME = ".gitignore"
RUNS_DIRNAME = "runs"
STORE_DIRNAME = ".lean4-skills"

EXIT_OK = 0
EXIT_USAGE = 2
EXIT_REFUSED = 3
EXIT_JOURNAL_ONLY = 5
EXIT_INDETERMINATE = 6

_O_NOFOLLOW = getattr(os, "O_NOFOLLOW", 0)
_O_BINARY = getattr(os, "O_BINARY", 0)
_O_NONBLOCK = getattr(os, "O_NONBLOCK", 0)

# Indirections so fault-injection tests can fail exactly one step.
_write = os.write
_fsync = os.fsync
_rename = os.rename
_full_fsync_hook: Callable[[int], None] | None = None


class RefusedError(Exception):
    """Nothing was written; `code` names why."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


class IndeterminateError(Exception):
    """A write started (or durability could not be confirmed)."""

    def __init__(self, step: str, detail: str) -> None:
        super().__init__(f"indeterminate at {step}: {detail}")
        self.step = step
        self.detail = detail


class UsageError(Exception):
    pass


# --------------------------------------------------------------------------
# platform + identity
# --------------------------------------------------------------------------


def platform_supported() -> bool:
    need = {os.open, os.rename, os.mkdir, os.unlink, os.stat, os.link}
    return (
        os.name == "posix"
        and hasattr(os, "O_DIRECTORY")
        and hasattr(os, "O_NOFOLLOW")
        and need <= os.supports_dir_fd
    )


def require_platform() -> None:
    if not platform_supported():
        raise RefusedError(
            "unsupported_platform",
            "run-store mutations need a POSIX host with dir_fd support "
            "(Linux/macOS); load/validate work everywhere",
        )


def resolve_storage_root(project_root: str | None, explicit: str | None) -> str:
    if explicit:
        return os.path.abspath(explicit)
    env = os.environ.get("LEAN4_RUN_STORE")
    if env:
        return os.path.abspath(env)
    base = os.path.abspath(project_root or os.getcwd())
    return os.path.join(base, STORE_DIRNAME)


def valid_run_id(run_id: Any) -> bool:
    return isinstance(run_id, str) and RUN_ID_RE.fullmatch(run_id) is not None


def parse_timestamp(created: str) -> datetime:
    """Exactly `YYYY-MM-DDTHH:MM:SSZ` (UTC); anything else is rejected."""
    if not isinstance(created, str) or not TIMESTAMP_RE.fullmatch(created):
        raise ValueError("timestamp must be YYYY-MM-DDTHH:MM:SSZ (UTC)")
    return datetime.strptime(created, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)


def make_run_id(
    target: str, scope: str, mode: str, tracker_session_id: str | None, created: str
) -> str:
    dt = parse_timestamp(created)
    h = hashlib.sha256(
        "|".join([target, scope, mode, tracker_session_id or "none", created]).encode(
            "utf-8"
        )
    ).hexdigest()[:8]
    # zero-padded from components: strftime("%Y") is platform-dependent for
    # years < 1000 and would produce an id that fails the store's own regex.
    stamp = (
        f"{dt.year:04d}{dt.month:02d}{dt.day:02d}T"
        f"{dt.hour:02d}{dt.minute:02d}{dt.second:02d}Z"
    )
    rid = f"{stamp}-{h}"
    if not valid_run_id(rid):  # pragma: no cover — defensive
        raise ValueError(f"generated run id {rid!r} is malformed")
    return rid


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# --------------------------------------------------------------------------
# descriptor-relative filesystem helpers (supported hosts)
# --------------------------------------------------------------------------


def _open_dir(name: str, dir_fd: int | None) -> int:
    return os.open(name, os.O_RDONLY | os.O_DIRECTORY | _O_NOFOLLOW, dir_fd=dir_fd)


def _open_dir_contained(name: str, dir_fd: int, what: str) -> int:
    try:
        return _open_dir(name, dir_fd)
    except FileNotFoundError as ex:
        raise RefusedError(f"no_{what}", f"{name}: {ex}") from ex
    except OSError as ex:
        raise RefusedError(
            "containment", f"{what} {name!r}: not a real directory ({ex})"
        ) from ex


def _mkdir_if_missing(name: str, dir_fd: int) -> bool:
    """True when this call created it."""
    try:
        os.mkdir(name, 0o755, dir_fd=dir_fd)
    except FileExistsError:
        return False
    return True


def _fsync_all(fd: int, step: str, *, directory: bool = False) -> None:
    """fsync; on macOS additionally F_FULLFSYNC for FILE descriptors."""
    try:
        _fsync(fd)
    except OSError as ex:
        raise IndeterminateError(step, f"fsync failed: {ex}") from ex
    if directory:
        return
    if _full_fsync_hook is not None:
        try:
            _full_fsync_hook(fd)
        except OSError as ex:
            raise IndeterminateError(step, f"F_FULLFSYNC failed: {ex}") from ex
    elif sys.platform == "darwin":
        try:
            import fcntl

            fcntl.fcntl(fd, fcntl.F_FULLFSYNC)
        except OSError as ex:
            raise IndeterminateError(step, f"F_FULLFSYNC failed: {ex}") from ex


def _write_all(fd: int, data: bytes, step: str) -> None:
    """Loop on short writes. Failure after the first byte is indeterminate."""
    written = 0
    while written < len(data):
        try:
            n = _write(fd, data[written:])
        except OSError as ex:
            if written == 0:
                raise RefusedError("write_failed", f"{step}: {ex}") from ex
            raise IndeterminateError(
                step, f"partial write ({written}/{len(data)}): {ex}"
            ) from ex
        if n <= 0:
            raise IndeterminateError(step, f"write returned {n} after {written} bytes")
        written += n


def _temp_name(name: str) -> str:
    return f"{name}.{os.getpid()}.{secrets.token_hex(4)}.tmp"


def _write_temp(dir_fd: int, name: str, data: bytes, step: str) -> str:
    """Create a unique temp file beside `name`, write + fsync it; return its
    name. On failure the temp file is removed (best effort) before raising."""
    tmp = _temp_name(name)
    try:
        fd = os.open(
            tmp,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | _O_NOFOLLOW,
            0o644,
            dir_fd=dir_fd,
        )
    except OSError as ex:
        raise RefusedError("temp_unavailable", f"{tmp}: {ex}") from ex
    try:
        _write_all(fd, data, step)
        _fsync_all(fd, step)
    except BaseException:
        os.close(fd)
        with contextlib.suppress(OSError):
            os.unlink(tmp, dir_fd=dir_fd)
        raise
    os.close(fd)
    return tmp


def _write_file_atomic(dir_fd: int, name: str, data: bytes, step: str) -> None:
    """unique temp → write all → fsync → rename over `name` → fsync(dir).
    A failed rename removes the temp (best effort) so the next attempt is
    not blocked by a leftover."""
    tmp = _write_temp(dir_fd, name, data, step)
    try:
        _rename(tmp, name, src_dir_fd=dir_fd, dst_dir_fd=dir_fd)
    except OSError as ex:
        with contextlib.suppress(OSError):
            os.unlink(tmp, dir_fd=dir_fd)
        raise IndeterminateError(step, f"rename failed: {ex}") from ex
    _fsync_all(dir_fd, step, directory=True)


# --------------------------------------------------------------------------
# lock
# --------------------------------------------------------------------------


class _Lock:
    """One mutation holds .lock in the run directory. Any existing lock blocks
    (busy) — contents are diagnostic only, never used to break a lock.
    Released on normal completion and handled failures (including a failed
    initialization of the lock's own contents); a crash may leave a stale
    lock (manual recovery: delete it with no store process running)."""

    def __init__(self, run_fd: int) -> None:
        self.run_fd = run_fd
        self.held = False

    def __enter__(self) -> _Lock:
        try:
            fd = os.open(
                LOCK_NAME,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | _O_NOFOLLOW,
                0o644,
                dir_fd=self.run_fd,
            )
        except FileExistsError as ex:
            raise RefusedError("busy", "another store process holds .lock") from ex
        except OSError as ex:
            raise RefusedError("lock_unavailable", str(ex)) from ex
        self.held = True  # created by us: release on any failure below
        info = {
            "pid": os.getpid(),
            "host": os.uname().nodename if hasattr(os, "uname") else None,
            "acquired": _now_iso(),
        }
        try:
            _write_all(fd, (json.dumps(info) + "\n").encode("utf-8"), "lock")
        except (RefusedError, IndeterminateError) as ex:
            os.close(fd)
            self.__exit__()
            raise RefusedError("lock_init_failed", str(ex)) from ex
        os.close(fd)
        return self

    def __exit__(self, *exc: Any) -> None:
        if self.held:
            with contextlib.suppress(OSError):
                os.unlink(LOCK_NAME, dir_fd=self.run_fd)
            self.held = False


# --------------------------------------------------------------------------
# run handles: descriptor-relative (supported hosts) or path-based read-only
# --------------------------------------------------------------------------


class _FdRun:
    """Reads relative to an open run-directory descriptor with O_NOFOLLOW."""

    def __init__(self, run_fd: int) -> None:
        self.run_fd = run_fd

    def open_read(self, name: str) -> int:
        # O_NONBLOCK: opening a FIFO left in the run directory must not hang;
        # the regular-file check after open rejects it.
        return os.open(
            name, os.O_RDONLY | _O_NOFOLLOW | _O_NONBLOCK, dir_fd=self.run_fd
        )

    def exists(self, name: str) -> bool:
        try:
            os.stat(name, dir_fd=self.run_fd, follow_symlinks=False)
        except FileNotFoundError:
            return False
        return True


class _PathRun:
    """Portable READ-ONLY backend: plain paths. Symlinks are refused by
    inspection before each open (best effort, not race-proof) — this backend
    never mutates, so the exposure is limited to reading a swapped-in file."""

    def __init__(self, run_dir: str) -> None:
        self.run_dir = run_dir

    def _path(self, name: str) -> str:
        p = os.path.join(self.run_dir, name)
        if os.path.islink(p):
            raise OSError(f"{name}: symlink refused by the portable read-only backend")
        return p

    def open_read(self, name: str) -> int:
        return os.open(self._path(name), os.O_RDONLY | _O_BINARY)

    def exists(self, name: str) -> bool:
        return os.path.lexists(os.path.join(self.run_dir, name))


# --------------------------------------------------------------------------
# validation of stored shapes
# --------------------------------------------------------------------------


def validate_note(payload: Any) -> list[str]:
    if not rc._exact(
        payload,
        {
            "kind": lambda x: rc._in_enum(x, NOTE_KINDS),
            "text": rc._is_str,
            "lean": lambda x: x is None or rc._is_str(x),
        },
    ):
        return ["note payload must be {kind: <note kind>, text: str, lean: str|null}"]
    return []


def validate_review_record(payload: Any) -> list[str]:
    """review-record/v1 (#82B): one event per review the command ran, skipped,
    or failed. Combinations are explicit — a skipped review is never a
    fabricated success, and "completed" never implies edits were applied."""
    want = {
        "schema",
        "cycle",
        "mode",
        "target",
        "scope",
        "line",
        "source",
        "status",
        "output",
        "triage",
        "mapped_handoff",
        "detail",
    }
    if not isinstance(payload, dict) or set(payload) != want:
        return [f"review record must have exactly {sorted(want)}"]
    e: list[str] = []
    if payload["schema"] != REVIEW_RECORD_SCHEMA:
        e.append(f"review record schema must be {REVIEW_RECORD_SCHEMA}")
    if not rc._is_int(payload["cycle"]) or payload["cycle"] < 0:
        e.append("review record cycle must be a non-negative integer")
    if not rc._in_enum(payload["mode"], REVIEW_MODES):
        e.append("review record mode must be batch|stuck")
    if not rc._is_str(payload["target"]) or not rc._is_str(payload["scope"]):
        e.append("review record target/scope must be strings")
    if payload["line"] is not None and not rc._is_int(payload["line"]):
        e.append("review record line must be int|null")
    if not rc._in_enum(payload["source"], REVIEW_SOURCES):
        e.append("review record source must be internal|external|both")
    status = payload["status"]
    if not rc._in_enum(status, REVIEW_STATUSES):
        e.append("review record status must be completed|skipped|failed")
        return e
    out, tri, mh, detail = (
        payload["output"],
        payload["triage"],
        payload["mapped_handoff"],
        payload["detail"],
    )
    if detail is not None and not rc._is_str(detail):
        e.append("review record detail must be str|null")
    if out is not None:
        e += [f"review output: {m}" for m in _validate_review_output(out)]
    if tri is not None:
        e += [f"review triage: {m}" for m in _validate_triage(tri)]
    if mh is not None:
        e += [f"mapped_handoff: {m}" for m in rc.validate_handoff(mh)]
    if status == "completed":
        if payload["mode"] == "batch" and out is None:
            e.append("a completed batch review must carry its lean4-review-output/v2")
        if payload["mode"] == "stuck" and (tri is None or mh is None):
            e.append("a completed stuck review must carry triage and mapped_handoff")
        if payload["mode"] == "batch" and (tri is not None or mh is not None):
            e.append("a batch review carries no triage/mapped_handoff")
        # cross-field: a completed report is not a failed one
        if isinstance(out, dict) and out.get("error") is not None:
            e.append(
                "a completed review's output carries a non-null error — record it as status failed"
            )
        # cross-field: the mapped handoff wraps THIS triage of THIS target
        if isinstance(tri, dict) and isinstance(mh, dict) and not e:
            if mh.get("target") != payload["target"]:
                e.append("mapped_handoff.target must be the review's target")
            if mh.get("next_action") != tri.get("next_action"):
                e.append("mapped_handoff.next_action must equal triage.next_action")
            driven = mh.get("status") == "stuck" or (
                mh.get("status") == "stopped" and mh.get("stop_reason") == "max-stuck"
            )
            if not driven:
                e.append(
                    "a stuck review's mapped_handoff must be blocker-driven (stuck, or stopped/max-stuck)"
                )
            for k in ("blocker_class", "blocker_kind", "blocker_signature"):
                if mh.get(k) != tri.get(k):
                    e.append(f"mapped_handoff.{k} must equal triage.{k}")
    else:
        if out is not None or tri is not None or mh is not None:
            e.append(f"a {status} review carries no output/triage/mapped_handoff")
        if not (rc._is_str(detail) and detail):
            e.append(f"a {status} review must say why in detail")
    return e


def _validate_review_output(out: Any) -> list[str]:
    """The shipped lean4-review-output/v2 validator (production module)."""
    try:
        import review_validate
    except ImportError as ex:  # pragma: no cover
        return [f"review validator unavailable: {ex}"]
    try:
        res = review_validate.validate_output(out)
    except review_validate.SchemaUnavailableError as ex:  # pragma: no cover
        return [f"review schema unavailable: {ex}"]
    return list(res.errors) if not res.ok else []


def _validate_triage(tri: Any) -> list[str]:
    want = {
        "blocker_class",
        "blocker_kind",
        "blocker_signature",
        "next_action",
        "statement_may_be_false",
        "evidence",
    }
    if not isinstance(tri, dict) or set(tri) != want:
        return [f"triage must have exactly {sorted(want)}"]
    e: list[str] = []
    if tri["blocker_class"] is not None and not rc._in_enum(
        tri["blocker_class"], rc.BLOCKER_CLASSES
    ):
        e.append("triage blocker_class must be a Blocked-Goal Triage class or null")
    if tri["blocker_kind"] is not None and not rc._in_enum(
        tri["blocker_kind"], rc.BLOCKER_KINDS
    ):
        e.append("triage blocker_kind not in enum")
    if tri["blocker_signature"] is not None and not rc._is_str(
        tri["blocker_signature"]
    ):
        e.append("triage blocker_signature must be str|null")
    if not rc._in_enum(tri["next_action"], rc.NEXT_ACTIONS):
        e.append("triage next_action not in enum")
    if not isinstance(tri["statement_may_be_false"], bool):
        e.append("triage statement_may_be_false must be a boolean")
    ev = tri["evidence"]
    if not isinstance(ev, dict) or not (
        rc._str_list(ev.get("queries"))
        and rc._str_list(ev.get("top_candidates"))
        and rc._typed_dicts(
            ev.get("attempts"), {"snippet": rc._is_str, "result": rc._is_str}
        )
        and {"goal_delta", "diagnostic_delta"} <= set(ev)
        and (ev.get("goal_delta") is None or rc._is_str(ev.get("goal_delta")))
        and (
            ev.get("diagnostic_delta") is None or rc._is_str(ev.get("diagnostic_delta"))
        )
    ):
        e.append("triage evidence shape invalid")
    return e


def validate_replan_summary(payload: Any) -> list[str]:
    """replan-summary/v1 (#82B): one per cycle boundary. `cites` are
    `<run_id>#<seq>` references; the append path checks they resolve."""
    want = {
        "schema",
        "cycle",
        "plan",
        "failed_approaches",
        "blockers",
        "next_steps",
        "cites",
    }
    if not isinstance(payload, dict) or set(payload) != want:
        return [f"replan summary must have exactly {sorted(want)}"]
    e: list[str] = []
    if payload["schema"] != REPLAN_SUMMARY_SCHEMA:
        e.append(f"replan summary schema must be {REPLAN_SUMMARY_SCHEMA}")
    if not rc._is_int(payload["cycle"]) or payload["cycle"] < 1:
        e.append("replan summary cycle must be a positive integer")
    if not rc._is_str(payload["plan"]):
        e.append("replan summary plan must be a string")
    for k in ("failed_approaches", "next_steps", "cites"):
        if not rc._str_list(payload[k]):
            e.append(f"replan summary {k} must be an array of strings")
    if rc._str_list(payload["cites"]) and not all(
        CITE_RE.match(c) for c in payload["cites"]
    ):
        e.append("replan summary cites must be <run_id>#<seq> references")
    if not rc._typed_dicts(
        payload["blockers"],
        {
            "file": rc._is_str,
            "line": lambda x: x is None or rc._is_int(x),
            "blocker_class": lambda x: x is None or rc._in_enum(x, rc.BLOCKER_CLASSES),
            "blocker_signature": lambda x: x is None or rc._is_str(x),
        },
    ):
        e.append(
            "replan summary blockers items must be {file, line, blocker_class, blocker_signature}"
        )
    return e


def validate_event(
    obj: Any, expect_seq: int | None = None, event_schema: str = EVENT_SCHEMA
) -> list[str]:
    if not isinstance(obj, dict):
        return ["event must be a JSON object"]
    e: list[str] = []
    if set(obj) != {"schema", "seq", "ts", "kind", "payload"}:
        e.append("event must have exactly {schema, seq, ts, kind, payload}")
        return e
    if event_schema not in EVENT_SCHEMAS:
        return [f"unknown event schema {event_schema!r}"]
    if obj["schema"] != event_schema:
        e.append(
            f"event schema must be {event_schema} (this run's manifest selects it)"
        )
    if not rc._is_int(obj["seq"]) or obj["seq"] < 1:
        e.append("event seq must be a positive integer")
    elif expect_seq is not None and obj["seq"] != expect_seq:
        e.append(f"event seq {obj['seq']} but expected {expect_seq} (gap or duplicate)")
    if not rc._is_str(obj["ts"]):
        e.append("event ts must be a string")
    kind = obj["kind"]
    if not rc._in_enum(kind, EVENT_SCHEMAS[event_schema]):
        e.append(f"event kind not in enum for {event_schema}")
    else:
        e += validate_payload(kind, obj["payload"])
    return e


def validate_payload(kind: str, payload: Any) -> list[str]:
    if kind == "dispatch":
        return [f"dispatch payload: {m}" for m in rc.validate_dispatch(payload)]
    if kind == "handoff":
        return [f"handoff payload: {m}" for m in rc.validate_handoff(payload)]
    if kind == "note":
        return validate_note(payload)
    if kind == "review":
        return validate_review_record(payload)
    if kind == "replan":
        return validate_replan_summary(payload)
    return ["event kind not in enum"]


def validate_manifest(obj: Any) -> list[str]:
    if not isinstance(obj, dict):
        return ["manifest must be a JSON object"]
    e: list[str] = []
    want = {
        "schema",
        "run_id",
        "created",
        "plugin_version",
        "storage_root",
        "tracker_session_id",
        "prior_run",
        "dispatch",
    }
    schema = obj.get("schema")
    if schema == MANIFEST_SCHEMA_V2:
        # v2 REQUIRES event_schema; a v2 manifest without it is invalid, never
        # implicitly v1.
        want = want | {"event_schema"}
        if set(obj) != want:
            e.append(f"manifest v2 must have exactly {sorted(want)}")
            return e
        if obj["event_schema"] != EVENT_SCHEMA_V2:
            e.append(f"manifest v2 event_schema must be {EVENT_SCHEMA_V2}")
    else:
        if set(obj) != want:
            e.append(f"manifest must have exactly {sorted(want)}")
            return e
        if schema != MANIFEST_SCHEMA:
            e.append(
                f"manifest schema must be {MANIFEST_SCHEMA} or {MANIFEST_SCHEMA_V2}"
            )
    if not valid_run_id(obj["run_id"]):
        e.append("manifest run_id malformed")
    for k in ("created", "plugin_version", "storage_root"):
        if not rc._is_str(obj[k]):
            e.append(f"manifest {k} must be a string")
    if obj["tracker_session_id"] is not None and not rc._is_str(
        obj["tracker_session_id"]
    ):
        e.append("manifest tracker_session_id must be str|null")
    if obj["prior_run"] is not None and not valid_run_id(obj["prior_run"]):
        e.append("manifest prior_run must be a run id or null")
    e += [f"manifest dispatch: {m}" for m in rc.validate_dispatch(obj["dispatch"])]
    return e


def manifest_event_schema(manifest: dict[str, Any]) -> str:
    """The event schema a (validated) manifest selects: v1 implies event v1."""
    if manifest.get("schema") == MANIFEST_SCHEMA_V2:
        return str(manifest["event_schema"])
    return EVENT_SCHEMA


def validate_cache(obj: Any) -> list[str]:
    if not isinstance(obj, dict) or set(obj) != {"schema", "seq", "payload"}:
        return ["handoff cache must be {schema, seq, payload}"]
    e: list[str] = []
    if obj["schema"] != HANDOFF_CACHE_SCHEMA:
        e.append(f"handoff cache schema must be {HANDOFF_CACHE_SCHEMA}")
    if not rc._is_int(obj["seq"]) or obj["seq"] < 1:
        e.append("handoff cache seq must be a positive integer")
    e += [f"cache payload: {m}" for m in rc.validate_handoff(obj["payload"])]
    return e


# --------------------------------------------------------------------------
# reading (validated observed prefix)
# --------------------------------------------------------------------------


def _read_exact(fd: int, size: int) -> bytes:
    chunks: list[bytes] = []
    remaining = size
    while remaining > 0:
        b = os.read(fd, min(remaining, 1 << 20))
        if not b:
            break
        chunks.append(b)
        remaining -= len(b)
    return b"".join(chunks)


def read_journal(
    run: _FdRun | _PathRun, event_schema: str = EVENT_SCHEMA
) -> dict[str, Any]:
    """The validated observed prefix of events.jsonl.

    Captures the size at open and reads only through that boundary. Returns
    {events, warnings, damaged, next_seq}. `truncated_tail` (an unterminated
    final fragment) is recoverable and is NOT proof of a crashed writer — a
    concurrent append looks the same; `corrupt` (a terminated malformed line,
    schema-invalid event, seq gap or duplicate) is not. Nothing is rewritten.
    """
    try:
        fd = run.open_read(JOURNAL_NAME)
    except FileNotFoundError:
        return {
            "events": [],
            "warnings": [{"code": "journal_missing"}],
            "damaged": True,
            "next_seq": 1,
        }
    except OSError as ex:
        raise RefusedError("containment", f"{JOURNAL_NAME}: {ex}") from ex
    try:
        data = _read_regular(fd)  # size captured at open, read to that boundary
    except OSError as ex:
        raise RefusedError("journal_unreadable", f"{JOURNAL_NAME}: {ex}") from ex
    finally:
        os.close(fd)
    events: list[dict[str, Any]] = []
    warnings: list[dict[str, Any]] = []
    damaged = False
    lines = data.split(b"\n")
    tail = lines.pop()  # bytes after the last newline (b"" when terminated)
    for i, raw in enumerate(lines, start=1):
        try:
            obj = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as ex:
            warnings.append(
                {"code": "corrupt", "line": i, "detail": f"unparseable: {ex}"}
            )
            damaged = True
            break
        errs = validate_event(
            obj, expect_seq=len(events) + 1, event_schema=event_schema
        )
        if errs:
            warnings.append({"code": "corrupt", "line": i, "detail": "; ".join(errs)})
            damaged = True
            break
        events.append(obj)
    if tail and not damaged:
        warnings.append(
            {"code": "truncated_tail", "line": len(lines) + 1, "bytes": len(tail)}
        )
        damaged = True
    return {
        "events": events,
        "warnings": warnings,
        "damaged": damaged,
        "next_seq": len(events) + 1,
    }


def _read_regular(fd: int) -> bytes:
    """Whole contents of an open REGULAR file; anything else is an OSError."""
    st = os.fstat(fd)
    if not stat.S_ISREG(st.st_mode):
        raise OSError(f"not a regular file (mode {oct(st.st_mode)})")
    return _read_exact(fd, st.st_size)


def _read_json_file(run: _FdRun | _PathRun, name: str) -> tuple[Any, str | None]:
    """(object, None) or (None, reason) — every failure of the whole read is
    a reason, never an exception, so an unusable CACHE can only ever be
    reported stale (callers apply stricter treatment to the manifest)."""
    try:
        fd = run.open_read(name)
    except FileNotFoundError:
        return None, "missing"
    except OSError as ex:
        return None, f"unreadable: {ex}"
    try:
        data = _read_regular(fd)
    except OSError as ex:
        return None, f"unreadable: {ex}"
    finally:
        os.close(fd)
    try:
        return json.loads(data.decode("utf-8")), None
    except (UnicodeDecodeError, json.JSONDecodeError) as ex:
        return None, f"malformed: {ex}"


def _check_run_loadable(run: _FdRun | _PathRun, run_id: str) -> dict[str, Any]:
    manifest, why = _read_json_file(run, MANIFEST_NAME)
    if manifest is None:
        raise RefusedError("incomplete_run", f"manifest {why}")
    errs = validate_manifest(manifest)
    if errs:
        raise RefusedError("incomplete_run", "manifest invalid: " + "; ".join(errs))
    assert isinstance(manifest, dict)
    if manifest["run_id"] != run_id:
        raise RefusedError(
            "integrity_failure",
            f"manifest run_id {manifest['run_id']} does not match directory {run_id}",
        )
    if not run.exists(JOURNAL_NAME):
        raise RefusedError(
            "integrity_failure", "manifest published but journal missing"
        )
    return manifest


def _load_from(run: _FdRun | _PathRun, run_id: str) -> dict[str, Any]:
    manifest = _check_run_loadable(run, run_id)
    event_schema = manifest_event_schema(manifest)
    journal = read_journal(run, event_schema)
    warnings = list(journal["warnings"])
    handoffs = [ev for ev in journal["events"] if ev["kind"] == "handoff"]
    effective = handoffs[-1] if handoffs else None
    cache, why = _read_json_file(run, CACHE_NAME)
    cache_state = "absent"
    if why is None:
        cerrs = validate_cache(cache)
        if cerrs:
            cache_state = "stale"
            warnings.append({"code": "handoff_cache_stale", "detail": "; ".join(cerrs)})
        elif effective is None:
            cache_state = "stale"
            warnings.append(
                {
                    "code": "handoff_cache_stale",
                    "detail": "cache present but no handoff in the observed journal prefix",
                }
            )
        elif (
            cache["seq"] != effective["seq"] or cache["payload"] != effective["payload"]
        ):
            cache_state = "stale"
            warnings.append(
                {
                    "code": "handoff_cache_stale",
                    "detail": f"cache seq {cache['seq']} vs journal {effective['seq']}",
                }
            )
        else:
            cache_state = "current"
    elif why != "missing":
        cache_state = "stale"
        warnings.append({"code": "handoff_cache_stale", "detail": why})
    elif effective is not None:
        cache_state = "stale"
        warnings.append({"code": "handoff_cache_stale", "detail": "missing"})
    return {
        "schema": LOAD_SCHEMA,
        "run_id": run_id,
        "event_schema": event_schema,
        "manifest": manifest,
        "events": journal["events"],
        "effective_handoff": effective,
        "handoff_cache": cache_state,
        "damaged": journal["damaged"],
        "warnings": warnings,
        "note": "validated observed prefix; historical evidence, not certification",
    }


# --------------------------------------------------------------------------
# store layout (supported hosts)
# --------------------------------------------------------------------------


class _Store:
    """Open descriptors for parent → storage_root → runs. `resolved_root` is
    realpath(parent)/name — the path recorded in manifests."""

    def __init__(self, parent_fd: int, root_fd: int, runs_fd: int, resolved_root: str):
        self.parent_fd = parent_fd
        self.root_fd = root_fd
        self.runs_fd = runs_fd
        self.resolved_root = resolved_root

    def close(self) -> None:
        for fd in (self.runs_fd, self.root_fd, self.parent_fd):
            with contextlib.suppress(OSError):
                os.close(fd)


def _open_store(storage_root: str, create: bool) -> _Store:
    parent = os.path.realpath(os.path.dirname(storage_root))
    name = os.path.basename(storage_root)
    if not name or name in (".", ".."):
        raise RefusedError("bad_storage_root", f"{storage_root!r} has no usable name")
    # The parent is the user's anchor and must already exist: creating an
    # ancestor chain here would leave entries above the root unsynchronized.
    try:
        parent_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY)
    except OSError as ex:
        raise RefusedError(
            "no_parent_anchor",
            f"{parent}: the parent of the storage root must already exist ({ex})",
        ) from ex
    root_fd = runs_fd = -1
    try:
        if create:
            _mkdir_if_missing(name, parent_fd)
        root_fd = _open_dir_contained(name, parent_fd, "storage_root")
        if create:
            _mkdir_if_missing(RUNS_DIRNAME, root_fd)
        runs_fd = _open_dir_contained(RUNS_DIRNAME, root_fd, "runs_dir")
        # Store-initialization barriers, repeated on EVERY create: a directory
        # entry is durable only once its parent is synchronized, and the
        # entry's existence does not prove an earlier publication reached
        # disk (a previous create may have failed or died right here).
        if create:
            try:
                _fsync_all(root_fd, "store.init.runs", directory=True)
                _fsync_all(parent_fd, "store.init.root", directory=True)
            except IndeterminateError as ex:
                raise RefusedError("store_init_unsynced", ex.detail) from ex
    except BaseException:
        for fd in (runs_fd, root_fd, parent_fd):
            if fd >= 0:
                with contextlib.suppress(OSError):
                    os.close(fd)
        raise
    return _Store(parent_fd, root_fd, runs_fd, os.path.join(parent, name))


def _ensure_gitignore(runs_fd: int) -> None:
    """Publish runs/.gitignore containing '*' unless a file already exists.
    Written to a unique temp and LINKED into place: link() fails with EEXIST
    on an existing file, so user policy is never overwritten, and a failed
    initialization leaves no half-written .gitignore behind."""
    try:
        os.stat(GITIGNORE_NAME, dir_fd=runs_fd, follow_symlinks=False)
        return  # user policy (or an earlier publication) — preserved
    except FileNotFoundError:
        pass
    try:
        tmp = _write_temp(runs_fd, GITIGNORE_NAME, b"*\n", "gitignore")
    except (RefusedError, IndeterminateError) as ex:
        raise RefusedError("gitignore_write_failed", str(ex)) from ex
    try:
        try:
            os.link(tmp, GITIGNORE_NAME, src_dir_fd=runs_fd, dst_dir_fd=runs_fd)
        except FileExistsError:
            return  # raced with another publisher / user: keep theirs
        except OSError as ex:
            raise RefusedError("gitignore_write_failed", f"link: {ex}") from ex
        try:
            _fsync_all(runs_fd, "gitignore.publish", directory=True)
        except IndeterminateError as ex:
            raise RefusedError("gitignore_write_failed", ex.detail) from ex
    finally:
        with contextlib.suppress(OSError):
            os.unlink(tmp, dir_fd=runs_fd)


def _git_tracked_under(runs_dir: str) -> list[str]:
    """Paths under runs_dir already in the index of the repository that
    CONTAINS runs_dir (whichever repository that is). Empty when git is
    absent or no repository contains it."""
    anchor = runs_dir
    while not os.path.isdir(anchor):
        up = os.path.dirname(anchor)
        if up == anchor:
            return []
        anchor = up
    try:
        top = subprocess.run(
            ["git", "-C", anchor, "rev-parse", "--show-toplevel"],
            capture_output=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return []
    if top.returncode != 0:
        return []
    toplevel = top.stdout.decode("utf-8", "replace").strip()
    rel = os.path.relpath(os.path.realpath(runs_dir), os.path.realpath(toplevel))
    if rel.startswith(".."):
        return []
    try:
        out = subprocess.run(
            ["git", "-C", toplevel, "ls-files", "-z", "--", rel],
            capture_output=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return []
    if out.returncode != 0:
        return []
    return [p.decode("utf-8", "replace") for p in out.stdout.split(b"\0") if p]


def _open_run(runs_fd: int, run_id: str) -> int:
    if not valid_run_id(run_id):
        raise RefusedError("bad_run_id", "run id must match YYYYMMDDTHHMMSSZ-<8 hex>")
    return _open_dir_contained(run_id, runs_fd, "such_run")


def _with_run(
    storage_root: str, run_id: str, fn: Callable[[int, _Store], dict[str, Any]]
) -> dict[str, Any]:
    store = _open_store(storage_root, create=False)
    try:
        run_fd = _open_run(store.runs_fd, run_id)
        try:
            return fn(run_fd, store)
        finally:
            os.close(run_fd)
    finally:
        store.close()


# --------------------------------------------------------------------------
# operations
# --------------------------------------------------------------------------


def _dumps(obj: Any) -> bytes:
    return (
        json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode("utf-8")


def _plugin_version() -> str:
    here = os.path.dirname(os.path.abspath(__file__))
    p = os.path.join(
        os.path.dirname(os.path.dirname(here)), ".claude-plugin", "plugin.json"
    )
    try:
        with open(p, encoding="utf-8") as f:
            v = json.load(f).get("version")
        return str(v) if isinstance(v, str) else "unknown"
    except (OSError, ValueError):
        return "unknown"


def op_create(
    dispatch: Any,
    *,
    storage_root: str,
    project_root: str,
    tracker_session_id: str | None,
    prior_run: str | None,
    now: str | None = None,
    event_schema: str = EVENT_SCHEMA,
) -> dict[str, Any]:
    require_platform()
    if event_schema not in EVENT_SCHEMAS:
        raise RefusedError("bad_event_schema", f"unknown event schema {event_schema!r}")
    errs = rc.validate_dispatch(dispatch)
    if errs:
        raise RefusedError("invalid_dispatch", "; ".join(errs))
    _require_serializable(dispatch, "dispatch")
    if prior_run is not None and not valid_run_id(prior_run):
        raise RefusedError("bad_run_id", "prior_run must be a run id")
    created = now or _now_iso()
    try:
        run_id = make_run_id(
            dispatch["target"],
            dispatch["scope"],
            dispatch["mode"],
            tracker_session_id,
            created,
        )
    except ValueError as ex:
        raise RefusedError("bad_timestamp", str(ex)) from ex
    # Git index refusal, against the repository that CONTAINS the storage
    # location (not necessarily the project): ignore rules never untrack.
    tracked = _git_tracked_under(os.path.join(storage_root, RUNS_DIRNAME))
    if tracked:
        raise RefusedError(
            "git_tracked",
            f"{len(tracked)} path(s) under {storage_root}/runs are in the Git index "
            f"(e.g. {tracked[0]})",
        )
    store = _open_store(storage_root, create=True)
    try:
        # Preflight the COMPLETE manifest before reserving anything: the
        # resolved root can carry a surrogate-escaped (non-UTF-8) directory
        # name that the strict serializer would reject after the run
        # directory and empty journal already existed.
        manifest: dict[str, Any] = {
            "schema": MANIFEST_SCHEMA
            if event_schema == EVENT_SCHEMA
            else MANIFEST_SCHEMA_V2,
            "run_id": run_id,
            "created": created,
            "plugin_version": _plugin_version(),
            "storage_root": store.resolved_root,
            "tracker_session_id": tracker_session_id,
            "prior_run": prior_run,
            "dispatch": dispatch,
        }
        if event_schema != EVENT_SCHEMA:
            manifest["event_schema"] = event_schema
        _require_serializable(manifest, "manifest (storage_root or session id)")
        _ensure_gitignore(store.runs_fd)
        # 1. exclusively reserve the run directory
        if not _mkdir_if_missing(run_id, store.runs_fd):
            raise RefusedError("run_exists", f"{run_id} already exists (collision)")
        run_fd = _open_dir_contained(run_id, store.runs_fd, "such_run")
        try:
            with _Lock(run_fd):
                # 2. empty journal, synchronized
                jfd = os.open(
                    JOURNAL_NAME,
                    os.O_WRONLY | os.O_CREAT | os.O_EXCL | _O_NOFOLLOW,
                    0o644,
                    dir_fd=run_fd,
                )
                try:
                    _fsync_all(jfd, "create.journal")
                finally:
                    os.close(jfd)
                # 3+4. manifest via unique temp → rename → fsync(run dir)
                _write_file_atomic(
                    run_fd, MANIFEST_NAME, _dumps(manifest), "create.manifest"
                )
                # publication: the runs directory entry must persist too —
                # still under the lock, so no mutation can interleave
                _fsync_all(store.runs_fd, "create.publish", directory=True)
        finally:
            os.close(run_fd)
        run_directory = os.path.join(store.resolved_root, RUNS_DIRNAME, run_id)
    finally:
        store.close()
    return {"outcome": "committed", "run_id": run_id, "run_directory": run_directory}


def _append_locked(
    run_fd: int, kind: str, payload: Any, event_schema: str, run_id: str
) -> int:
    """Under the lock: re-read, refuse damage, append one event. Returns seq.
    The run's manifest selects the event schema; a kind the run's version does
    not know is refused BEFORE anything is written (the run stays valid)."""
    if not rc._in_enum(kind, EVENT_SCHEMAS[event_schema]):
        raise RefusedError(
            "kind_unsupported",
            f"event kind {kind!r} is not part of {event_schema}; this run stays "
            f"{event_schema} (never silently upgraded)",
        )
    errs = validate_payload(kind, payload)
    if errs:
        raise RefusedError("invalid_payload", "; ".join(errs))
    journal = read_journal(_FdRun(run_fd), event_schema)
    if journal["damaged"]:
        raise RefusedError(
            "journal_damaged",
            "; ".join(f"{w['code']}@line {w.get('line')}" for w in journal["warnings"])
            + " — start a new run with prior_run set; repair is not a v1 operation",
        )
    seq = int(journal["next_seq"])
    if kind == "replan":
        # cites must resolve to EARLIER events of THIS run
        for c in payload["cites"]:
            m = CITE_RE.match(c)
            if m is None or m.group(1) != run_id or int(m.group(2)) >= seq:
                raise RefusedError(
                    "invalid_payload",
                    f"replan cite {c!r} does not resolve to an earlier event of {run_id}",
                )
    event = {
        "schema": event_schema,
        "seq": seq,
        "ts": _now_iso(),
        "kind": kind,
        "payload": payload,
    }
    line = _dumps(event)
    try:
        fd = os.open(
            JOURNAL_NAME, os.O_WRONLY | os.O_APPEND | _O_NOFOLLOW, dir_fd=run_fd
        )
    except OSError as ex:
        raise RefusedError("containment", f"{JOURNAL_NAME}: {ex}") from ex
    try:
        _write_all(fd, line, "append.write")
        _fsync_all(fd, "append.fsync")
    finally:
        os.close(fd)
    return seq


def _publish_barriers(run_fd: int, runs_fd: int) -> None:
    """Under the mutation lock, before accepting a journal mutation: make the
    run's directory entries durable. A loadable run may have been left by a
    `create` that failed or died at its last barriers, and synchronizing the
    journal's contents does not make the entries needed to REACH it durable.
    Nothing has been written yet, so a failure here is a refusal."""
    try:
        _fsync_all(run_fd, "mutate.publish.run", directory=True)
        _fsync_all(runs_fd, "mutate.publish.runs", directory=True)
    except IndeterminateError as ex:
        raise RefusedError("publish_unsynced", ex.detail) from ex


def _require_serializable(payload: Any, what: str) -> None:
    """Reject payloads the strict UTF-8 serializer cannot write (an unpaired
    surrogate passes the structural string checks) BEFORE any filesystem
    change."""
    try:
        _dumps(payload)
    except UnicodeEncodeError as ex:
        raise RefusedError(
            "invalid_payload", f"{what} is not UTF-8 serializable: {ex}"
        ) from ex


def op_append(
    storage_root: str, run_id: str, kind: str, payload: Any
) -> dict[str, Any]:
    require_platform()
    _require_serializable(payload, "payload")

    def body(run_fd: int, store: _Store) -> dict[str, Any]:
        manifest = _check_run_loadable(_FdRun(run_fd), run_id)
        es = manifest_event_schema(manifest)
        with _Lock(run_fd):
            _publish_barriers(run_fd, store.runs_fd)
            seq = _append_locked(run_fd, kind, payload, es, run_id)
        return {"outcome": "committed", "run_id": run_id, "seq": seq}

    return _with_run(storage_root, run_id, body)


def op_set_handoff(storage_root: str, run_id: str, payload: Any) -> dict[str, Any]:
    require_platform()
    _require_serializable(payload, "payload")

    def body(run_fd: int, store: _Store) -> dict[str, Any]:
        manifest = _check_run_loadable(_FdRun(run_fd), run_id)
        es = manifest_event_schema(manifest)
        with _Lock(run_fd):
            _publish_barriers(run_fd, store.runs_fd)
            seq = _append_locked(run_fd, "handoff", payload, es, run_id)
            cache = {"schema": HANDOFF_CACHE_SCHEMA, "seq": seq, "payload": payload}
            try:
                _write_file_atomic(run_fd, CACHE_NAME, _dumps(cache), "cache")
            except (RefusedError, IndeterminateError) as ex:
                return {
                    "outcome": "journal_only",
                    "run_id": run_id,
                    "seq": seq,
                    "detail": str(ex),
                }
        return {"outcome": "committed", "run_id": run_id, "seq": seq}

    return _with_run(storage_root, run_id, body)


def op_load(storage_root: str, run_id: str) -> dict[str, Any]:
    if platform_supported():
        return _with_run(
            storage_root, run_id, lambda fd, _store: _load_from(_FdRun(fd), run_id)
        )
    # Portable read-only backend.
    if not valid_run_id(run_id):
        raise RefusedError("bad_run_id", "run id must match YYYYMMDDTHHMMSSZ-<8 hex>")
    runs_dir = os.path.join(os.path.abspath(storage_root), RUNS_DIRNAME)
    run_dir = os.path.join(runs_dir, run_id)
    for p, what in (
        (os.path.abspath(storage_root), "storage_root"),
        (runs_dir, "runs_dir"),
        (run_dir, "such_run"),
    ):
        if os.path.islink(p):
            raise RefusedError("containment", f"{what} {p!r} is a symlink")
        if not os.path.isdir(p):
            raise RefusedError(f"no_{what}", f"{p}: not a directory")
    return _load_from(_PathRun(run_dir), run_id)


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def _read_payload(src: str) -> Any:
    try:
        if src == "-":
            stream = getattr(sys.stdin, "buffer", None)
            raw = stream.read() if stream is not None else sys.stdin.read().encode()
        else:
            with open(src, "rb") as f:
                raw = f.read()
    except OSError as ex:
        raise RefusedError("payload_unreadable", f"{src}: {ex}") from ex
    try:
        data = raw.decode("utf-8")  # payloads are UTF-8 regardless of the console
    except UnicodeDecodeError as ex:
        raise UsageError(f"payload is not UTF-8: {ex}") from ex
    if not data.strip():
        raise UsageError("empty payload")
    try:
        return json.loads(data)
    except json.JSONDecodeError as ex:
        raise UsageError(f"malformed JSON: {ex}") from ex


def _emit(obj: dict[str, Any]) -> None:
    """Always UTF-8 bytes: a cp1252 console (native Windows) cannot encode
    Lean goals such as `⊢`, and a text-mode write would raise after the
    operation already succeeded."""
    obj = {"schema": RESULT_SCHEMA, **obj}
    # backslashreplace: a lone surrogate in hand-edited stored data must not
    # crash the report of an operation that already happened.
    out = (json.dumps(obj, ensure_ascii=False, indent=2) + "\n").encode(
        "utf-8", "backslashreplace"
    )
    stream = getattr(sys.stdout, "buffer", None)
    if stream is None:  # pragma: no cover — replaced stdout without a buffer
        sys.stdout.write(out.decode("utf-8", "replace"))
    else:
        stream.write(out)
    sys.stdout.flush()


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        prog="lean4-skills-run-store", description=__doc__.split("\n\n")[0]
    )
    ap.add_argument(
        "--root",
        help="explicit storage root (overrides LEAN4_RUN_STORE and --project-root)",
    )
    ap.add_argument(
        "--project-root", help="project root; default cwd → <root>/.lean4-skills"
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("create")
    c.add_argument(
        "--dispatch", required=True, help="run-contract/v1 dispatch JSON file or -"
    )
    c.add_argument("--tracker-session-id")
    c.add_argument("--prior-run")
    c.add_argument(
        "--now", help="creation timestamp, exactly YYYY-MM-DDTHH:MM:SSZ; default now"
    )
    c.add_argument(
        "--event-schema",
        choices=sorted(EVENT_SCHEMAS),
        default=EVENT_SCHEMA,
        help="event schema for this run (manifest v2 ⇔ run-store-event/v2)",
    )
    a = sub.add_parser("append")
    a.add_argument("--run-id", required=True)
    a.add_argument("--kind", required=True, choices=sorted(EVENT_KINDS_V2))
    a.add_argument("--payload", required=True)
    h = sub.add_parser("set-handoff")
    h.add_argument("--run-id", required=True)
    h.add_argument("--payload", required=True)
    ld = sub.add_parser("load")
    ld.add_argument("--run-id", required=True)
    v = sub.add_parser("validate")
    v.add_argument(
        "--kind",
        required=True,
        choices=[
            "manifest",
            "event",
            "dispatch",
            "handoff",
            "note",
            "cache",
            "review",
            "replan",
        ],
    )
    v.add_argument("file")
    try:
        ns = ap.parse_args(argv)
    except SystemExit as ex:
        return EXIT_USAGE if ex.code else EXIT_OK
    project_root = os.path.abspath(ns.project_root or os.getcwd())
    storage_root = resolve_storage_root(project_root, ns.root)
    try:
        if ns.cmd == "validate":
            obj = _read_payload(ns.file)
            fn = {
                "manifest": validate_manifest,
                "event": lambda o: validate_event(
                    o,
                    event_schema=(
                        o["schema"]
                        if isinstance(o, dict)
                        and isinstance(o.get("schema"), str)
                        and o.get("schema") in EVENT_SCHEMAS
                        else EVENT_SCHEMA
                    ),
                ),
                "dispatch": rc.validate_dispatch,
                "handoff": rc.validate_handoff,
                "note": validate_note,
                "cache": validate_cache,
                "review": validate_review_record,
                "replan": validate_replan_summary,
            }[ns.kind]
            errs = fn(obj)
            _emit(
                {
                    "outcome": "ok" if not errs else "invalid",
                    "kind": ns.kind,
                    "errors": errs,
                }
            )
            return EXIT_OK if not errs else EXIT_REFUSED
        if ns.cmd == "create":
            res = op_create(
                _read_payload(ns.dispatch),
                storage_root=storage_root,
                project_root=project_root,
                tracker_session_id=ns.tracker_session_id,
                prior_run=ns.prior_run,
                now=ns.now,
                event_schema=ns.event_schema,
            )
        elif ns.cmd == "append":
            res = op_append(storage_root, ns.run_id, ns.kind, _read_payload(ns.payload))
        elif ns.cmd == "set-handoff":
            res = op_set_handoff(storage_root, ns.run_id, _read_payload(ns.payload))
        else:
            res = op_load(storage_root, ns.run_id)
            _emit(res)
            return EXIT_OK
        _emit(res)
        return {"committed": EXIT_OK, "journal_only": EXIT_JOURNAL_ONLY}[res["outcome"]]
    except UsageError as ex:
        _emit({"outcome": "nothing_written", "code": "usage", "detail": str(ex)})
        return EXIT_USAGE
    except RefusedError as ex:
        _emit({"outcome": "nothing_written", "code": ex.code, "detail": ex.detail})
        return EXIT_REFUSED
    except IndeterminateError as ex:
        _emit({"outcome": "indeterminate", "step": ex.step, "detail": ex.detail})
        return EXIT_INDETERMINATE
    except OSError as ex:
        # Not a blanket "nothing written": the journal may or may not have
        # changed, so say so and let the caller reconcile with `load`.
        _emit(
            {
                "outcome": "indeterminate",
                "step": "unexpected",
                "detail": f"{type(ex).__name__}: {ex}",
            }
        )
        return EXIT_INDETERMINATE


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
