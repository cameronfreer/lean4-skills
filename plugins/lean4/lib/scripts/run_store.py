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

Platform boundary (v3 spec): mutations (`create`, `append`, `set-handoff`) are
implemented for POSIX hosts whose `os` supports dir_fd on open/rename/mkdir/
unlink/stat (Linux, macOS). Elsewhere they exit 3 `unsupported_platform`
BEFORE touching the filesystem; `load` and `validate` work everywhere.

Containment: every path component under the storage root is opened relative
to its already-open parent directory fd with O_NOFOLLOW (which guards only the
final component of one open — hence one open per component), so a symlink
swapped in after any path check is still refused.

Durability, per operation:
  append       write loop until every byte is written (short writes retried),
               then fsync(journal); ack only after fsync.
  set-handoff  append (as above) → write+fsync temp → rename(dir_fd) →
               fsync(run dir).
  create       mkdir(run dir, exclusive) → create+fsync empty journal →
               write+fsync manifest.json.tmp → rename → fsync(run dir) →
               fsync(runs dir).
On macOS F_FULLFSYNC is attempted after fsync on file fds; its failure is an
`indeterminate` outcome, not ignored.

Write outcomes (exit codes): committed 0; refused/nothing_written 3;
journal_only 5; indeterminate 6. `journal_only` does not guarantee the next
`load` sees a stale cache (the rename may have landed before the directory
sync failed); a process killed after commit but before returning yields no
outcome at all. Callers reconcile with `load` before retrying — these are
honest outcomes, not exactly-once delivery.

Stdlib only; Python 3.10+.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
import re
import sys
from collections.abc import Callable
from datetime import datetime, timezone
from typing import Any

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_contract_validate as rc

MANIFEST_SCHEMA = "run-store-manifest/v1"
EVENT_SCHEMA = "run-store-event/v1"
HANDOFF_CACHE_SCHEMA = "run-store-handoff/v1"
LOAD_SCHEMA = "run-store-load/v1"
RESULT_SCHEMA = "run-store-result/v1"

EVENT_KINDS = {"dispatch", "handoff", "note"}
NOTE_KINDS = {
    "candidate",
    "failed-avenue",
    "search-result",
    "blocker-diagnosis",
    "definition-gap",
    "source-note",
}

RUN_ID_RE = re.compile(r"^[0-9]{8}T[0-9]{6}Z-[0-9a-f]{8}$")

MANIFEST_NAME = "manifest.json"
JOURNAL_NAME = "events.jsonl"
CACHE_NAME = "handoff.json"
LOCK_NAME = ".lock"
RUNS_DIRNAME = "runs"
STORE_DIRNAME = ".lean4-skills"

EXIT_OK = 0
EXIT_USAGE = 2
EXIT_REFUSED = 3
EXIT_JOURNAL_ONLY = 5
EXIT_INDETERMINATE = 6

# Indirections so fault-injection tests can fail exactly one step.
_write = os.write
_fsync = os.fsync
_rename = os.rename
_full_fsync_hook = None  # tests may set a callable(fd) to simulate F_FULLFSYNC


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


# --------------------------------------------------------------------------
# platform + paths
# --------------------------------------------------------------------------


def platform_supported() -> bool:
    need = {os.open, os.rename, os.mkdir, os.unlink, os.stat}
    return os.name == "posix" and need <= os.supports_dir_fd


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


def make_run_id(
    target: str, scope: str, mode: str, tracker_session_id: str | None, created: str
) -> str:
    h = hashlib.sha256(
        "|".join([target, scope, mode, tracker_session_id or "none", created]).encode(
            "utf-8"
        )
    ).hexdigest()[:8]
    stamp = datetime.fromisoformat(created.replace("Z", "+00:00")).strftime(
        "%Y%m%dT%H%M%SZ"
    )
    return f"{stamp}-{h}"


def _open_dir(name: str, dir_fd: int | None) -> int:
    flags = os.O_RDONLY | os.O_DIRECTORY | getattr(os, "O_NOFOLLOW", 0)
    return os.open(name, flags, dir_fd=dir_fd)


def _open_root(storage_root: str) -> int:
    """The configured root itself is opened by absolute path (it is the
    user's choice, symlink or not); everything BELOW it is opened per
    component with O_NOFOLLOW."""
    try:
        return os.open(storage_root, os.O_RDONLY | os.O_DIRECTORY)
    except OSError as ex:
        raise RefusedError("storage_root_unavailable", f"{storage_root}: {ex}") from ex


def _ensure_dir(name: str, dir_fd: int) -> int:
    """mkdir name under dir_fd if missing (EEXIST tolerated), then open it
    with O_NOFOLLOW — an existing symlink of that name is refused."""
    with contextlib.suppress(FileExistsError):
        os.mkdir(name, 0o755, dir_fd=dir_fd)
    try:
        return _open_dir(name, dir_fd)
    except OSError as ex:
        raise RefusedError(
            "containment", f"{name}: not a real directory ({ex})"
        ) from ex


def _fsync_all(fd: int, step: str) -> None:
    try:
        _fsync(fd)
    except OSError as ex:
        raise IndeterminateError(step, f"fsync failed: {ex}") from ex
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


def _write_file_atomic(dir_fd: int, name: str, data: bytes, step: str) -> None:
    """temp (O_EXCL) → write all → fsync → rename → fsync(dir)."""
    tmp = f"{name}.tmp"
    try:
        fd = os.open(
            tmp,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
            0o644,
            dir_fd=dir_fd,
        )
    except OSError as ex:
        raise RefusedError("temp_unavailable", f"{tmp}: {ex}") from ex
    try:
        _write_all(fd, data, step)
        _fsync_all(fd, step)
    finally:
        os.close(fd)
    try:
        _rename(tmp, name, src_dir_fd=dir_fd, dst_dir_fd=dir_fd)
    except OSError as ex:
        raise IndeterminateError(step, f"rename failed: {ex}") from ex
    _fsync_all(dir_fd, step)


# --------------------------------------------------------------------------
# lock
# --------------------------------------------------------------------------


class _Lock:
    """One mutation holds .lock in the run directory. Any existing lock blocks
    (busy) — contents are diagnostic only, never used to break a lock.
    Released on normal completion and handled failures; a crash may leave a
    stale lock (manual recovery: delete it with no store process running)."""

    def __init__(self, run_fd: int) -> None:
        self.run_fd = run_fd
        self.held = False

    def __enter__(self) -> _Lock:
        try:
            fd = os.open(
                LOCK_NAME,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
                0o644,
                dir_fd=self.run_fd,
            )
        except FileExistsError as ex:
            raise RefusedError("busy", "another store process holds .lock") from ex
        except OSError as ex:
            raise RefusedError("lock_unavailable", str(ex)) from ex
        info = {
            "pid": os.getpid(),
            "host": os.uname().nodename if hasattr(os, "uname") else None,
            "acquired": _now_iso(),
        }
        try:
            os.write(fd, (json.dumps(info) + "\n").encode("utf-8"))
        finally:
            os.close(fd)
        self.held = True
        return self

    def __exit__(self, *exc: Any) -> None:
        if self.held:
            with contextlib.suppress(OSError):
                os.unlink(LOCK_NAME, dir_fd=self.run_fd)
            self.held = False


# --------------------------------------------------------------------------
# journal reading (validated observed prefix)
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


def validate_event(obj: Any, expect_seq: int | None = None) -> list[str]:
    if not isinstance(obj, dict):
        return ["event must be a JSON object"]
    e: list[str] = []
    if set(obj) != {"schema", "seq", "ts", "kind", "payload"}:
        e.append("event must have exactly {schema, seq, ts, kind, payload}")
        return e
    if obj["schema"] != EVENT_SCHEMA:
        e.append(f"event schema must be {EVENT_SCHEMA}")
    if not rc._is_int(obj["seq"]) or obj["seq"] < 1:
        e.append("event seq must be a positive integer")
    elif expect_seq is not None and obj["seq"] != expect_seq:
        e.append(f"event seq {obj['seq']} but expected {expect_seq} (gap or duplicate)")
    if not rc._is_str(obj["ts"]):
        e.append("event ts must be a string")
    kind = obj["kind"]
    if not rc._in_enum(kind, EVENT_KINDS):
        e.append("event kind not in enum")
    elif kind == "dispatch":
        e += [f"dispatch payload: {m}" for m in rc.validate_dispatch(obj["payload"])]
    elif kind == "handoff":
        e += [f"handoff payload: {m}" for m in rc.validate_handoff(obj["payload"])]
    else:
        e += validate_note(obj["payload"])
    return e


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
    if set(obj) != want:
        e.append(f"manifest must have exactly {sorted(want)}")
        return e
    if obj["schema"] != MANIFEST_SCHEMA:
        e.append(f"manifest schema must be {MANIFEST_SCHEMA}")
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


def read_journal(run_fd: int) -> dict[str, Any]:
    """The validated observed prefix of events.jsonl.

    Captures the size at open and reads only through that boundary. Returns
    {events, warnings, damaged, next_seq}. `truncated_tail` (an unterminated
    final fragment) is recoverable and is NOT proof of a crashed writer — a
    concurrent append looks the same; `corrupt` (a terminated malformed line,
    schema-invalid event, seq gap or duplicate) is not. Nothing is rewritten.
    """
    try:
        fd = os.open(
            JOURNAL_NAME, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0), dir_fd=run_fd
        )
    except FileNotFoundError:
        return {
            "events": [],
            "warnings": [{"code": "journal_missing"}],
            "damaged": True,
            "next_seq": 1,
        }
    try:
        size = os.fstat(fd).st_size
        data = _read_exact(fd, size)
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
        errs = validate_event(obj, expect_seq=len(events) + 1)
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


def _read_json_file(run_fd: int, name: str) -> tuple[Any, str | None]:
    """(object, None) or (None, reason)."""
    try:
        fd = os.open(name, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0), dir_fd=run_fd)
    except FileNotFoundError:
        return None, "missing"
    except OSError as ex:
        return None, f"unreadable: {ex}"
    try:
        data = _read_exact(fd, os.fstat(fd).st_size)
    finally:
        os.close(fd)
    try:
        return json.loads(data.decode("utf-8")), None
    except (UnicodeDecodeError, json.JSONDecodeError) as ex:
        return None, f"malformed: {ex}"


# --------------------------------------------------------------------------
# operations
# --------------------------------------------------------------------------


def _now_iso() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


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


def _git_tracked_under(project_root: str, rel_dir: str) -> list[str]:
    """Paths under rel_dir already in the Git index (ignore rules never
    untrack). Empty when git is absent or the root is not a repository."""
    import subprocess

    try:
        out = subprocess.run(
            ["git", "-C", project_root, "ls-files", "-z", "--", rel_dir],
            capture_output=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return []
    if out.returncode != 0:
        return []
    return [p.decode("utf-8", "replace") for p in out.stdout.split(b"\0") if p]


def _open_runs(storage_root: str, create: bool) -> tuple[int, int]:
    """(root_fd, runs_fd). With create=True the directories are made."""
    if create:
        os.makedirs(storage_root, exist_ok=True)
    root_fd = _open_root(storage_root)
    try:
        if create:
            runs_fd = _ensure_dir(RUNS_DIRNAME, root_fd)
        else:
            try:
                runs_fd = _open_dir(RUNS_DIRNAME, root_fd)
            except OSError as ex:
                raise RefusedError("no_runs_dir", f"{storage_root}/runs: {ex}") from ex
    except BaseException:
        os.close(root_fd)
        raise
    return root_fd, runs_fd


def _open_run(runs_fd: int, run_id: str) -> int:
    if not valid_run_id(run_id):
        raise RefusedError("bad_run_id", "run id must match YYYYMMDDTHHMMSSZ-<8 hex>")
    try:
        return _open_dir(run_id, runs_fd)
    except OSError as ex:
        raise RefusedError("no_such_run", f"{run_id}: {ex}") from ex


def _ensure_gitignore(runs_fd: int) -> None:
    """runs/.gitignore containing '*' — ONLY if absent (user policy preserved)."""
    try:
        fd = os.open(
            ".gitignore",
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
            0o644,
            dir_fd=runs_fd,
        )
    except FileExistsError:
        return
    try:
        _write_all(fd, b"*\n", "gitignore")
        _fsync_all(fd, "gitignore")
    except IndeterminateError as ex:
        # No run exists yet, so this is a refusal, not an indeterminate run write.
        raise RefusedError("gitignore_write_failed", ex.detail) from ex
    finally:
        os.close(fd)


def op_create(
    dispatch: Any,
    *,
    storage_root: str,
    project_root: str,
    tracker_session_id: str | None,
    prior_run: str | None,
    now: str | None = None,
) -> dict[str, Any]:
    require_platform()
    errs = rc.validate_dispatch(dispatch)
    if errs:
        raise RefusedError("invalid_dispatch", "; ".join(errs))
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
    # Git index refusal: ignore rules never untrack an indexed file.
    rel = os.path.relpath(os.path.join(storage_root, RUNS_DIRNAME), project_root)
    if not rel.startswith(".."):
        tracked = _git_tracked_under(project_root, rel)
        if tracked:
            raise RefusedError(
                "git_tracked",
                f"{len(tracked)} path(s) under {rel} are in the Git index (e.g. {tracked[0]})",
            )
    root_fd, runs_fd = _open_runs(storage_root, create=True)
    try:
        _ensure_gitignore(runs_fd)
        # 1. exclusively reserve the run directory
        try:
            os.mkdir(run_id, 0o755, dir_fd=runs_fd)
        except FileExistsError as ex:
            raise RefusedError(
                "run_exists", f"{run_id} already exists (collision)"
            ) from ex
        run_fd = _open_dir(run_id, runs_fd)
        try:
            with _Lock(run_fd):
                # 2. empty journal, synchronized
                jfd = os.open(
                    JOURNAL_NAME,
                    os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
                    0o644,
                    dir_fd=run_fd,
                )
                try:
                    _fsync_all(jfd, "create.journal")
                finally:
                    os.close(jfd)
                # 3+4. manifest via temp → rename → fsync(run dir)
                manifest = {
                    "schema": MANIFEST_SCHEMA,
                    "run_id": run_id,
                    "created": created,
                    "plugin_version": _plugin_version(),
                    "storage_root": storage_root,
                    "tracker_session_id": tracker_session_id,
                    "prior_run": prior_run,
                    "dispatch": dispatch,
                }
                _write_file_atomic(
                    run_fd, MANIFEST_NAME, _dumps(manifest), "create.manifest"
                )
            # publication: the runs directory entry must persist too
            _fsync_all(runs_fd, "create.publish")
        finally:
            os.close(run_fd)
    finally:
        os.close(runs_fd)
        os.close(root_fd)
    return {
        "outcome": "committed",
        "run_id": run_id,
        "run_directory": os.path.join(storage_root, RUNS_DIRNAME, run_id),
    }


def _dumps(obj: Any) -> bytes:
    return (
        json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode("utf-8")


def _check_run_loadable(run_fd: int) -> dict[str, Any]:
    manifest, why = _read_json_file(run_fd, MANIFEST_NAME)
    if manifest is None:
        raise RefusedError("incomplete_run", f"manifest {why}")
    errs = validate_manifest(manifest)
    if errs:
        raise RefusedError("incomplete_run", "manifest invalid: " + "; ".join(errs))
    try:
        os.stat(JOURNAL_NAME, dir_fd=run_fd, follow_symlinks=False)
    except FileNotFoundError as ex:
        raise RefusedError(
            "integrity_failure", "manifest published but journal missing"
        ) from ex
    assert isinstance(manifest, dict)
    return manifest


def _append_locked(run_fd: int, kind: str, payload: Any) -> int:
    """Under the lock: re-read, refuse damage, append one event. Returns seq."""
    if kind == "dispatch":
        errs = rc.validate_dispatch(payload)
    elif kind == "handoff":
        errs = rc.validate_handoff(payload)
    elif kind == "note":
        errs = validate_note(payload)
    else:
        errs = ["event kind not in enum"]
    if errs:
        raise RefusedError("invalid_payload", "; ".join(errs))
    journal = read_journal(run_fd)
    if journal["damaged"]:
        raise RefusedError(
            "journal_damaged",
            "; ".join(f"{w['code']}@line {w.get('line')}" for w in journal["warnings"])
            + " — start a new run with prior_run set; repair is not a v1 operation",
        )
    seq = int(journal["next_seq"])
    event = {
        "schema": EVENT_SCHEMA,
        "seq": seq,
        "ts": _now_iso(),
        "kind": kind,
        "payload": payload,
    }
    line = _dumps(event)
    fd = os.open(
        JOURNAL_NAME,
        os.O_WRONLY | os.O_APPEND | getattr(os, "O_NOFOLLOW", 0),
        dir_fd=run_fd,
    )
    try:
        _write_all(fd, line, "append.write")
        _fsync_all(fd, "append.fsync")
    finally:
        os.close(fd)
    return seq


def _with_run(
    storage_root: str, run_id: str, fn: Callable[[int], dict[str, Any]]
) -> dict[str, Any]:
    root_fd, runs_fd = _open_runs(storage_root, create=False)
    try:
        run_fd = _open_run(runs_fd, run_id)
        try:
            return fn(run_fd)
        finally:
            os.close(run_fd)
    finally:
        os.close(runs_fd)
        os.close(root_fd)


def op_append(
    storage_root: str, run_id: str, kind: str, payload: Any
) -> dict[str, Any]:
    require_platform()

    def body(run_fd: int) -> dict[str, Any]:
        _check_run_loadable(run_fd)
        with _Lock(run_fd):
            seq = _append_locked(run_fd, kind, payload)
        return {"outcome": "committed", "run_id": run_id, "seq": seq}

    return _with_run(storage_root, run_id, body)


def op_set_handoff(storage_root: str, run_id: str, payload: Any) -> dict[str, Any]:
    require_platform()

    def body(run_fd: int) -> dict[str, Any]:
        _check_run_loadable(run_fd)
        with _Lock(run_fd):
            seq = _append_locked(run_fd, "handoff", payload)
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
    def body(run_fd: int) -> dict[str, Any]:
        manifest = _check_run_loadable(run_fd)
        journal = read_journal(run_fd)
        warnings = list(journal["warnings"])
        handoffs = [ev for ev in journal["events"] if ev["kind"] == "handoff"]
        effective = handoffs[-1] if handoffs else None
        cache, why = _read_json_file(run_fd, CACHE_NAME)
        cache_state = "absent"
        if why is None:
            cerrs = validate_cache(cache)
            if cerrs:
                cache_state = "stale"
                warnings.append(
                    {"code": "handoff_cache_stale", "detail": "; ".join(cerrs)}
                )
            elif effective is None:
                cache_state = "stale"
                warnings.append(
                    {
                        "code": "handoff_cache_stale",
                        "detail": "cache present but no handoff in the observed journal prefix",
                    }
                )
            elif (
                cache["seq"] != effective["seq"]
                or cache["payload"] != effective["payload"]
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
            "manifest": manifest,
            "events": journal["events"],
            "effective_handoff": effective,
            "handoff_cache": cache_state,
            "damaged": journal["damaged"],
            "warnings": warnings,
            "note": "validated observed prefix; historical evidence, not certification",
        }

    return _with_run(storage_root, run_id, body)


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def _read_payload(src: str) -> Any:
    try:
        if src == "-":
            data = sys.stdin.read()
        else:
            with open(src, encoding="utf-8") as f:
                data = f.read()
    except OSError as ex:
        raise RefusedError("payload_unreadable", f"{src}: {ex}") from ex
    if not data.strip():
        raise UsageError("empty payload")
    try:
        return json.loads(data)
    except json.JSONDecodeError as ex:
        raise UsageError(f"malformed JSON: {ex}") from ex


class UsageError(Exception):
    pass


def _emit(obj: dict[str, Any]) -> None:
    obj = {"schema": RESULT_SCHEMA, **obj}
    sys.stdout.write(json.dumps(obj, ensure_ascii=False, indent=2) + "\n")


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
    c.add_argument("--now", help="creation timestamp (ISO-8601 UTC); default now")
    a = sub.add_parser("append")
    a.add_argument("--run-id", required=True)
    a.add_argument("--kind", required=True, choices=sorted(EVENT_KINDS))
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
        choices=["manifest", "event", "dispatch", "handoff", "note", "cache"],
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
                "event": validate_event,
                "dispatch": rc.validate_dispatch,
                "handoff": rc.validate_handoff,
                "note": validate_note,
                "cache": validate_cache,
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


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
