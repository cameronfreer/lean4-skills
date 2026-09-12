#!/usr/bin/env python3
"""run-persist — the proving commands' persistence protocol over run-store (#82B).

`prove` and `autoprove` (with `--persist`) drive this helper instead of calling
the store directly, so the failure policy is deterministic code rather than
prose the model must re-implement each time:

    start    create the run (manifest v2 / event v2) after inputs, capability
             checks and a valid first dispatch — before any proof edit
    dispatch / handoff / note / review / replan
             append one event; the parent/controller is the sole writer
    finish   set the run's final handoff (terminal)
    status   show the invocation state

Every command prints one `run-persist-result/v1` object with an `action`:

    continue       the event is committed: go on
    stop           persistence failed, is uncertain, or its bookkeeping could
                   not be completed: STOP further proof work and emit the
                   operational-error handoff carried in the result
    startup-error  `start` could not create the run: do not start the command
    done           `finish` completed; `stored` says whether the handoff was
                   actually persisted — a fallback is never claimed as saved
    usage          the helper could not run at all (nothing was attempted)

Policy (references/cycle-engine.md § Run Persistence):
  committed       → continue
  journal_only    → (finish only) done, stored, with a warning; NEVER re-append
  busy            → one bounded retry after 1 s; never break the lock
  other refusal   → stop (operational-error, stop_detail names the code)
  indeterminate   → stop; an event visible to `load` is not evidence of a
                    durable commit, so no retry and no inferred success
  no / malformed / contradictory store result → stop, as uncertain

Invocation state (`--state FILE`, or $LEAN4_RUN_PERSIST_STATE) is CONTROL
state, not a run-id cache:
  * `start` creates it exclusively — an existing file is refused;
  * it binds the storage root and run id for the invocation — later calls use
    the bound root (a different --root is refused);
  * every mutation is recorded as in-flight BEFORE the store is invoked and
    resolved afterwards; if the resolution cannot be recorded (or the process
    dies in between), the next call finds the unresolved operation and stops —
    a state-write failure never suppresses the store's own outcome or the
    fallback report, and never lets the run continue;
  * `finish` and a policy stop are terminal: later mutations return `stop`
    without touching the store.
The state also carries the CURRENT parent context (target/scope/mode and
ownership from the latest persisted dispatch; files changed, baseline and
evidence accumulated from persisted worker handoffs and notes), so the
operational-error handoff emitted on a stop reports the work as it stands,
never the first dispatch with "no changes".

Exit codes: 0 continue/done(stored); 2 usage; 3 startup-error;
5 stop / done(not stored).
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from typing import Any

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run_contract_validate as rc  # noqa: E402

STORE = os.path.join(HERE, "run_store.py")
RESULT_SCHEMA = "run-persist-result/v1"
STATE_SCHEMA = "run-persist-state/v1"
STORE_RESULT_SCHEMA = "run-store-result/v1"
EVENT_SCHEMA_V2 = "run-store-event/v2"

EXIT_OK = 0
EXIT_USAGE = 2
EXIT_STARTUP = 3
EXIT_STOP = 5

# Store exit codes (run_store.py) an acknowledgment must agree with.
_STORE_EXIT = {
    "committed": 0,
    "nothing_written": 3,
    "journal_only": 5,
    "indeterminate": 6,
}

# Injection point for in-process tests (a fake store CLI).
_STORE_ARGV: list[str] | None = None


class UsageError(Exception):
    pass


def _store_argv() -> list[str]:
    if _STORE_ARGV is not None:
        return list(_STORE_ARGV)
    env = os.environ.get("LEAN4_RUN_STORE_ARGV")  # tests: a fake store CLI
    if env:
        argv = json.loads(env)
        if isinstance(argv, list) and all(isinstance(a, str) for a in argv):
            return argv
    return [sys.executable, STORE]


def _run_store(
    args: list[str], stdin: bytes | None, root: str
) -> tuple[int | None, Any, str]:
    """(exit code | None if the process yielded no result, parsed stdout | None, stderr)."""
    try:
        p = subprocess.run(
            [*_store_argv(), "--root", root, *args],
            input=stdin,
            capture_output=True,
            check=False,
            timeout=120,
        )
    except (OSError, subprocess.SubprocessError) as ex:
        return None, None, f"store process failed: {ex}"
    try:
        res = json.loads(p.stdout.decode("utf-8"))
    except (UnicodeDecodeError, ValueError):
        res = None
    return p.returncode, res, p.stderr.decode("utf-8", "replace")


def _emit(obj: dict[str, Any]) -> None:
    out = (
        json.dumps({"schema": RESULT_SCHEMA, **obj}, ensure_ascii=False, indent=2)
        + "\n"
    ).encode("utf-8", "backslashreplace")
    sys.stdout.buffer.write(out)
    sys.stdout.flush()


# --------------------------------------------------------------------------
# acknowledgment validation
# --------------------------------------------------------------------------


def _classify(
    code: int | None, res: Any, stderr: str, *, expect_run_id: str | None
) -> tuple[str, str, dict[str, Any] | None]:
    """(outcome, detail, result). `outcome` ∈ committed / journal_only /
    indeterminate / refused:<code> / malformed. Anything the store did not
    acknowledge in a well-formed, exit-consistent, operation-appropriate
    result is `malformed` — treated as uncertain, never as success."""
    if code is None or not isinstance(res, dict):
        return (
            "malformed",
            stderr.strip() or "the store process yielded no result",
            None,
        )
    if res.get("schema") != STORE_RESULT_SCHEMA:
        return "malformed", f"store result has schema {res.get('schema')!r}", None
    outcome = res.get("outcome")
    if not isinstance(outcome, str) or outcome not in _STORE_EXIT:
        return "malformed", f"store result outcome {outcome!r}", None
    if code != _STORE_EXIT[outcome] and not (
        outcome == "nothing_written" and code == 2
    ):
        return "malformed", f"store exit {code} contradicts outcome {outcome!r}", None
    if outcome in ("committed", "journal_only"):
        seq, rid = res.get("seq"), res.get("run_id")
        if expect_run_id is not None:
            if not (isinstance(seq, int) and not isinstance(seq, bool) and seq >= 1):
                return "malformed", f"store result seq {seq!r}", None
            if rid != expect_run_id:
                return (
                    "malformed",
                    f"store result run_id {rid!r} is not {expect_run_id}",
                    None,
                )
        elif not (isinstance(rid, str) and isinstance(res.get("run_directory"), str)):
            return "malformed", "store create result lacks run_id/run_directory", None
        if outcome == "journal_only":
            return "journal_only", str(res.get("detail", "")), res
        return "committed", "", res
    if outcome == "indeterminate":
        return (
            "indeterminate",
            f"run-store indeterminate at {res.get('step')}: {res.get('detail')}",
            res,
        )
    return (
        f"refused:{res.get('code')}",
        f"run-store {res.get('code')}: {res.get('detail')}",
        res,
    )


# --------------------------------------------------------------------------
# state
# --------------------------------------------------------------------------


def _load_state(path: str) -> dict[str, Any]:
    try:
        with open(path, "rb") as f:
            st = json.loads(f.read().decode("utf-8"))
    except FileNotFoundError as ex:
        raise UsageError(f"no invocation state at {path}: run `start` first") from ex
    except (OSError, ValueError) as ex:
        raise UsageError(f"invocation state unreadable: {ex}") from ex
    if not isinstance(st, dict) or st.get("schema") != STATE_SCHEMA:
        raise UsageError("state file is not run-persist-state/v1")
    return st


def _save_state(path: str, st: dict[str, Any], *, exclusive: bool = False) -> None:
    """Atomic replace; with exclusive=True the destination must not exist."""
    data = (json.dumps(st, indent=2) + "\n").encode("utf-8")
    if exclusive:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
        try:
            os.write(fd, data)
            os.fsync(fd)
        finally:
            os.close(fd)
        return
    tmp = f"{path}.{os.getpid()}.tmp"
    with open(tmp, "wb") as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def _try_save(path: str, st: dict[str, Any]) -> str | None:
    """None on success, else the failure text. Never raises."""
    try:
        _save_state(path, st)
    except OSError as ex:
        return f"{type(ex).__name__}: {ex}"
    return None


def _context_from_dispatch(d: dict[str, Any]) -> dict[str, Any]:
    return {
        "target": d["target"],
        "scope": d["scope"],
        "mode": d["mode"],
        "files_owned": list(d["owned_files"]),
        "file_baseline": d["file_baseline"],
    }


def _new_state(
    root: str, run_id: str, run_directory: str, dispatch: dict[str, Any]
) -> dict[str, Any]:
    return {
        "schema": STATE_SCHEMA,
        "run_id": run_id,
        "run_directory": run_directory,
        "storage_root": root,
        "current": _context_from_dispatch(dispatch),
        "files_changed": [],
        "attempted_tools": [],
        "best_candidates": [],
        "failed_avenues": [],
        "evidence": {
            "queries": [],
            "top_candidates": [],
            "attempts": [],
            "goal_delta": None,
            "diagnostic_delta": None,
        },
        "last_seq": 0,
        "inflight": None,
        "stopped": None,
        "finished": None,
    }


def _absorb(st: dict[str, Any], kind: str, payload: dict[str, Any]) -> None:
    """Fold an event into the parent context (committed history when called
    on the real state; parent KNOWLEDGE when called on a copy with a pending,
    unpersisted submission — see `_knowledge`)."""
    if kind == "dispatch":
        st["current"] = _context_from_dispatch(payload)
    elif kind == "handoff":
        for f in payload["files_changed"]:
            if f not in st["files_changed"]:
                st["files_changed"].append(f)
        if payload.get("file_baseline") is not None:
            st["current"]["file_baseline"] = payload["file_baseline"]
        for k in ("attempted_tools", "failed_avenues"):
            for x in payload[k]:
                if x not in st[k]:
                    st[k].append(x)
        st["best_candidates"].extend(payload["best_candidates"])
        ev = payload["evidence"]
        for k in ("queries", "top_candidates"):
            for x in ev[k]:
                if x not in st["evidence"][k]:
                    st["evidence"][k].append(x)
        st["evidence"]["attempts"].extend(ev["attempts"])
        st.setdefault("artifacts", []).extend(payload.get("artifacts", []))
        if ev.get("goal_delta") is not None:
            st["evidence"]["goal_delta"] = ev["goal_delta"]
        if ev.get("diagnostic_delta") is not None:
            st["evidence"]["diagnostic_delta"] = ev["diagnostic_delta"]
    elif (
        kind == "note"
        and payload.get("kind") == "failed-avenue"
        and payload["text"] not in st["failed_avenues"]
    ):
        st["failed_avenues"].append(payload["text"])


def _valid_submission(kind: str, payload: Any) -> bool:
    if kind == "dispatch":
        return not rc.validate_dispatch(payload)
    if kind == "handoff":
        return not rc.validate_handoff(payload)
    if kind == "note":
        return rc._exact(
            payload,
            {
                "kind": rc._is_str,
                "text": rc._is_str,
                "lean": lambda x: x is None or rc._is_str(x),
            },
        )
    return False


def _knowledge(st: dict[str, Any]) -> dict[str, Any]:
    """Current parent knowledge = committed history + the validated submission
    of an unresolved / failed operation (`inflight.pending`), which describes
    work that HAPPENED even though its journal write did not commit."""
    k: dict[str, Any] = json.loads(json.dumps(st))
    pend = (st.get("inflight") or {}).get("pending")
    if isinstance(pend, dict) and pend.get("kind") in ("dispatch", "handoff", "note"):
        _absorb(k, str(pend["kind"]), pend["payload"])
    return k


def _operational_handoff(st: dict[str, Any], detail: str) -> dict[str, Any]:
    """The complete run-contract/v1 handoff the command must EMIT TO THE USER
    when persistence stops the run — built from current parent KNOWLEDGE
    (latest dispatch, accumulated changes, baseline, evidence and artifacts,
    including a validated submission whose write failed) and validated. Never
    written to the broken store by this helper."""
    st = _knowledge(st)
    c = st["current"]
    h = {
        "schema": "run-contract/v1",
        "record": "handoff",
        "target": c["target"],
        "scope": c["scope"],
        "mode": c["mode"],
        "status": "stopped",
        "stop_reason": "operational-error",
        "stop_detail": detail,
        "blocker_kind": None,
        "blocker_class": None,
        "blocker_signature": None,
        "attempted_tools": list(st["attempted_tools"]),
        "best_candidates": list(st["best_candidates"]),
        "failed_avenues": list(st["failed_avenues"]),
        "evidence": json.loads(json.dumps(st["evidence"])),
        "files_owned": list(c["files_owned"]),
        "files_changed": list(st["files_changed"]),
        "file_baseline": c["file_baseline"],
        "artifacts": list(st.get("artifacts", [])),
        "next_action": "stop",
        "new_evidence_required_for_rerun": None,
    }
    errs = rc.validate_handoff(h)
    if errs:  # pragma: no cover — every ingredient was a validated record
        raise RuntimeError("operational handoff invalid: " + "; ".join(errs))
    return h


def _stop_result(
    st: dict[str, Any], kind: str, outcome: str, detail: str
) -> dict[str, Any]:
    res: dict[str, Any] = {
        "action": "stop",
        "run_id": st["run_id"],
        "kind": kind,
        "outcome": outcome,
        "detail": detail,
        "handoff": _operational_handoff(st, detail),
    }
    pend = (st.get("inflight") or {}).get("pending")
    if isinstance(pend, dict):
        res["unpersisted"] = {
            "kind": pend.get("kind"),
            "seq": None,
            "note": "this validated submission informed the handoff above but was NOT stored; it has no citation",
        }
    return res


def _terminal_reason(st: dict[str, Any]) -> str | None:
    if st.get("stopped"):
        return f"run already stopped by persistence policy: {st['stopped']}"
    if st.get("finished"):
        return f"run already finished ({st['finished']}); no mutation after finish"
    inflight = st.get("inflight")
    if inflight:
        return (
            f"an earlier {inflight.get('op')} ({inflight.get('kind')}) was left unresolved at "
            f"{inflight.get('at')} — its bookkeeping never completed, so its outcome is unknown"
        )
    return None


# --------------------------------------------------------------------------
# operations
# --------------------------------------------------------------------------


def _bind_root(st: dict[str, Any], requested: str | None) -> str:
    bound = str(st["storage_root"])
    if requested is not None and os.path.abspath(requested) != bound:
        raise UsageError(
            f"--root {requested!r} differs from the bound storage root {bound!r}"
        )
    return bound


def _mutate(
    ns: argparse.Namespace, st: dict[str, Any], op: str, kind: str, payload: Any
) -> tuple[dict[str, Any], int]:
    """One store mutation under the policy, with in-flight bookkeeping."""
    root = _bind_root(st, ns.root)
    reason = _terminal_reason(st)
    if reason:
        if not st.get("stopped"):  # first sight of an unresolved op / finished run
            st["stopped"] = reason
            _try_save(ns.state, st)
        if op == "finish":
            return _not_stored(st, "terminal", reason, payload), EXIT_STOP
        return _stop_result(st, kind, "terminal", reason), EXIT_STOP
    # 1. record the attempt BEFORE touching the store
    st["inflight"] = {
        "op": op,
        "kind": kind,
        "at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        # the VALIDATED submission: parent knowledge even if the write fails
        # (an invalid one is refused by the store and informs nothing)
        "pending": (
            {"kind": kind, "payload": payload}
            if op != "finish" and _valid_submission(kind, payload)
            else None
        ),
    }
    err = _try_save(ns.state, st)
    if err:
        # nothing was attempted; without bookkeeping the run cannot continue
        st["inflight"] = None
        st["stopped"] = f"invocation state unwritable before {op}: {err}"
        _try_save(ns.state, st)
        if op == "finish":
            return _not_stored(
                st, "state_unwritable", st["stopped"], payload
            ), EXIT_STOP
        return _stop_result(st, kind, "state_unwritable", st["stopped"]), EXIT_STOP
    # 2. the store
    body = json.dumps(payload).encode("utf-8")
    if op == "finish":
        args = ["set-handoff", "--run-id", st["run_id"], "--payload", "-"]
    else:
        args = ["append", "--run-id", st["run_id"], "--kind", kind, "--payload", "-"]
    code, raw, err_out = _run_store(args, body, root)
    outcome, detail, res = _classify(code, raw, err_out, expect_run_id=st["run_id"])
    if outcome == "refused:busy":
        time.sleep(1.0)
        code, raw, err_out = _run_store(args, body, root)
        outcome, detail, res = _classify(code, raw, err_out, expect_run_id=st["run_id"])
    # 3. resolve
    inflight = st["inflight"]
    st["inflight"] = None
    if res is not None and (
        outcome == "committed" or (op == "finish" and outcome == "journal_only")
    ):
        seq = int(res["seq"])
        st["last_seq"] = seq
        if op == "finish":
            st["finished"] = "stored"
        else:
            _absorb(st, kind, payload)
        result: dict[str, Any] = {
            "action": "done" if op == "finish" else "continue",
            "run_id": st["run_id"],
            "kind": kind,
            "seq": seq,
            "cite": f"{st['run_id']}#{seq}",
        }
        if op == "finish":
            result["stored"] = True
            if outcome == "journal_only":
                result["warning"] = (
                    f"handoff cache not confirmed ({detail}); the journal is authoritative"
                )
        save_err = _try_save(ns.state, st)
        if save_err:
            # The store DID commit — keep the outcome and its citation — but the
            # resolution could not be recorded, so the run must stop NOW, not
            # after one more step: the on-disk state still shows the in-flight
            # record and would stop the next call anyway.
            st["inflight"] = inflight  # what the disk still says
            detail = (
                f"invocation state could not be updated after a committed {op} "
                f"({save_err}); bookkeeping is unresolved"
            )
            if op == "finish":
                result["warning"] = (
                    result.get("warning", "") + " " if result.get("warning") else ""
                ) + detail
                return result, EXIT_OK  # terminal anyway; the handoff IS stored
            stop = _stop_result(st, kind, "state_unwritable", detail)
            stop["committed"] = {"seq": seq, "cite": result["cite"]}
            stop.pop("unpersisted", None)  # it WAS persisted
            return stop, EXIT_STOP
        return result, EXIT_OK
    # not committed: the run stops (finish → not stored). The submission is
    # kept as pending knowledge: it describes work that happened.
    if outcome == "malformed":
        detail = f"store acknowledgment unusable, treated as uncertain: {detail}"
    st["stopped"] = detail
    st["inflight"] = inflight if op != "finish" else None
    if op == "finish":
        st["finished"] = "not-stored"
        result = _not_stored(st, outcome, detail, payload)
    else:
        result = _stop_result(st, kind, outcome, detail)
    save_err = _try_save(ns.state, st)
    if save_err:
        result["warning"] = (
            f"invocation state could not be updated ({save_err}); later calls will stop"
        )
    return result, EXIT_STOP


def _not_stored(
    st: dict[str, Any], outcome: str, detail: str, submitted: Any
) -> dict[str, Any]:
    return {
        "action": "done",
        "run_id": st["run_id"],
        "stored": False,
        "outcome": outcome,
        "detail": detail,
        "fallback_handoff": submitted,
        "note": "emit fallback_handoff to the user in the stop summary; it was NOT saved and has no citation",
    }


def cmd_start(ns: argparse.Namespace, root: str) -> int:
    if os.path.lexists(ns.state):
        _emit(
            {
                "action": "startup-error",
                "code": "state_exists",
                "detail": f"invocation state {ns.state} already exists; each invocation needs a fresh, private state path",
            }
        )
        return EXIT_STARTUP
    dispatch = _read_json(ns.dispatch)
    errs = rc.validate_dispatch(dispatch)
    if errs:
        _emit(
            {
                "action": "startup-error",
                "code": "invalid_dispatch",
                "detail": "; ".join(errs),
            }
        )
        return EXIT_STARTUP
    args = ["create", "--dispatch", "-", "--event-schema", EVENT_SCHEMA_V2]
    if ns.tracker_session_id:
        args += ["--tracker-session-id", ns.tracker_session_id]
    if ns.prior_run:
        args += ["--prior-run", ns.prior_run]
    if ns.now:
        args += ["--now", ns.now]
    code, raw, err = _run_store(args, json.dumps(dispatch).encode("utf-8"), root)
    outcome, detail, res = _classify(code, raw, err, expect_run_id=None)
    if outcome != "committed" or res is None:
        _emit(
            {
                "action": "startup-error",
                "outcome": outcome,
                "code": res.get("code") if isinstance(res, dict) else None,
                "detail": detail or "run-store create did not commit",
                "note": "requested persistence could not start; do not start the command",
            }
        )
        return EXIT_STARTUP
    st = _new_state(root, str(res["run_id"]), str(res["run_directory"]), dispatch)
    try:
        _save_state(ns.state, st, exclusive=True)
    except OSError as ex:
        _emit(
            {
                "action": "startup-error",
                "code": "state_unwritable",
                "detail": f"run {st['run_id']} was created but the invocation state could not be written: {ex}",
            }
        )
        return EXIT_STARTUP
    _emit(
        {
            "action": "continue",
            "run_id": st["run_id"],
            "run_directory": st["run_directory"],
            "state": ns.state,
        }
    )
    return EXIT_OK


def cmd_append(ns: argparse.Namespace, kind: str) -> int:
    st = _load_state(ns.state)
    if kind == "note":
        payload: Any = {
            "kind": ns.kind,
            "text": ns.text,
            "lean": _read_text(ns.lean) if ns.lean else None,
        }
    else:
        payload = _read_json(ns.payload)
    res, code = _mutate(ns, st, "append", kind, payload)
    _emit(res)
    return code


def cmd_finish(ns: argparse.Namespace) -> int:
    st = _load_state(ns.state)
    handoff = _read_json(ns.payload)
    errs = rc.validate_handoff(handoff)
    if errs:
        # The submission is not a complete handoff: nothing is sent, and the
        # fallback the user sees is the VALID operational record built from
        # the current context — never the invalid submission.
        detail = (
            "submitted handoff is not a valid run-contract/v1 record: "
            + "; ".join(errs)
        )
        st["stopped"] = detail
        st["finished"] = "not-stored"
        _try_save(ns.state, st)
        _emit(
            {
                "action": "done",
                "run_id": st["run_id"],
                "stored": False,
                "outcome": "invalid_submission",
                "detail": detail,
                "fallback_handoff": _operational_handoff(st, detail),
                "submitted_errors": errs,
                "note": "emit fallback_handoff to the user in the stop summary; it was NOT saved and has no citation",
            }
        )
        return EXIT_STOP
    res, code = _mutate(ns, st, "finish", "handoff", handoff)
    _emit(res)
    return code


def _read_json(src: str) -> Any:
    try:
        if src == "-":
            data = sys.stdin.buffer.read()
        else:
            with open(src, "rb") as f:
                data = f.read()
        return json.loads(data.decode("utf-8"))
    except (OSError, ValueError) as ex:
        raise UsageError(f"payload {src!r}: {ex}") from ex


def _read_text(src: str) -> str:
    with open(src, encoding="utf-8") as f:
        return f.read()


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        prog="lean4-skills-run-persist", description=__doc__.split("\n\n")[0]
    )
    ap.add_argument(
        "--root",
        help="storage root for `start` (--run-store → $LEAN4_RUN_STORE → <project>/.lean4-skills); later calls use the root bound in the state",
    )
    ap.add_argument("--project-root")
    ap.add_argument(
        "--state",
        default=os.environ.get("LEAN4_RUN_PERSIST_STATE"),
        help="invocation-private state file (default $LEAN4_RUN_PERSIST_STATE)",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("start")
    s.add_argument("--dispatch", required=True)
    s.add_argument("--tracker-session-id")
    s.add_argument("--prior-run")
    s.add_argument("--now")
    for k in ("dispatch", "handoff", "review", "replan"):
        p = sub.add_parser(k)
        p.add_argument("--payload", required=True)
    n = sub.add_parser("note")
    n.add_argument("--kind", required=True)
    n.add_argument("--text", required=True)
    n.add_argument("--lean", help="file whose contents become the note's lean field")
    f = sub.add_parser("finish")
    f.add_argument("--payload", required=True)
    sub.add_parser("status")
    try:
        ns = ap.parse_args(argv)
    except SystemExit as ex:
        return EXIT_USAGE if ex.code else EXIT_OK
    if not ns.state:
        _emit(
            {
                "action": "usage",
                "detail": "--state (or $LEAN4_RUN_PERSIST_STATE) is required",
            }
        )
        return EXIT_USAGE
    try:
        if ns.cmd == "start":
            project_root = os.path.abspath(ns.project_root or os.getcwd())
            if ns.root:
                root = os.path.abspath(ns.root)
            elif os.environ.get("LEAN4_RUN_STORE"):
                root = os.path.abspath(os.environ["LEAN4_RUN_STORE"])
            else:
                root = os.path.join(project_root, ".lean4-skills")
            return cmd_start(ns, root)
        if ns.cmd == "status":
            _emit({"action": "status", "state": _load_state(ns.state)})
            return EXIT_OK
        if ns.cmd == "finish":
            return cmd_finish(ns)
        return cmd_append(ns, ns.cmd)
    except UsageError as ex:
        _emit({"action": "usage", "detail": str(ex)})
        return EXIT_USAGE


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
