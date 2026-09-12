#!/usr/bin/env python3
"""run-persist — the proving commands' persistence protocol over run-store/v1 (#82B).

`prove` and `autoprove` (with `--persist`) drive this helper instead of calling
the store directly, so the failure policy is deterministic code rather than
prose the model must re-implement each time:

    start    create the run (manifest v2 / event v2) after inputs, capability
             checks and a valid first dispatch — before any proof edit
    dispatch / handoff / note / review / replan
             append one event; the parent/controller is the sole writer
    finish   set the run's final handoff
    status   show the session state file

Every command prints one `run-persist-result/v1` object with an `action`:

    continue       the event is committed (or journal_only for finish): go on
    stop           persistence failed or is uncertain: STOP further proof work
                   and emit the operational-error handoff carried in the result
    startup-error  `start` could not create the run: do not start the command
    done           `finish` completed; `stored` says whether the handoff was
                   actually persisted — a fallback is never claimed as saved

Policy (references/cycle-engine.md § Run Persistence):
  committed       → continue
  journal_only    → continue with a warning; NEVER re-append
  busy            → one bounded retry after 1 s; never break the lock
  other refusal   → stop (operational-error, stop_detail names the code)
  indeterminate   → stop; an event visible to `load` is not evidence of a
                    durable commit, so no retry and no inferred success
  no result       → stop
Once a run is stopped by this policy the state file records it and every later
mutation returns `stop` without touching the store (the store is never asked
to persist its own failure report).

Session state lives in a small JSON file (`--state`, default
$LEAN4_RUN_PERSIST_STATE) so successive command steps share the run id.

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
STORE = os.path.join(HERE, "run_store.py")
RESULT_SCHEMA = "run-persist-result/v1"
STATE_SCHEMA = "run-persist-state/v1"
EVENT_SCHEMA_V2 = "run-store-event/v2"

EXIT_OK = 0
EXIT_USAGE = 2
EXIT_STARTUP = 3
EXIT_STOP = 5

# Injection point for tests (a fake store CLI).
_STORE_ARGV: list[str] | None = None


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
) -> tuple[int | None, dict[str, Any] | None, str]:
    """(exit code | None if the process yielded no result, parsed result | None, stderr)."""
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
        if not isinstance(res, dict):
            res = None
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
# state
# --------------------------------------------------------------------------


def _load_state(path: str) -> dict[str, Any]:
    with open(path, "rb") as f:
        st = json.loads(f.read().decode("utf-8"))
    if not isinstance(st, dict) or st.get("schema") != STATE_SCHEMA:
        raise ValueError("state file is not run-persist-state/v1")
    return st


def _save_state(path: str, st: dict[str, Any]) -> None:
    tmp = f"{path}.{os.getpid()}.tmp"
    with open(tmp, "wb") as f:
        f.write((json.dumps(st, indent=2) + "\n").encode("utf-8"))
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def _operational_handoff(st: dict[str, Any], detail: str) -> dict[str, Any]:
    """The complete run-contract/v1 handoff the command must EMIT TO THE USER
    when persistence stops the run. Built from the first dispatch so it is
    self-identifying; never written to the broken store by this helper."""
    d = st["dispatch"]
    return {
        "schema": "run-contract/v1",
        "record": "handoff",
        "target": d["target"],
        "scope": d["scope"],
        "mode": d["mode"],
        "status": "stopped",
        "stop_reason": "operational-error",
        "stop_detail": detail,
        "blocker_kind": None,
        "blocker_class": None,
        "blocker_signature": None,
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
        "files_owned": list(d["owned_files"]),
        "files_changed": [],
        "file_baseline": d["file_baseline"],
        "artifacts": [],
        "next_action": "stop",
        "new_evidence_required_for_rerun": None,
    }


# --------------------------------------------------------------------------
# policy
# --------------------------------------------------------------------------


def _classify(
    code: int | None, res: dict[str, Any] | None, stderr: str
) -> tuple[str, str]:
    """(outcome, detail) from a store invocation."""
    if code is None or res is None:
        return "no_result", stderr.strip() or "the store process yielded no result"
    outcome = res.get("outcome")
    if outcome == "committed":
        return "committed", ""
    if outcome == "journal_only":
        return "journal_only", str(res.get("detail", ""))
    if outcome == "indeterminate":
        return (
            "indeterminate",
            f"run-store indeterminate at {res.get('step')}: {res.get('detail')}",
        )
    if outcome == "nothing_written":
        return (
            f"refused:{res.get('code')}",
            f"run-store {res.get('code')}: {res.get('detail')}",
        )
    return "no_result", f"unrecognized store result: {json.dumps(res)[:200]}"


def _append(st: dict[str, Any], kind: str, payload: Any, root: str) -> dict[str, Any]:
    """One event under the policy. Returns the result object (with action)."""
    if st.get("stopped"):
        return {
            "action": "stop",
            "run_id": st["run_id"],
            "kind": kind,
            "detail": f"run already stopped by persistence policy: {st['stopped']}",
            "handoff": _operational_handoff(st, str(st["stopped"])),
        }
    body = json.dumps(payload).encode("utf-8")
    args = ["append", "--run-id", st["run_id"], "--kind", kind, "--payload", "-"]
    code, res, err = _run_store(args, body, root)
    outcome, detail = _classify(code, res, err)
    if outcome == "refused:busy":
        time.sleep(1.0)
        code, res, err = _run_store(args, body, root)
        outcome, detail = _classify(code, res, err)
    if outcome == "committed":
        assert res is not None
        seq = int(res["seq"])
        st["last_seq"] = seq
        return {
            "action": "continue",
            "run_id": st["run_id"],
            "kind": kind,
            "seq": seq,
            "cite": f"{st['run_id']}#{seq}",
        }
    # everything else stops the run (journal_only cannot happen on append)
    st["stopped"] = detail
    return {
        "action": "stop",
        "run_id": st["run_id"],
        "kind": kind,
        "outcome": outcome,
        "detail": detail,
        "handoff": _operational_handoff(st, detail),
    }


# --------------------------------------------------------------------------
# commands
# --------------------------------------------------------------------------


def cmd_start(ns: argparse.Namespace, root: str) -> int:
    dispatch = _read_json(ns.dispatch)
    args = ["create", "--dispatch", "-", "--event-schema", EVENT_SCHEMA_V2]
    if ns.tracker_session_id:
        args += ["--tracker-session-id", ns.tracker_session_id]
    if ns.prior_run:
        args += ["--prior-run", ns.prior_run]
    if ns.now:
        args += ["--now", ns.now]
    code, res, err = _run_store(args, json.dumps(dispatch).encode("utf-8"), root)
    outcome, detail = _classify(code, res, err)
    if outcome != "committed":
        assert res is None or isinstance(res, dict)
        _emit(
            {
                "action": "startup-error",
                "outcome": outcome,
                "code": (res or {}).get("code"),
                "detail": detail or "run-store create did not commit",
                "note": "requested persistence could not start; do not start the command",
            }
        )
        return EXIT_STARTUP
    assert res is not None
    st = {
        "schema": STATE_SCHEMA,
        "run_id": res["run_id"],
        "run_directory": res["run_directory"],
        "storage_root": root,
        "dispatch": dispatch,
        "last_seq": 0,
        "stopped": None,
        "finished": None,
    }
    _save_state(ns.state, st)
    _emit(
        {
            "action": "continue",
            "run_id": st["run_id"],
            "run_directory": st["run_directory"],
            "state": ns.state,
        }
    )
    return EXIT_OK


def cmd_append(ns: argparse.Namespace, root: str, kind: str) -> int:
    st = _load_state(ns.state)
    if kind == "note":
        payload: Any = {
            "kind": ns.kind,
            "text": ns.text,
            "lean": _read_text(ns.lean) if ns.lean else None,
        }
    else:
        payload = _read_json(ns.payload)
    res = _append(st, kind, payload, root)
    _save_state(ns.state, st)
    _emit(res)
    return EXIT_OK if res["action"] == "continue" else EXIT_STOP


def cmd_finish(ns: argparse.Namespace, root: str) -> int:
    st = _load_state(ns.state)
    handoff = _read_json(ns.payload)
    if st.get("stopped"):
        # The store already failed this run: the fallback is EMITTED, not saved.
        res = {
            "action": "done",
            "run_id": st["run_id"],
            "stored": False,
            "detail": f"run stopped by persistence policy: {st['stopped']}",
            "fallback_handoff": handoff,
        }
        st["finished"] = "not-stored"
        _save_state(ns.state, st)
        _emit(res)
        return EXIT_STOP
    body = json.dumps(handoff).encode("utf-8")
    args = ["set-handoff", "--run-id", st["run_id"], "--payload", "-"]
    code, sres, err = _run_store(args, body, root)
    outcome, detail = _classify(code, sres, err)
    if outcome == "refused:busy":
        time.sleep(1.0)
        code, sres, err = _run_store(args, body, root)
        outcome, detail = _classify(code, sres, err)
    if outcome in ("committed", "journal_only"):
        assert sres is not None
        seq = int(sres["seq"])
        st["finished"] = "stored"
        st["last_seq"] = seq
        _save_state(ns.state, st)
        out: dict[str, Any] = {
            "action": "done",
            "run_id": st["run_id"],
            "stored": True,
            "seq": seq,
            "cite": f"{st['run_id']}#{seq}",
        }
        if outcome == "journal_only":
            out["warning"] = (
                f"handoff cache not confirmed ({detail}); the journal is authoritative"
            )
        _emit(out)
        return EXIT_OK
    st["finished"] = "not-stored"
    st["stopped"] = detail
    _save_state(ns.state, st)
    _emit(
        {
            "action": "done",
            "run_id": st["run_id"],
            "stored": False,
            "outcome": outcome,
            "detail": detail,
            "fallback_handoff": handoff,
            "note": "emit fallback_handoff to the user in the stop summary; it was NOT saved and has no citation",
        }
    )
    return EXIT_STOP


def _read_json(src: str) -> Any:
    data = sys.stdin.buffer.read() if src == "-" else open(src, "rb").read()  # noqa: SIM115
    return json.loads(data.decode("utf-8"))


def _read_text(src: str) -> str:
    with open(src, encoding="utf-8") as f:
        return f.read()


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        prog="lean4-skills-run-persist", description=__doc__.split("\n\n")[0]
    )
    ap.add_argument(
        "--root",
        help="storage root (the command resolves --run-store → $LEAN4_RUN_STORE → <project>/.lean4-skills)",
    )
    ap.add_argument("--project-root")
    ap.add_argument(
        "--state",
        default=os.environ.get("LEAN4_RUN_PERSIST_STATE"),
        help="session state file (default $LEAN4_RUN_PERSIST_STATE)",
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
    project_root = os.path.abspath(ns.project_root or os.getcwd())
    root = (
        os.path.abspath(ns.root)
        if ns.root
        else (
            os.path.abspath(os.environ["LEAN4_RUN_STORE"])
            if os.environ.get("LEAN4_RUN_STORE")
            else os.path.join(project_root, ".lean4-skills")
        )
    )
    try:
        if ns.cmd == "start":
            return cmd_start(ns, root)
        if ns.cmd == "status":
            _emit({"action": "status", "state": _load_state(ns.state)})
            return EXIT_OK
        if ns.cmd == "finish":
            return cmd_finish(ns, root)
        return cmd_append(ns, root, ns.cmd)
    except (OSError, ValueError) as ex:
        _emit({"action": "usage", "detail": f"{type(ex).__name__}: {ex}"})
        return EXIT_USAGE


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
