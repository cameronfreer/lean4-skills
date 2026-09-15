#!/usr/bin/env python3
"""Prior-run reuse (#82C; Refs #82): selection, compatibility, content-bound drift.

A NEW invocation may name a prior run. This module is the read-only side of
that: it loads the prior run through the store's portable read path, selects
the historical material, checks compatibility with the current task, runs the
content-bound drift check, and describes what it observed. It never records a
baseline, never creates a run, never breaks a lock, and never claims to have
frozen the prior run.

Selection (no finality assumption):
  * prior dispatch = the last `dispatch` event, else the manifest's dispatch
    (cited as `<run_id>#manifest`);
  * prior handoff = the LATEST recorded handoff in the validated prefix, or
    none — its finality is UNKNOWN (the cache is disposable and irrelevant);
  * prior baseline = the selected handoff's `file_baseline` when present,
    else the dispatch's; origin recorded either way;
  * the selected handoff's blocker / stop fields are preserved as historical
    evidence and drive the rerun guard; the last Replan's blockers SUPPLEMENT
    them; with no usable handoff the handoff-based guard is not evaluable.

Drift: `file-baseline check` against the prior baseline over its files, plus a
`record` of the CURRENT content of the intended owned files. The approval
token is the digest of both — existence, resolved path, and content hash per
file — so approval binds to exact content, and custody re-derives the same
token before recording (any further change aborts).

Observation: the preview names the observed prefix (`observed_seq`,
`prefix_digest`); startup revalidates it. Absence of `.lock` proves nothing
about invocation liveness (locks cover single mutations); a present lock
refuses.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from typing import Any

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run_contract_validate as rc  # noqa: E402

REUSE_SCHEMA = "run-persist-reuse/v1"
CUSTODY_SCHEMA = "run-persist-custody/v1"
STORE = os.path.join(HERE, "run_store.py")
BASELINE = os.path.join(HERE, "file_baseline.py")
GENERIC_JUSTIFICATIONS = {
    "new run",
    "new run id",
    "fresh baseline",
    "drift approved",
    "retry",
    "rerun",
    "",
}


class ReuseError(Exception):
    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


def _canon(obj: Any) -> bytes:
    return json.dumps(
        obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def _digest(obj: Any) -> str:
    return hashlib.sha256(_canon(obj)).hexdigest()


# --------------------------------------------------------------------------
# loading (portable read path of the store)
# --------------------------------------------------------------------------


def _store_argv() -> list[str]:
    env = os.environ.get("LEAN4_RUN_STORE_ARGV")
    if env:
        argv = json.loads(env)
        if isinstance(argv, list) and all(isinstance(a, str) for a in argv):
            return argv
    return [sys.executable, STORE]


def load_prior(root: str, prior_run: str) -> dict[str, Any]:
    """The store's `load` result for the prior run, or a ReuseError naming why
    the run is unusable. Read-only."""
    from run_store import valid_run_id

    if not valid_run_id(prior_run):
        raise ReuseError(
            "bad_prior_run", "prior run id must match YYYYMMDDTHHMMSSZ-<8 hex>"
        )
    lock = os.path.join(root, "runs", prior_run, ".lock")
    if os.path.lexists(lock):
        raise ReuseError(
            "prior_run_active",
            f"{lock} exists: a mutation of the prior run may be in progress (never broken here)",
        )
    try:
        p = subprocess.run(
            [*_store_argv(), "--root", root, "load", "--run-id", prior_run],
            capture_output=True,
            check=False,
            timeout=120,
        )
    except (OSError, subprocess.SubprocessError) as ex:
        raise ReuseError("prior_run_unreadable", f"store load failed: {ex}") from ex
    try:
        res = json.loads(p.stdout.decode("utf-8"))
    except (UnicodeDecodeError, ValueError) as ex:
        raise ReuseError(
            "prior_run_unreadable", f"store load gave no result: {ex}"
        ) from ex
    if not isinstance(res, dict):
        raise ReuseError("prior_run_unreadable", "store load result is not an object")
    if res.get("schema") != "run-store-load/v1":
        code = (
            res.get("code")
            if isinstance(res.get("code"), str)
            else "prior_run_unusable"
        )
        raise ReuseError(
            str(code), str(res.get("detail", "store refused to load the prior run"))
        )
    if res.get("damaged"):
        raise ReuseError(
            "prior_run_damaged",
            "the prior journal is damaged ("
            + "; ".join(w.get("code", "?") for w in res.get("warnings", []))
            + "); reuse never reads past the valid prefix and never repairs",
        )
    return res


def prefix_digest(loaded: dict[str, Any]) -> tuple[int, str]:
    events = loaded.get("events", [])
    return len(events), _digest({"run_id": loaded.get("run_id"), "events": events})


# --------------------------------------------------------------------------
# selection
# --------------------------------------------------------------------------


def select(loaded: dict[str, Any]) -> dict[str, Any]:
    rid = str(loaded["run_id"])
    events: list[dict[str, Any]] = list(loaded.get("events", []))
    manifest = loaded["manifest"]

    dispatches = [e for e in events if e["kind"] == "dispatch"]
    if dispatches:
        dispatch, dispatch_cite = (
            dispatches[-1]["payload"],
            f"{rid}#{dispatches[-1]['seq']}",
        )
    else:
        dispatch, dispatch_cite = manifest["dispatch"], f"{rid}#manifest"

    handoffs = [e for e in events if e["kind"] == "handoff"]
    handoff = handoffs[-1]["payload"] if handoffs else None
    handoff_cite = f"{rid}#{handoffs[-1]['seq']}" if handoffs else None

    if handoff is not None and handoff.get("file_baseline") is not None:
        baseline, baseline_origin = handoff["file_baseline"], handoff_cite
    elif dispatch.get("file_baseline") is not None:
        baseline, baseline_origin = dispatch["file_baseline"], dispatch_cite
    else:
        raise ReuseError(
            "no_usable_baseline",
            "neither the selected handoff nor the dispatch carries a file_baseline",
        )

    replans = [e for e in events if e["kind"] == "replan"]
    last_replan = replans[-1]["payload"] if replans else None
    reviews = [
        {
            "cite": f"{rid}#{e['seq']}",
            "cycle": e["payload"]["cycle"],
            "mode": e["payload"]["mode"],
            "status": e["payload"]["status"],
            "next_action": (e["payload"].get("triage") or {}).get("next_action"),
            "disposition": "unknown",  # recorded as completed; not known to have been applied
        }
        for e in events
        if e["kind"] == "review" and e["payload"]["status"] == "completed"
    ]
    failed: list[dict[str, str]] = []
    for e in events:
        if e["kind"] == "note" and e["payload"]["kind"] == "failed-avenue":
            failed.append({"text": e["payload"]["text"], "cite": f"{rid}#{e['seq']}"})
        elif e["kind"] == "handoff":
            failed.extend(
                {"text": t, "cite": f"{rid}#{e['seq']}"}
                for t in e["payload"]["failed_avenues"]
            )
    snippets = [
        {"cite": f"{rid}#{e['seq']}", "kind": e["payload"]["kind"], "verified": False}
        for e in events
        if e["kind"] == "note" and e["payload"].get("lean")
    ]

    carry: dict[str, Any] = {
        "prior_blocker": handoff.get("blocker_signature") if handoff else None,
        "blocker_kind": handoff.get("blocker_kind") if handoff else None,
        "blocker_class": handoff.get("blocker_class") if handoff else None,
        "status": handoff.get("status") if handoff else None,
        "stop_reason": handoff.get("stop_reason") if handoff else None,
        "stop_detail": handoff.get("stop_detail") if handoff else None,
        "new_evidence_required_for_rerun": handoff.get(
            "new_evidence_required_for_rerun"
        )
        if handoff
        else None,
        "replan_blockers": (last_replan or {}).get(
            "blockers", []
        ),  # supplement, never a replacement
    }
    return {
        "dispatch": dispatch,
        "dispatch_cite": dispatch_cite,
        "handoff": handoff,
        "handoff_cite": handoff_cite,
        "handoff_finality": "unknown",
        "guard_evaluable": handoff is not None,
        "baseline": baseline,
        "baseline_origin": baseline_origin,
        "carry": carry,
        "historical": {
            "plan": (last_replan or {}).get("plan"),
            "next_steps": (last_replan or {}).get("next_steps", []),
            "plan_cite": f"{rid}#{replans[-1]['seq']}" if replans else None,
            "failed_avenues": failed,
            "reviews": reviews,
            "snippets": snippets,
        },
    }


# --------------------------------------------------------------------------
# compatibility
# --------------------------------------------------------------------------

_MODE_FAMILY = {"prove": "proving", "autoprove": "proving", "golf": "golf"}


def check_compat(
    selection: dict[str, Any], *, target: str, scope: str, mode: str, project_root: str
) -> None:
    d = selection["dispatch"]
    if _MODE_FAMILY.get(str(d.get("mode"))) != _MODE_FAMILY.get(mode):
        raise ReuseError(
            "incompatible_mode", f"prior mode {d.get('mode')!r} vs current {mode!r}"
        )
    pt = str(d.get("target"))
    if scope in ("file", "project", "changed"):
        ok = pt == target or pt.startswith(target.split(":", 1)[0])
    else:
        ok = pt == target
    if not ok:
        raise ReuseError(
            "incompatible_target",
            f"prior target {pt!r} is not the current target {target!r} (scope {scope})",
        )
    real_root = os.path.realpath(project_root)
    for f in d.get("owned_files", []):
        rp = os.path.realpath(f)
        if not (rp == real_root or rp.startswith(real_root + os.sep)):
            raise ReuseError(
                "incompatible_owned_files",
                f"prior owned file {f!r} lies outside the current project root",
            )


# --------------------------------------------------------------------------
# drift (content-bound)
# --------------------------------------------------------------------------


def _baseline_cmd(args: list[str], stdin: bytes | None) -> tuple[int, Any, str]:
    try:
        p = subprocess.run(
            [sys.executable, BASELINE, *args],
            input=stdin,
            capture_output=True,
            check=False,
            timeout=120,
        )
    except (OSError, subprocess.SubprocessError) as ex:
        return -1, None, str(ex)
    try:
        return (
            p.returncode,
            json.loads(p.stdout.decode("utf-8")),
            p.stderr.decode("utf-8", "replace"),
        )
    except (UnicodeDecodeError, ValueError):
        return p.returncode, None, p.stderr.decode("utf-8", "replace")


def drift_report(baseline: dict[str, Any], owned_files: list[str]) -> dict[str, Any]:
    """check (statuses vs the prior baseline) + record (current content of the
    intended owned files); `approval_token` = digest of both."""
    code, check, err = _baseline_cmd(["check", "--baseline", "-"], _canon(baseline))
    if not isinstance(check, dict) or code == 4 or code < 0:
        raise ReuseError(
            "drift_check_failed", err.strip() or f"file-baseline check exit {code}"
        )
    code2, current, err2 = _baseline_cmd(["record", "--", *owned_files], None)
    if not isinstance(current, dict) or code2 != 0:
        raise ReuseError(
            "drift_check_failed", err2.strip() or f"file-baseline record exit {code2}"
        )
    token = _digest({"check": check["entries"], "current": current["files"]})
    return {
        "result": check["result"],
        "entries": check["entries"],
        "unchecked": check.get("unchecked", []),
        "current_baseline": current,
        "approval_token": token,
    }


# --------------------------------------------------------------------------
# preview / custody
# --------------------------------------------------------------------------


def preview(
    *,
    root: str,
    prior_run: str,
    target: str,
    scope: str,
    mode: str,
    project_root: str,
    owned_files: list[str],
) -> dict[str, Any]:
    loaded = load_prior(root, prior_run)
    observed_seq, digest = prefix_digest(loaded)
    sel = select(loaded)
    check_compat(sel, target=target, scope=scope, mode=mode, project_root=project_root)
    drift = drift_report(sel["baseline"], owned_files)
    note = {
        "prior_run": prior_run,
        "observed_seq": observed_seq,
        "prefix_digest": digest,
        "dispatch": sel["dispatch_cite"],
        "handoff": sel["handoff_cite"],
        "handoff_finality": "unknown",
        "baseline_origin": sel["baseline_origin"],
        "carry": sel["carry"],
        "historical": sel["historical"],
        "presentation": {
            "failed_avenues": "known dead ends under the prior assumptions — evidence, not prohibitions",
            "reviews": "recorded as completed; not known to have been applied — reassess",
            "snippets": "historical, unverified",
        },
    }
    return {
        "schema": REUSE_SCHEMA,
        "prior_run": prior_run,
        "observed_seq": observed_seq,
        "prefix_digest": digest,
        "selection": {
            "dispatch_cite": sel["dispatch_cite"],
            "handoff_cite": sel["handoff_cite"],
            "handoff_finality": "unknown",
            "guard_evaluable": sel["guard_evaluable"],
            "baseline_origin": sel["baseline_origin"],
        },
        "carry": sel["carry"],
        "historical": sel["historical"],
        "drift": drift,
        "source_note_text": json.dumps(note, ensure_ascii=False, sort_keys=True),
        "note": (
            "read-only preview of an observed journal prefix; no ownership of the prior run is "
            "claimed and nothing was recorded or created"
        ),
    }


def custody(
    *,
    report: dict[str, Any],
    owned_files: list[str],
    approve: str | None,
    prior_baseline: dict[str, Any],
) -> dict[str, Any]:
    """Re-derive the drift report over ALL intended owned files; the fresh
    approval token must equal the report's (and, with drift, the approved
    one). Returns the fresh baseline to record — nothing is written here."""
    fresh = drift_report(prior_baseline, owned_files)
    expected = str(report["drift"]["approval_token"])
    if fresh["approval_token"] != expected:
        raise ReuseError(
            "custody_mismatch",
            "the files changed again after the preview/approval (content differs from the approved report); re-run reuse",
        )
    if fresh["result"] != "match":
        if approve is None:
            raise ReuseError(
                "drift_unapproved", "drift is present and no approval token was given"
            )
        if approve != expected:
            raise ReuseError(
                "approval_mismatch",
                "the approval token does not name this exact drift report",
            )
    return {
        "schema": CUSTODY_SCHEMA,
        "result": fresh["result"],
        "fresh_baseline": fresh["current_baseline"],
        "approval_token": expected,
    }


def guard_decision(
    dispatch: dict[str, Any], selection: dict[str, Any], justification: str | None
) -> dict[str, Any]:
    """The shipped rerun guard, applied to the new run's first dispatch against
    the prior run's selected handoff. Never clears the carried blocker."""
    carry = selection["carry"]
    if dispatch.get("prior_blocker") != carry["prior_blocker"]:
        raise ReuseError(
            "blocker_cleared",
            f"first dispatch must carry the prior blocker {carry['prior_blocker']!r} as prior_blocker (got {dispatch.get('prior_blocker')!r})",
        )
    handoff = selection.get("handoff")
    if handoff is None:
        return {
            "evaluable": False,
            "forbidden": False,
            "reason": "no usable prior handoff: the handoff-based guard cannot be evaluated",
        }
    forbidden = rc.rerun_forbidden(dispatch, handoff)
    if forbidden:
        return {
            "evaluable": True,
            "forbidden": True,
            "reason": "same task, same blocker, no evidence delta",
            "new_evidence_required_for_rerun": handoff.get(
                "new_evidence_required_for_rerun"
            ),
        }
    if handoff.get("stop_reason") in rc.OPERATIONAL_STOPS and dispatch.get(
        "evidence_delta"
    ):
        j = (justification or "").strip().lower()
        if j in GENERIC_JUSTIFICATIONS or len(j) < 12:
            raise ReuseError(
                "justification_required",
                "the prior stop was operational; state specifically how the evidence delta addresses "
                f"its stop_detail ({handoff.get('stop_detail')!r}) — a new run id, approved drift or a fresh baseline is not evidence",
            )
    return {
        "evaluable": True,
        "forbidden": False,
        "reason": "guard allows the dispatch",
    }
