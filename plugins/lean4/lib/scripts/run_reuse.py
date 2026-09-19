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
import re
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
    """Digest of the OBSERVED prefix: run id, manifest (the initial dispatch
    lives there) and the validated events."""
    events = loaded.get("events", [])
    return len(events), _digest(
        {
            "run_id": loaded.get("run_id"),
            "manifest": loaded.get("manifest"),
            "events": events,
        }
    )


# --------------------------------------------------------------------------
# selection
# --------------------------------------------------------------------------


def _merge_baselines(
    layers: list[tuple[dict[str, Any] | None, str | None]],
) -> tuple[dict[str, Any], dict[str, str]]:
    """Per-file merged baseline. Layers are applied in JOURNAL order (the
    manifest's dispatch first, then every dispatch/handoff event by seq); the
    newest entry for a path wins, while paths a newer record does not cover
    keep the older entry. Returns a file-baseline/v1 record and
    {path: origin cite}."""
    merged: dict[str, dict[str, Any]] = {}
    origins: dict[str, str] = {}
    for baseline, cite in layers:
        if not isinstance(baseline, dict) or cite is None:
            continue
        for e in baseline.get("files", []):
            if isinstance(e, dict) and isinstance(e.get("path"), str):
                merged[e["path"]] = e
                origins[e["path"]] = cite
    if not merged:
        raise ReuseError(
            "no_usable_baseline",
            "neither the selected handoff nor the dispatch carries a file_baseline",
        )
    return {"schema": "file-baseline/v1", "files": list(merged.values())}, origins


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

    # per-file, in ACTUAL journal order: a redispatch may be newer than the
    # last handoff (the process stopped before its worker returned), and a
    # worker handoff may cover FEWER files than its dispatch — so the newest
    # applicable entry per path wins and older records fill the rest (never
    # an implicit match)
    layers: list[tuple[dict[str, Any] | None, str | None]] = [
        (manifest["dispatch"].get("file_baseline"), f"{rid}#manifest")
    ]
    layers += [
        (e["payload"].get("file_baseline"), f"{rid}#{e['seq']}")
        for e in events
        if e["kind"] in ("dispatch", "handoff")
    ]
    baseline, baseline_origins = _merge_baselines(layers)

    replans = [e for e in events if e["kind"] == "replan"]
    last_replan = replans[-1]["payload"] if replans else None
    reviews = []
    for e in events:
        if e["kind"] != "review" or e["payload"]["status"] != "completed":
            continue
        out = e["payload"].get("output") or {}
        reviews.append(
            {
                "cite": f"{rid}#{e['seq']}",
                "cycle": e["payload"]["cycle"],
                "mode": e["payload"]["mode"],
                "status": e["payload"]["status"],
                # the recommendations themselves, not just that a review happened
                "recommendations": list(out.get("suggestions") or []),
                "triage": e["payload"].get("triage"),
                "next_action": (e["payload"].get("triage") or {}).get("next_action"),
                "disposition": "unknown",  # recorded as completed; not known to have been applied
            }
        )
    failed: list[dict[str, str]] = []
    notes: list[dict[str, Any]] = []
    snippets: list[dict[str, Any]] = []
    for e in events:
        if e["kind"] == "note":
            p = e["payload"]
            cite = f"{rid}#{e['seq']}"
            notes.append(
                {
                    "cite": cite,
                    "kind": p["kind"],
                    "text": p["text"],
                    "lean": p.get("lean"),
                }
            )
            if p["kind"] == "failed-avenue":
                failed.append({"text": p["text"], "cite": cite})
            if p.get("lean"):
                snippets.append(
                    {
                        "cite": cite,
                        "kind": p["kind"],
                        "text": p["text"],
                        "lean": p["lean"],
                        "verified": False,
                    }
                )
        elif e["kind"] == "handoff":
            # a handoff's failed_avenues are citations (`<rid>#<seq>`) or prose;
            # a citation of a note already listed above is not repeated as text
            listed = {f["cite"] for f in failed}
            failed.extend(
                {"text": t, "cite": f"{rid}#{e['seq']}"}
                for t in e["payload"]["failed_avenues"]
                if t not in listed
            )

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
        "baseline_origins": baseline_origins,
        "carry": carry,
        "historical": {
            "plan": (last_replan or {}).get("plan"),
            "next_steps": (last_replan or {}).get("next_steps", []),
            "plan_cite": f"{rid}#{replans[-1]['seq']}" if replans else None,
            "failed_avenues": failed,
            "reviews": reviews,
            "notes": notes,
            "snippets": snippets,
        },
    }


# --------------------------------------------------------------------------
# compatibility
# --------------------------------------------------------------------------

_MODE_FAMILY = {"prove": "proving", "autoprove": "proving", "golf": "golf"}


def _inside(path: str, real_root: str) -> bool:
    rp = os.path.realpath(path)
    return rp == real_root or rp.startswith(real_root + os.sep)


def check_compat(
    selection: dict[str, Any],
    *,
    target: str,
    scope: str,
    mode: str,
    project_root: str,
    owned_files: list[str],
) -> None:
    """Prior dispatch vs the CURRENT invocation: mode family, target, and
    every path involved (prior owned files, the selected baseline's paths,
    and the current intended owned files) inside the current project."""
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
        if not _inside(str(f), real_root):
            raise ReuseError(
                "incompatible_owned_files",
                f"prior owned file {f!r} lies outside the current project root",
            )
    for f in selection["baseline_origins"]:
        if not _inside(f, real_root):
            raise ReuseError(
                "incompatible_owned_files",
                f"selected baseline path {f!r} lies outside the current project root",
            )
    if not owned_files:
        raise ReuseError("incompatible_owned_files", "no intended owned file given")
    for f in owned_files:
        if not _inside(f, real_root):
            raise ReuseError(
                "incompatible_owned_files",
                f"intended owned file {f!r} lies outside the current project root",
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


def _norm_files(owned_files: list[str]) -> list[str]:
    return sorted({os.path.abspath(f) for f in owned_files})


def drift_report(baseline: dict[str, Any], owned_files: list[str]) -> dict[str, Any]:
    """check (statuses vs the merged prior baseline) + record (current content
    of the intended owned files) + coverage (an intended file with NO prior
    baseline entry is an explicit `uncovered` outcome, never an implicit
    match); `approval_token` = digest of all three."""
    code, check, err = _baseline_cmd(["check", "--baseline", "-"], _canon(baseline))
    if not isinstance(check, dict) or code == 4 or code < 0:
        raise ReuseError(
            "drift_check_failed", err.strip() or f"file-baseline check exit {code}"
        )
    files = _norm_files(owned_files)
    code2, current, err2 = _baseline_cmd(["record", "--", *files], None)
    if not isinstance(current, dict) or code2 != 0:
        raise ReuseError(
            "drift_check_failed", err2.strip() or f"file-baseline record exit {code2}"
        )
    covered = {os.path.abspath(str(e["path"])) for e in baseline.get("files", [])}
    uncovered = [f for f in files if f not in covered]
    result = str(check["result"])
    if result == "match" and uncovered:
        result = "uncovered"
    token = _digest(
        {"check": check["entries"], "current": current["files"], "uncovered": uncovered}
    )
    return {
        "result": result,
        "entries": check["entries"],
        "unchecked": check.get("unchecked", []),
        "uncovered": uncovered,
        "current_baseline": current,
        "approval_token": token,
    }


# --------------------------------------------------------------------------
# preview / custody
# --------------------------------------------------------------------------


def invocation_record(
    *, project_root: str, target: str, scope: str, mode: str, owned_files: list[str]
) -> dict[str, Any]:
    return {
        "project_root": os.path.realpath(project_root),
        "target": target,
        "scope": scope,
        "mode": mode,
        "owned_files": _norm_files(owned_files),
    }


def source_note(
    *,
    prior_run: str,
    observed_seq: int,
    prefix_digest_: str,
    sel: dict[str, Any],
    drift: dict[str, Any],
) -> dict[str, Any]:
    """The local source-note: the selected material with its ORIGINAL
    citations, rebuilt from validated records (never copied from a report)."""
    return {
        "prior_run": prior_run,
        "observed_seq": observed_seq,
        "prefix_digest": prefix_digest_,
        "dispatch": sel["dispatch_cite"],
        "handoff": sel["handoff_cite"],
        "handoff_finality": "unknown",
        "baseline_origins": sel["baseline_origins"],
        "drift": {"result": drift["result"], "approval_token": drift["approval_token"]},
        "carry": sel["carry"],
        "historical": sel["historical"],
        "presentation": {
            "failed_avenues": "known dead ends under the prior assumptions — evidence, not prohibitions",
            "reviews": "recorded as completed; not known to have been applied — reassess",
            "snippets": "historical, unverified",
        },
    }


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
    check_compat(
        sel,
        target=target,
        scope=scope,
        mode=mode,
        project_root=project_root,
        owned_files=owned_files,
    )
    drift = drift_report(sel["baseline"], owned_files)
    inv = invocation_record(
        project_root=project_root,
        target=target,
        scope=scope,
        mode=mode,
        owned_files=owned_files,
    )
    note = source_note(
        prior_run=prior_run,
        observed_seq=observed_seq,
        prefix_digest_=digest,
        sel=sel,
        drift=drift,
    )
    return {
        "schema": REUSE_SCHEMA,
        "prior_run": prior_run,
        "observed_seq": observed_seq,
        "prefix_digest": digest,
        "invocation": inv,
        "selection": {
            "dispatch_cite": sel["dispatch_cite"],
            "handoff_cite": sel["handoff_cite"],
            "handoff_finality": "unknown",
            "guard_evaluable": sel["guard_evaluable"],
            "baseline_origins": sel["baseline_origins"],
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


_HEX64 = re.compile(r"^[0-9a-f]{64}$")


def validate_report(report: Any) -> dict[str, Any]:
    """Shape-check a `reuse` report (a structured refusal, never a KeyError).
    Historical material is NOT taken from it — it is rebuilt from the prior
    run's validated records at use."""
    from run_store import valid_run_id

    def bad(msg: str) -> ReuseError:
        return ReuseError("bad_reuse_report", f"not a {REUSE_SCHEMA} report: {msg}")

    if not isinstance(report, dict) or report.get("schema") != REUSE_SCHEMA:
        raise bad("schema")
    if not valid_run_id(report.get("prior_run")):
        raise bad("prior_run")
    if not isinstance(report.get("observed_seq"), int) or isinstance(
        report.get("observed_seq"), bool
    ):
        raise bad("observed_seq")
    if not isinstance(report.get("prefix_digest"), str) or not _HEX64.match(
        report["prefix_digest"]
    ):
        raise bad("prefix_digest")
    inv = report.get("invocation")
    if not isinstance(inv, dict):
        raise bad("invocation")
    for k in ("project_root", "target", "scope", "mode"):
        if not isinstance(inv.get(k), str) or not inv[k]:
            raise bad(f"invocation.{k}")
    of = inv.get("owned_files")
    if (
        not isinstance(of, list)
        or not of
        or not all(isinstance(f, str) and f for f in of)
        or of != _norm_files(of)
    ):
        raise bad("invocation.owned_files")
    drift = report.get("drift")
    if not isinstance(drift, dict):
        raise bad("drift")
    if drift.get("result") not in ("match", "drift", "uncovered", "error"):
        raise bad("drift.result")
    if not isinstance(drift.get("approval_token"), str) or not _HEX64.match(
        drift["approval_token"]
    ):
        raise bad("drift.approval_token")
    return report


def bind_invocation(
    report: dict[str, Any],
    *,
    project_root: str,
    target: str | None,
    scope: str | None,
    mode: str | None,
    owned_files: list[str],
) -> None:
    """The report must be THIS invocation's: same project, task (target AND
    scope — the guard's same_task predicate depends on both), mode and
    intended ownership set (a journal digest alone does not establish that)."""
    inv = report["invocation"]
    want = {
        "project_root": os.path.realpath(project_root),
        "target": target,
        "scope": scope,
        "mode": mode,
        "owned_files": _norm_files(owned_files),
    }
    for k, v in want.items():
        if v is not None and inv.get(k) != v:
            raise ReuseError(
                "reuse_report_mismatch",
                f"the reuse report was made for {k}={inv.get(k)!r}, not {v!r}; re-run reuse for this invocation",
            )


def custody(
    *,
    report: dict[str, Any],
    owned_files: list[str],
    approve: str | None,
    selection: dict[str, Any],
) -> dict[str, Any]:
    """Re-derive the drift report over ALL intended owned files (which must be
    the report's set); the fresh approval token must equal the report's (and,
    unless everything matched, the approved one). Returns the fresh baseline
    to record — nothing is written here."""
    if _norm_files(owned_files) != report["invocation"]["owned_files"]:
        raise ReuseError(
            "reuse_report_mismatch",
            "custody must cover exactly the intended owned files the report was made for",
        )
    fresh = drift_report(selection["baseline"], owned_files)
    expected = str(report["drift"]["approval_token"])
    if fresh["approval_token"] != expected:
        raise ReuseError(
            "custody_mismatch",
            "the files changed again after the preview/approval (content differs from the approved report); re-run reuse",
        )
    if fresh["result"] != "match":
        if approve is None:
            raise ReuseError(
                "drift_unapproved",
                f"{fresh['result']}: reconciliation is required and no approval token was given",
            )
        if approve != expected:
            raise ReuseError(
                "approval_mismatch",
                "the approval token does not name this exact drift report",
            )
    return {
        "schema": CUSTODY_SCHEMA,
        "result": fresh["result"],
        "uncovered": fresh["uncovered"],
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
