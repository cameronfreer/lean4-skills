"""Structural validator for run-contract/v1 dispatch + handoff records (#190).

Production home of the validator that `tests/test_run_contract.py` introduced
(#191). The contract in `references/handoff-contract.md` is documentation, but
its required-field sets, enums, and conditional nullability are checkable; this
module encodes them so "valid record" cannot regress to prose, and so the run
store (#82A, `run_store.py`) can validate every dispatch/handoff it persists.

Hardened for ARBITRARY JSON (#82A review): every accessor type-checks before
use, so a non-object root, a list where a string/enum is expected, or a number
where a string is expected yields an error message naming the field — never a
`TypeError`/`AttributeError` escaping to the caller.

Structural validation only. `same_task` / `rerun_forbidden` implement the
contract's rerun-guard predicate for the proving controller; the store never
calls them — storing a dispatch is not controller enforcement.

Stdlib only.
"""

from __future__ import annotations

import re
from collections.abc import Callable
from typing import Any

SCHEMA = "run-contract/v1"


def _is_str(x: Any) -> bool:
    return isinstance(x, str)


def _is_int(x: Any) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


def _in_enum(x: Any, enum: set[str]) -> bool:
    """Membership that never raises: only a str can be a member."""
    return isinstance(x, str) and x in enum


# --- enums (mirrors handoff-contract.md) ---
SCOPES = {"sorry", "deps", "file", "changed", "project"}
MODES = {"prove", "autoprove", "golf"}
WORKERS = {"sorry-filler-deep", "proof-repair", "proof-golfer", "axiom-eliminator"}
STOP_REASONS = {
    "max-stuck",
    "max-cycles",
    "max-runtime",
    "user-stop",
    "queue-empty",
    "protocol-error",
    "operational-error",
}
OPERATIONAL_STOPS = {"protocol-error", "operational-error"}
BLOCKER_KINDS = {
    "proof",
    "false-statement",
    "safety-guard",
    "capability",
    "protocol",
    "operational",
}
BLOCKER_CLASSES = {
    "definitional-equality",
    "missing-intro-constructor-cases",
    "missing-rewrite",
    "arithmetic",
    "missing-library-lemma",
    "typeclass-coercion-elaboration",
    "needs-helper-lemma",
}
NEXT_ACTIONS = {"continue", "deep", "repair", "redraft", "golf", "stop"}
STATUSES = {"solved", "stuck", "stopped"}

DISPATCH_FIELDS = {
    "schema",
    "record",
    "target",
    "scope",
    "mode",
    "worker",
    "parameters",
    "capabilities",
    "owned_files",
    "file_baseline",
    "prior_blocker",
    "evidence_delta",
    "budget",
    "context",
}
CONTEXT_FIELDS = {
    "prior_failure",
    "goal_state",
    "diagnostics",
    "search_results",
    "candidates_tested",
    "code_actions",
    "scratch_location",
}
HANDOFF_FIELDS = {
    "schema",
    "record",
    "target",
    "scope",
    "mode",
    "status",
    "stop_reason",
    "stop_detail",
    "blocker_kind",
    "blocker_class",
    "blocker_signature",
    "attempted_tools",
    "best_candidates",
    "failed_avenues",
    "evidence",
    "files_owned",
    "files_changed",
    "file_baseline",
    "artifacts",
    "next_action",
    "new_evidence_required_for_rerun",
}


def _str_list(x: Any) -> bool:
    return isinstance(x, list) and all(isinstance(s, str) for s in x)


def _baseline_covers(baseline: Any, owned_files: Any) -> bool:
    """Every owned path appears in baseline.files — callers pass a validated
    baseline and a string list, but this never raises on anything else."""
    if not isinstance(baseline, dict) or not _str_list(owned_files):
        return False
    files = baseline.get("files")
    if not isinstance(files, list):
        return False
    covered = {f.get("path") for f in files if isinstance(f, dict)}
    return set(owned_files) <= covered


def _exact(obj: Any, spec: dict[str, Callable[[Any], bool]]) -> bool:
    """obj is a dict with EXACTLY the keys in spec, each value passing its predicate."""
    return (
        isinstance(obj, dict)
        and set(obj) == set(spec)
        and all(pred(obj[k]) for k, pred in spec.items())
    )


def _typed_dicts(seq: Any, spec: dict[str, Callable[[Any], bool]]) -> bool:
    return isinstance(seq, list) and all(_exact(x, spec) for x in seq)


# Serialized path grammar for PERSISTED records: a stored baseline must stay
# valid whichever host reads it (Python 3.13's ntpath.isabs rejects "/x", so
# os.path.isabs would make a POSIX-written record invalid on Windows). This
# recognizes the supported serialized styles without resolving anything;
# host-local custody checks (file_baseline.py) keep host-local semantics.
_SERIALIZED_ABS = re.compile(r"^(/|[A-Za-z]:[\\/]|\\\\)")


def _serialized_abs(p: Any) -> bool:
    return isinstance(p, str) and _SERIALIZED_ABS.match(p) is not None


def _valid_baseline(fb: Any) -> bool:
    """A structurally valid file-baseline/v1 record (as the primitive requires).
    Path absoluteness is judged by the serialized grammar above, not by the
    reading host's os.path."""
    if not isinstance(fb, dict) or fb.get("schema") != "file-baseline/v1":
        return False
    files = fb.get("files")
    if not isinstance(files, list) or not files:  # the primitive rejects empty
        return False
    seen_paths: set[str] = set()
    seen_reals: set[str] = set()
    for f in files:
        if not isinstance(f, dict):
            return False
        path, real = f.get("path"), f.get("realpath")
        if not (isinstance(path, str) and isinstance(real, str)):
            return False
        if not _serialized_abs(path) or not _serialized_abs(real):
            return False
        # The primitive rejects a duplicate path OR a duplicate realpath.
        if path in seen_paths or real in seen_reals:
            return False
        seen_paths.add(path)
        seen_reals.add(real)
        if not isinstance(f.get("exists"), bool):
            return False
        sha, size = f.get("sha256"), f.get("size")
        if f["exists"]:
            if not (isinstance(sha, str) and re.fullmatch(r"[0-9a-f]{64}", sha)):
                return False
            # negative size is invalid
            if not (isinstance(size, int) and not isinstance(size, bool) and size >= 0):
                return False
        elif sha is not None or size is not None:
            return False
    return True


# Fully-typed shape of each worker's `parameters` payload (exact keys + types).
def _deep_budget_ok(x: Any) -> bool:
    return _exact(x, {"scope": _is_str, "max_files": _is_int, "max_lines": _is_int})


def _repair_error_ok(x: Any) -> bool:
    return _exact(
        x,
        {
            "errorType": _is_str,
            "message": _is_str,
            "file": _is_str,
            "line": _is_int,
            "goal": _is_str,
            "localContext": _str_list,
        },
    )


WORKER_PARAM_SHAPES: dict[str, dict[str, Callable[[Any], bool]]] = {
    "sorry-filler-deep": {
        "fast_pass_error": _is_str,
        "permission_level": _is_str,
        "deep_budget": _deep_budget_ok,
    },
    "proof-repair": {"error": _repair_error_ok},
    "proof-golfer": {
        "search_mode": lambda x: _in_enum(x, {"off", "quick", "full"}),
        "golfable_patterns": _str_list,
        "candidate_targets": _str_list,
    },
    "axiom-eliminator": {"axioms": _str_list, "permission_level": _is_str},
}


def validate_parameters(worker: Any, params: Any) -> list[str]:
    """worker==null → parameters=={}; each named worker → its EXACT typed shape."""
    if worker is None:
        return (
            []
            if params == {}
            else ["inline dispatch (worker null) must have parameters {}"]
        )
    if not _in_enum(worker, set(WORKER_PARAM_SHAPES)):
        return ["unknown worker"]
    if not _exact(params, WORKER_PARAM_SHAPES[worker]):
        return [f"{worker} parameters must match its exact typed shape"]
    return []


def validate_dispatch(obj: Any) -> list[str]:
    """Errors for a run-contract/v1 dispatch record; [] when valid.

    Accepts any JSON value: a non-object root is one error, not an exception.
    """
    if not isinstance(obj, dict):
        return ["dispatch must be a JSON object"]
    e: list[str] = []
    missing = DISPATCH_FIELDS - set(obj)
    if missing:
        e.append(f"dispatch missing {sorted(missing)}")
    if obj.get("schema") != SCHEMA:
        e.append("dispatch schema must be run-contract/v1")
    if obj.get("record") != "dispatch":
        e.append("dispatch record must be 'dispatch'")
    if not _is_str(obj.get("target")):
        e.append("dispatch target must be a string")
    if not _in_enum(obj.get("scope"), SCOPES):
        e.append("dispatch scope not in enum")
    if not _in_enum(obj.get("mode"), MODES):
        e.append("dispatch mode not in enum")
    if obj.get("worker") is not None and not _in_enum(obj.get("worker"), WORKERS):
        e.append("dispatch worker must be a known agent or null")
    if (
        not _str_list(obj.get("owned_files"))
        or not _str_list(obj.get("evidence_delta"))
        or not _str_list(obj.get("capabilities"))
    ):
        e.append(
            "owned_files / evidence_delta / capabilities must be arrays of strings"
        )
    pb = obj.get("prior_blocker")
    if pb is not None and not _is_str(pb):
        e.append("dispatch prior_blocker must be str|null")
    # worker/parameters correlation (the "typed parameters" contract).
    e += validate_parameters(obj.get("worker"), obj.get("parameters"))
    # nested context member types + typed item shapes.
    ctx = obj.get("context")
    if not isinstance(ctx, dict) or (CONTEXT_FIELDS - set(ctx)):
        e.append("dispatch context missing required members")
    else:
        if not _str_list(ctx.get("diagnostics")) or not _str_list(
            ctx.get("code_actions")
        ):
            e.append("context.diagnostics / code_actions must be string arrays")
        if not _typed_dicts(
            ctx.get("search_results"),
            {"tool": _is_str, "query": _is_str, "top": _str_list},
        ):
            e.append(
                "context.search_results items must be {tool:str, query:str, top:[str]}"
            )
        if not _typed_dicts(
            ctx.get("candidates_tested"), {"snippet": _is_str, "result": _is_str}
        ):
            e.append(
                "context.candidates_tested items must be {snippet:str, result:str}"
            )
        if not isinstance(ctx.get("scratch_location"), str):
            e.append("context.scratch_location must be a non-null string")
        if not (ctx.get("prior_failure") is None or _is_str(ctx.get("prior_failure"))):
            e.append("context.prior_failure must be str|null")
        if not (ctx.get("goal_state") is None or _is_str(ctx.get("goal_state"))):
            e.append("context.goal_state must be str|null")
    # budget subfields: exact keys AND value types.
    b = obj.get("budget")
    if not isinstance(b, dict) or set(b) != {
        "max_cycles",
        "max_stuck_cycles",
        "runtime",
    }:
        e.append("budget must be {max_cycles, max_stuck_cycles, runtime}")
    else:
        for k in ("max_cycles", "max_stuck_cycles"):
            if not (b[k] is None or _is_int(b[k])):
                e.append(f"budget.{k} must be integer|null")
        if not (b["runtime"] is None or isinstance(b["runtime"], str)):
            e.append("budget.runtime must be duration-string|null")
    # file_baseline is a valid file-baseline/v1 covering every owned_files path.
    fb = obj.get("file_baseline")
    if not _valid_baseline(fb):
        e.append("file_baseline must be a valid file-baseline/v1 record")
    elif not _baseline_covers(fb, obj.get("owned_files")):
        e.append("file_baseline.files must cover every owned_files path")
    return e


def _blocker_driven(obj: dict[str, Any]) -> bool:
    return obj.get("status") == "stuck" or (
        obj.get("status") == "stopped" and obj.get("stop_reason") == "max-stuck"
    )


def validate_handoff(obj: Any) -> list[str]:
    """Errors for a run-contract/v1 handoff record; [] when valid.

    Accepts any JSON value: a non-object root is one error, not an exception.
    """
    if not isinstance(obj, dict):
        return ["handoff must be a JSON object"]
    e: list[str] = []
    missing = HANDOFF_FIELDS - set(obj)
    if missing:
        e.append(f"handoff missing {sorted(missing)}")
    if obj.get("schema") != SCHEMA or obj.get("record") != "handoff":
        e.append("handoff schema/record wrong")
    sr = obj.get("stop_reason")
    # Self-identifying task triple + baseline: non-null EXCEPT a protocol-error
    # handoff reporting a malformed dispatch (nothing valid to echo).
    malformed_ok = sr == "protocol-error"
    t, sc, md, fb = (obj.get(k) for k in ("target", "scope", "mode", "file_baseline"))
    if malformed_ok:
        if t is not None and not isinstance(t, str):
            e.append("target, when present, must be a string")
        if sc is not None and not _in_enum(sc, SCOPES):
            e.append("scope, when present, must be in enum")
        if md is not None and not _in_enum(md, MODES):
            e.append("mode, when present, must be in enum")
        if fb is not None and not _valid_baseline(fb):
            e.append("file_baseline, when present, must be a valid file-baseline/v1")
    else:
        if (
            not isinstance(t, str)
            or not _in_enum(sc, SCOPES)
            or not _in_enum(md, MODES)
        ):
            e.append("handoff must echo a valid target/scope/mode")
        if not _valid_baseline(fb) or not _baseline_covers(fb, obj.get("files_owned")):
            e.append(
                "handoff file_baseline must be a valid file-baseline/v1 covering files_owned"
            )
    if not _in_enum(obj.get("status"), STATUSES):
        e.append("handoff status not in enum")
    # stop_reason non-null iff stopped.
    if obj.get("status") == "stopped":
        if not _in_enum(sr, STOP_REASONS):
            e.append("stopped handoff needs a valid stop_reason")
    elif sr is not None:
        e.append("stop_reason must be null unless stopped")
    # stop_detail non-null iff operational/protocol stop — and a STRING.
    sd = obj.get("stop_detail")
    if _in_enum(sr, OPERATIONAL_STOPS):
        if not (_is_str(sd) and sd):
            e.append("operational/protocol stop needs a non-empty string stop_detail")
    elif sd is not None:
        e.append("stop_detail must be null unless operational/protocol stop")
    # blocker fields non-null iff blocker-driven (and strings when present).
    driven = _blocker_driven(obj)
    for f in ("blocker_kind", "blocker_signature", "new_evidence_required_for_rerun"):
        v = obj.get(f)
        if driven and not (_is_str(v) and v):
            e.append(f"blocker-driven handoff needs non-null {f}")
        if not driven and v is not None:
            e.append(f"{f} must be null when not blocker-driven")
    if driven and not _in_enum(obj.get("blocker_kind"), BLOCKER_KINDS):
        e.append("blocker_kind not in enum")
    # blocker_class non-null iff blocker_kind == proof.
    bc = obj.get("blocker_class")
    if driven and obj.get("blocker_kind") == "proof":
        if not _in_enum(bc, BLOCKER_CLASSES):
            e.append("proof blocker needs a valid blocker_class")
    elif bc is not None:
        e.append("blocker_class must be null unless blocker_kind == proof")
    if not _in_enum(obj.get("next_action"), NEXT_ACTIONS):
        e.append("next_action not in enum")
    # string-list fields.
    for f in ("files_owned", "files_changed", "attempted_tools", "failed_avenues"):
        if not _str_list(obj.get(f)):
            e.append(f"{f} must be an array of strings")
    # nested evidence shape incl. item + delta types.
    ev = obj.get("evidence")
    if not isinstance(ev, dict) or not (
        _str_list(ev.get("queries"))
        and _str_list(ev.get("top_candidates"))
        and _typed_dicts(ev.get("attempts"), {"snippet": _is_str, "result": _is_str})
        and {"goal_delta", "diagnostic_delta"} <= set(ev)
        and (ev.get("goal_delta") is None or _is_str(ev.get("goal_delta")))
        and (ev.get("diagnostic_delta") is None or _is_str(ev.get("diagnostic_delta")))
    ):
        e.append(
            "evidence shape invalid (str-list queries/top_candidates, {snippet:str,result:str} attempts, str|null deltas)"
        )
    # best_candidates and artifacts are fully-typed item lists.
    if not _typed_dicts(
        obj.get("best_candidates"), {"candidate": _is_str, "outcome": _is_str}
    ):
        e.append("best_candidates items must be {candidate:str, outcome:str}")
    if not _typed_dicts(obj.get("artifacts"), {"kind": _is_str, "content": _is_str}):
        e.append("artifacts items must be {kind:str, content:str}")
    return e


# --- rerun guard (controller policy; NOT called by the run store) ---


def same_task(new_dispatch: dict[str, Any], prior_handoff: dict[str, Any]) -> bool:
    return all(
        new_dispatch.get(k) == prior_handoff.get(k) for k in ("target", "scope", "mode")
    )


def rerun_forbidden(
    new_dispatch: dict[str, Any], prior_handoff: dict[str, Any]
) -> bool:
    """The rerun guard, evaluated from the two records — both branches."""
    # Operational/protocol branch: relaunch only with a nonempty evidence_delta
    # resolving stop_detail. Scope to same_task when the prior task identity is
    # available; a malformed-dispatch handoff (null identity) has no task to
    # compare, so the paired-retry fallback applies to any dispatch.
    if prior_handoff.get("stop_reason") in OPERATIONAL_STOPS:
        # same_task is only evaluable with a COMPLETE identity; a partial
        # malformed identity (e.g. target parsed, scope/mode null) must fall
        # through to the paired-retry rule, not be treated as unrelated.
        identity_complete = all(
            prior_handoff.get(k) is not None for k in ("target", "scope", "mode")
        )
        if identity_complete and not same_task(new_dispatch, prior_handoff):
            return False  # an unrelated task is not a rerun of this stop
        return not new_dispatch.get("evidence_delta")
    # Blocker branch.
    return (
        same_task(new_dispatch, prior_handoff)
        and prior_handoff.get("blocker_signature") is not None
        and new_dispatch.get("prior_blocker") == prior_handoff.get("blocker_signature")
        and not new_dispatch.get("evidence_delta")
    )
