"""Structural fixtures for the run-contract/v1 dispatch + handoff records (#190).

The contract in `references/handoff-contract.md` is documentation, but its
required-field sets and conditional nullability are checkable — this suite
encodes them as a small structural validator and exercises valid and invalid
fixtures (including a proof-repair handoff carrying a unified-diff artifact), so
"valid record" cannot regress to prose. Stdlib only.
"""

from __future__ import annotations

import unittest
from typing import Any

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


def validate_dispatch(obj: dict[str, Any]) -> list[str]:
    e: list[str] = []
    missing = DISPATCH_FIELDS - set(obj)
    if missing:
        e.append(f"dispatch missing {sorted(missing)}")
    if obj.get("schema") != "run-contract/v1":
        e.append("dispatch schema must be run-contract/v1")
    if obj.get("record") != "dispatch":
        e.append("dispatch record must be 'dispatch'")
    if obj.get("scope") not in SCOPES:
        e.append("dispatch scope not in enum")
    if obj.get("mode") not in MODES:
        e.append("dispatch mode not in enum")
    if obj.get("worker") is not None and obj.get("worker") not in WORKERS:
        e.append("dispatch worker must be a known agent or null")
    if not isinstance(obj.get("owned_files"), list) or not isinstance(
        obj.get("evidence_delta"), list
    ):
        e.append("owned_files / evidence_delta must be arrays")
    ctx = obj.get("context")
    if not isinstance(ctx, dict) or (CONTEXT_FIELDS - set(ctx)):
        e.append("dispatch context missing required members")
    return e


def _blocker_driven(obj: dict[str, Any]) -> bool:
    return obj.get("status") == "stuck" or (
        obj.get("status") == "stopped" and obj.get("stop_reason") == "max-stuck"
    )


def validate_handoff(obj: dict[str, Any]) -> list[str]:
    e: list[str] = []
    missing = HANDOFF_FIELDS - set(obj)
    if missing:
        e.append(f"handoff missing {sorted(missing)}")
    if obj.get("schema") != "run-contract/v1" or obj.get("record") != "handoff":
        e.append("handoff schema/record wrong")
    # Self-identifying task triple (the rerun guard's same_task).
    if (
        not isinstance(obj.get("target"), str)
        or obj.get("scope") not in SCOPES
        or obj.get("mode") not in MODES
    ):
        e.append("handoff must echo a valid target/scope/mode")
    if obj.get("status") not in STATUSES:
        e.append("handoff status not in enum")
    # stop_reason non-null iff stopped.
    sr = obj.get("stop_reason")
    if obj.get("status") == "stopped":
        if sr not in STOP_REASONS:
            e.append("stopped handoff needs a valid stop_reason")
    elif sr is not None:
        e.append("stop_reason must be null unless stopped")
    # stop_detail non-null iff operational/protocol stop.
    if sr in OPERATIONAL_STOPS:
        if not obj.get("stop_detail"):
            e.append("operational/protocol stop needs a stop_detail")
    elif obj.get("stop_detail") is not None:
        e.append("stop_detail must be null unless operational/protocol stop")
    # blocker fields non-null iff blocker-driven.
    driven = _blocker_driven(obj)
    for f in ("blocker_kind", "blocker_signature", "new_evidence_required_for_rerun"):
        if driven and not obj.get(f):
            e.append(f"blocker-driven handoff needs non-null {f}")
        if not driven and obj.get(f) is not None:
            e.append(f"{f} must be null when not blocker-driven")
    if driven and obj.get("blocker_kind") not in BLOCKER_KINDS:
        e.append("blocker_kind not in enum")
    # blocker_class non-null iff blocker_kind == proof.
    bc = obj.get("blocker_class")
    if driven and obj.get("blocker_kind") == "proof":
        if bc not in BLOCKER_CLASSES:
            e.append("proof blocker needs a valid blocker_class")
    elif bc is not None:
        e.append("blocker_class must be null unless blocker_kind == proof")
    if obj.get("next_action") not in NEXT_ACTIONS:
        e.append("next_action not in enum")
    if not isinstance(obj.get("artifacts"), list):
        e.append("artifacts must be an array")
    return e


# --- fixtures ---


def _ctx() -> dict[str, Any]:
    return {
        "prior_failure": None,
        "goal_state": "⊢ Continuous f",
        "diagnostics": [],
        "search_results": [],
        "candidates_tested": [],
        "code_actions": [],
        "scratch_location": "/tmp",
    }


def _baseline() -> dict[str, Any]:
    return {
        "schema": "file-baseline/v1",
        "files": [
            {
                "path": "/repo/Foo.lean",
                "realpath": "/repo/Foo.lean",
                "exists": True,
                "sha256": "0" * 64,
                "size": 12,
            }
        ],
    }


def valid_dispatch(**over: Any) -> dict[str, Any]:
    d = {
        "schema": "run-contract/v1",
        "record": "dispatch",
        "target": "/repo/Foo.lean:42",
        "scope": "sorry",
        "mode": "prove",
        "worker": "sorry-filler-deep",
        "parameters": {},
        "capabilities": ["lean-lsp"],
        "owned_files": ["/repo/Foo.lean"],
        "file_baseline": _baseline(),
        "prior_blocker": None,
        "evidence_delta": [],
        "budget": {"max_cycles": 20, "max_stuck_cycles": 3, "runtime": "120m"},
        "context": _ctx(),
    }
    d.update(over)
    return d


def valid_handoff(**over: Any) -> dict[str, Any]:
    h = {
        "schema": "run-contract/v1",
        "record": "handoff",
        "target": "/repo/Foo.lean:42",
        "scope": "sorry",
        "mode": "prove",
        "status": "solved",
        "stop_reason": None,
        "stop_detail": None,
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
        "files_owned": ["/repo/Foo.lean"],
        "files_changed": ["/repo/Foo.lean"],
        "file_baseline": _baseline(),
        "artifacts": [],
        "next_action": "continue",
        "new_evidence_required_for_rerun": None,
    }
    h.update(over)
    return h


class DispatchValid(unittest.TestCase):
    def test_valid_first_dispatch(self) -> None:
        self.assertEqual(validate_dispatch(valid_dispatch()), [])

    def test_missing_worker_field_rejected(self) -> None:
        d = valid_dispatch()
        del d["worker"]
        self.assertTrue(validate_dispatch(d))

    def test_missing_context_member_rejected(self) -> None:
        d = valid_dispatch()
        d["context"] = {k: v for k, v in _ctx().items() if k != "scratch_location"}
        self.assertTrue(validate_dispatch(d))


class HandoffValid(unittest.TestCase):
    def test_solved(self) -> None:
        self.assertEqual(validate_handoff(valid_handoff()), [])

    def test_proof_stuck(self) -> None:
        self.assertEqual(
            validate_handoff(
                valid_handoff(
                    status="stuck",
                    blocker_kind="proof",
                    blocker_class="missing-library-lemma",
                    blocker_signature="Foo.lean:42:elaboration",
                    new_evidence_required_for_rerun="a lemma about tendsto",
                    next_action="deep",
                )
            ),
            [],
        )

    def test_safety_guard_stuck_has_null_blocker_class(self) -> None:
        # deep regression / header-fence etc.: blocker_kind set, blocker_class null.
        self.assertEqual(
            validate_handoff(
                valid_handoff(
                    status="stuck",
                    blocker_kind="safety-guard",
                    blocker_class=None,
                    blocker_signature="Foo.lean:42:deep-header-fence",
                    new_evidence_required_for_rerun="revert header change",
                    next_action="redraft",
                )
            ),
            [],
        )

    def test_operational_stop_needs_detail(self) -> None:
        self.assertEqual(
            validate_handoff(
                valid_handoff(
                    status="stopped",
                    stop_reason="operational-error",
                    stop_detail="file-baseline drift on Foo.lean",
                    next_action="stop",
                )
            ),
            [],
        )

    def test_queue_empty_stop(self) -> None:
        self.assertEqual(
            validate_handoff(
                valid_handoff(
                    status="stopped",
                    stop_reason="queue-empty",
                    next_action="stop",
                )
            ),
            [],
        )

    def test_proof_repair_diff_artifact(self) -> None:
        self.assertEqual(
            validate_handoff(
                valid_handoff(
                    files_changed=[],
                    next_action="continue",
                    artifacts=[
                        {
                            "kind": "unified-diff",
                            "content": "--- Foo.lean\n+++ Foo.lean\n",
                        }
                    ],
                )
            ),
            [],
        )


class HandoffRejections(unittest.TestCase):
    def test_missing_task_echo(self) -> None:
        h = valid_handoff()
        del h["target"]
        self.assertTrue(validate_handoff(h))

    def test_blocker_class_without_proof_kind(self) -> None:
        self.assertTrue(
            validate_handoff(
                valid_handoff(
                    status="stuck",
                    blocker_kind="safety-guard",
                    blocker_class="arithmetic",
                    blocker_signature="x",
                    new_evidence_required_for_rerun="y",
                )
            )
        )

    def test_operational_stop_missing_detail(self) -> None:
        self.assertTrue(
            validate_handoff(
                valid_handoff(
                    status="stopped",
                    stop_reason="protocol-error",
                    stop_detail=None,
                )
            )
        )

    def test_stuck_missing_blocker_signature(self) -> None:
        self.assertTrue(
            validate_handoff(
                valid_handoff(
                    status="stuck",
                    blocker_kind="proof",
                    blocker_class="arithmetic",
                    blocker_signature=None,
                    new_evidence_required_for_rerun="y",
                )
            )
        )

    def test_solved_with_stray_blocker(self) -> None:
        self.assertTrue(validate_handoff(valid_handoff(blocker_signature="x")))


if __name__ == "__main__":
    unittest.main()
