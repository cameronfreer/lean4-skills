"""Structural fixtures for the run-contract/v1 dispatch + handoff records (#190).

The contract in `references/handoff-contract.md` is documentation, but its
required-field sets and conditional nullability are checkable. The validator is
PRODUCTION code (lib/scripts/run_contract_validate.py — moved there for the run
store, #82A) and this suite consumes that same module, exercising valid and
invalid fixtures (including a proof-repair handoff carrying a unified-diff
artifact) so "valid record" cannot regress to prose. Stdlib only.
"""

from __future__ import annotations

import os
import sys
import unittest
from typing import Any

_LIB_SCRIPTS = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "lib", "scripts"
)
sys.path.insert(0, _LIB_SCRIPTS)
from run_contract_validate import (  # noqa: E402
    _valid_baseline,
    rerun_forbidden,
    same_task,
    validate_dispatch,
    validate_handoff,
    validate_parameters,
)

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
        "parameters": {
            "fast_pass_error": "unsolved goals",
            "permission_level": "edit",
            "deep_budget": {"scope": "file", "max_files": 1, "max_lines": 40},
        },
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


class MalformedDispatchHandoff(unittest.TestCase):
    def test_protocol_error_may_null_task_and_baseline(self) -> None:
        # An unparseable dispatch still yields a VALID handoff.
        self.assertEqual(
            validate_handoff(
                valid_handoff(
                    target=None,
                    scope=None,
                    mode=None,
                    file_baseline=None,
                    status="stopped",
                    stop_reason="protocol-error",
                    stop_detail="dispatch missing owned_files",
                    next_action="stop",
                )
            ),
            [],
        )

    def test_non_protocol_stop_may_not_null_task(self) -> None:
        self.assertTrue(
            validate_handoff(
                valid_handoff(
                    target=None,
                    status="stopped",
                    stop_reason="queue-empty",
                    next_action="stop",
                )
            )
        )


class NestedShapeRejections(unittest.TestCase):
    def test_baseline_must_cover_owned_files(self) -> None:
        d = valid_dispatch(
            owned_files=["/repo/Other.lean"]
        )  # baseline covers /repo/Foo.lean
        self.assertTrue(any("cover" in x for x in validate_dispatch(d)))

    def test_context_member_wrong_type(self) -> None:
        d = valid_dispatch()
        d["context"]["diagnostics"] = "oops"
        self.assertTrue(validate_dispatch(d))

    def test_evidence_missing_subkey(self) -> None:
        h = valid_handoff()
        del h["evidence"]["goal_delta"]
        self.assertTrue(validate_handoff(h))

    def test_artifact_missing_content(self) -> None:
        self.assertTrue(
            validate_handoff(valid_handoff(artifacts=[{"kind": "unified-diff"}]))
        )

    def test_best_candidate_item_shape(self) -> None:
        self.assertTrue(
            validate_handoff(valid_handoff(best_candidates=["not-an-object"]))
        )


class RerunPredicate(unittest.TestCase):
    def _prior(self, **over: Any) -> dict[str, Any]:
        return valid_handoff(
            status="stuck",
            blocker_kind="proof",
            blocker_class="arithmetic",
            blocker_signature="Foo.lean:42:e",
            new_evidence_required_for_rerun="x",
            next_action="deep",
            **over,
        )

    def test_forbidden_same_blocker_no_evidence(self) -> None:
        prior = self._prior()
        d = valid_dispatch(prior_blocker="Foo.lean:42:e", evidence_delta=[])
        self.assertTrue(rerun_forbidden(d, prior))

    def test_allowed_different_task(self) -> None:
        prior = self._prior(target="/repo/Bar.lean:9")
        d = valid_dispatch(prior_blocker="Foo.lean:42:e", evidence_delta=[])
        self.assertFalse(rerun_forbidden(d, prior))  # same_task false

    def test_allowed_with_evidence_delta(self) -> None:
        prior = self._prior()
        d = valid_dispatch(prior_blocker="Foo.lean:42:e", evidence_delta=["new lemma"])
        self.assertFalse(rerun_forbidden(d, prior))

    def test_allowed_null_signature_stop(self) -> None:
        # queue-empty prior (null signature): null==null must NOT forbid.
        prior = valid_handoff(
            status="stopped", stop_reason="queue-empty", next_action="stop"
        )
        d = valid_dispatch(prior_blocker=None, evidence_delta=[])
        self.assertFalse(rerun_forbidden(d, prior))

    def test_task_echo_equality_drives_same_task(self) -> None:
        prior = self._prior()
        d = valid_dispatch()  # echoes the same /repo/Foo.lean:42, sorry, prove
        self.assertTrue(same_task(d, prior))

    def _op(self, **over: Any) -> dict[str, Any]:
        # A VALID operational handoff has non-null identity/baseline (nullability
        # is only for a malformed-dispatch protocol-error).
        return valid_handoff(
            status="stopped",
            stop_reason="operational-error",
            stop_detail="baseline drift",
            next_action="stop",
            **over,
        )

    def test_operational_same_task_empty_delta_forbidden(self) -> None:
        self.assertEqual(validate_handoff(self._op()), [])  # fixture itself is valid
        d = valid_dispatch(prior_blocker=None, evidence_delta=[])
        self.assertTrue(rerun_forbidden(d, self._op()))

    def test_operational_same_task_resolving_delta_allowed(self) -> None:
        d = valid_dispatch(prior_blocker=None, evidence_delta=["baseline reconciled"])
        self.assertFalse(rerun_forbidden(d, self._op()))

    def test_operational_different_task_allowed(self) -> None:
        prior = self._op(target="/repo/Bar.lean:9")
        d = valid_dispatch(prior_blocker=None, evidence_delta=[])  # /repo/Foo.lean:42
        self.assertFalse(rerun_forbidden(d, prior))

    def test_malformed_protocol_empty_delta_forbidden(self) -> None:
        prior = valid_handoff(
            target=None,
            scope=None,
            mode=None,
            file_baseline=None,
            status="stopped",
            stop_reason="protocol-error",
            stop_detail="dispatch missing owned_files",
            next_action="stop",
        )
        d = valid_dispatch(prior_blocker=None, evidence_delta=[])
        self.assertTrue(rerun_forbidden(d, prior))

    def _partial(self, **over: Any) -> dict[str, Any]:
        # target parsed, scope/mode null → same_task unevaluable (partial malformed).
        return valid_handoff(
            target="/repo/Foo.lean:42",
            scope=None,
            mode=None,
            file_baseline=None,
            status="stopped",
            stop_reason="protocol-error",
            stop_detail="scope unparseable",
            next_action="stop",
            **over,
        )

    def test_partial_identity_empty_delta_forbidden(self) -> None:
        # A non-null target must NOT be mistaken for a complete identity.
        d = valid_dispatch(prior_blocker=None, evidence_delta=[])
        self.assertTrue(rerun_forbidden(d, self._partial()))

    def test_partial_identity_resolving_delta_allowed(self) -> None:
        d = valid_dispatch(prior_blocker=None, evidence_delta=["dispatch corrected"])
        self.assertFalse(rerun_forbidden(d, self._partial()))

    def test_queue_empty_empty_delta_allowed(self) -> None:
        prior = valid_handoff(
            status="stopped", stop_reason="queue-empty", next_action="stop"
        )
        d = valid_dispatch(prior_blocker=None, evidence_delta=[])
        self.assertFalse(rerun_forbidden(d, prior))


class WorkerParameters(unittest.TestCase):
    def test_named_worker_requires_its_shape(self) -> None:
        # sorry-filler-deep with {} parameters is rejected (the r7 canonical bug).
        self.assertTrue(validate_dispatch(valid_dispatch(parameters={})))

    def test_inline_worker_requires_empty_params(self) -> None:
        self.assertEqual(validate_parameters(None, {}), [])
        self.assertTrue(validate_parameters(None, {"x": 1}))

    def test_each_worker_shape(self) -> None:
        self.assertEqual(
            validate_parameters(
                "proof-golfer",
                {
                    "search_mode": "quick",
                    "golfable_patterns": [],
                    "candidate_targets": [],
                },
            ),
            [],
        )
        self.assertEqual(
            validate_parameters(
                "axiom-eliminator", {"axioms": ["myAxiom"], "permission_level": "edit"}
            ),
            [],
        )
        self.assertEqual(
            validate_parameters(
                "proof-repair",
                {
                    "error": {
                        "errorType": "unsolved_goals",
                        "message": "m",
                        "file": "F.lean",
                        "line": 4,
                        "goal": "⊢ P",
                        "localContext": ["h : Q"],
                    }
                },
            ),
            [],
        )

    def test_wrong_or_missing_payload_rejected(self) -> None:
        self.assertTrue(
            validate_parameters("proof-golfer", {"axioms": []})
        )  # wrong worker's shape
        self.assertTrue(
            validate_parameters(
                "sorry-filler-deep",
                {"fast_pass_error": "e", "permission_level": "edit"},
            )
        )  # missing deep_budget
        # error missing goal/localContext, and a bad search_mode enum.
        self.assertTrue(
            validate_parameters("proof-repair", {"error": {"errorType": "x"}})
        )
        self.assertTrue(
            validate_parameters(
                "proof-golfer",
                {
                    "search_mode": "turbo",
                    "golfable_patterns": [],
                    "candidate_targets": [],
                },
            )
        )
        # extra key rejected (exact shape).
        self.assertTrue(
            validate_parameters(
                "axiom-eliminator",
                {"axioms": [], "permission_level": "edit", "extra": 1},
            )
        )


class DeeperRejections(unittest.TestCase):
    def test_budget_value_type(self) -> None:
        d = valid_dispatch()
        d["budget"]["max_cycles"] = "20"
        self.assertTrue(validate_dispatch(d))

    def test_context_search_result_item_shape(self) -> None:
        d = valid_dispatch()
        d["context"]["search_results"] = [{"tool": "x"}]  # missing query/top
        self.assertTrue(validate_dispatch(d))

    def test_handoff_string_lists(self) -> None:
        self.assertTrue(validate_handoff(valid_handoff(attempted_tools=[1, 2])))

    def test_evidence_attempt_item_shape(self) -> None:
        h = valid_handoff()
        h["evidence"]["attempts"] = [{"snippet": "s"}]  # missing result
        self.assertTrue(validate_handoff(h))

    def test_artifact_kind_must_be_string(self) -> None:
        self.assertTrue(
            validate_handoff(valid_handoff(artifacts=[{"kind": 1, "content": "x"}]))
        )

    def test_handoff_baseline_must_cover_files_owned(self) -> None:
        self.assertTrue(
            validate_handoff(valid_handoff(files_owned=["/repo/Other.lean"]))
        )

    def test_baseline_parity_with_primitive(self) -> None:
        entry = {
            "path": "/a",
            "realpath": "/a",
            "exists": True,
            "sha256": "0" * 64,
            "size": 1,
        }
        self.assertTrue(
            _valid_baseline({"schema": "file-baseline/v1", "files": [entry]})
        )
        # empty files, duplicate path, and negative size are all rejected.
        self.assertFalse(_valid_baseline({"schema": "file-baseline/v1", "files": []}))
        self.assertFalse(
            _valid_baseline(
                {"schema": "file-baseline/v1", "files": [entry, dict(entry)]}
            )
        )
        self.assertFalse(
            _valid_baseline(
                {"schema": "file-baseline/v1", "files": [{**entry, "size": -1}]}
            )
        )
        # two DISTINCT paths sharing one realpath are rejected too (as file_baseline.py does).
        self.assertFalse(
            _valid_baseline(
                {
                    "schema": "file-baseline/v1",
                    "files": [entry, {**entry, "path": "/b"}],
                }
            )
        )


if __name__ == "__main__":
    unittest.main()
