"""Reverse-direction allow-list for the doc-sync test (Layer 3).

Each entry is either:
  - A rule_id string (for Coercion / CrossValidation records)
  - A (command, "requires"|"forbidden_with", flag, other) tuple

Used for spec-side constraints that intentionally have no documented prose.
The forward-direction step (5) cannot use this list — it has its own
exclusions mechanism at _doc_sync_forward_exclusions.py.

This list must stay under ~10 entries.
"""

from __future__ import annotations

ALLOWLIST: list[str | tuple[str, str, str, str]] = [
    # Currently empty — all spec-encoded rules have corresponding doc prose.
    # If a rule is added to COMMAND_SPECS without a doc update, add it here
    # temporarily with a justification comment naming the issue or commit.
]
