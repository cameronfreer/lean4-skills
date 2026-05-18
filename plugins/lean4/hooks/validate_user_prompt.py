#!/usr/bin/env python3
"""Claude UserPromptSubmit hook for /lean4:* slash commands.

Validates slash-command inputs before the model sees the prompt.
Hard parse errors block the prompt; successful parses inject a
validated-invocation block via additionalContext.

Fails OPEN on any internal error — a Python bug must NEVER prevent
a user from running a command.
"""

from __future__ import annotations

import json
import os
import sys

# Resolve plugin root from CLAUDE_PLUGIN_ROOT (set by Claude Code at hook time)
# or fall back to the script's own location when invoked directly.
# hooks/validate_user_prompt.py -> dirname = hooks -> parent = plugin root.
_PLUGIN_ROOT = os.environ.get("CLAUDE_PLUGIN_ROOT") or os.path.dirname(
    os.path.dirname(os.path.abspath(__file__))
)
_LIB_ROOT = os.path.join(_PLUGIN_ROOT, "lib")
if _LIB_ROOT not in sys.path:
    sys.path.insert(0, _LIB_ROOT)

# Pre-import gate: only the six parser-covered commands go through the parser.
# Uncovered commands pass through without importing command_args.
_COVERED_COMMANDS = {
    "draft",
    "learn",
    "formalize",
    "autoformalize",
    "prove",
    "autoprove",
}


def _emit(obj: dict[str, object]) -> None:
    json.dump(obj, sys.stdout)
    sys.stdout.write("\n")


def _passthrough() -> None:
    sys.exit(0)


def _emit_warning(message: str) -> None:
    _emit(
        {
            "hookSpecificOutput": {
                "hookEventName": "UserPromptSubmit",
                "additionalContext": message,
            }
        }
    )


def main() -> None:
    # 1. Read stdin JSON
    try:
        raw = sys.stdin.read()
        if not raw.strip():
            return _passthrough()
        payload = json.loads(raw)
    except Exception:
        return _passthrough()

    # 2. Check /lean4: prefix
    prompt = (payload.get("prompt") or "").lstrip()
    if not prompt.startswith("/lean4:"):
        return _passthrough()

    # 3. Extract command name — split on any whitespace (space, tab, newline)
    # so /lean4:draft<TAB>... and /lean4:draft<NEWLINE>... are handled.
    parts = prompt.split(None, 1)
    head = parts[0]
    tail = parts[1] if len(parts) > 1 else ""
    name = head[len("/lean4:") :]
    if not name:
        return _passthrough()

    # 4. Pre-import covered-command gate
    if name not in _COVERED_COMMANDS:
        return _passthrough()

    # 5. Import command_args (fail-open on import failure)
    try:
        from command_args import COMMAND_SPECS, format_validated_block, parse_invocation
    except Exception:
        return _emit_warning(
            "[lean4 parser unavailable — fell back to model parsing. "
            "Please report this as a bug.]"
        )

    # 6. Look up spec (defensive — should always succeed after gate)
    spec = COMMAND_SPECS.get(name)
    if spec is None:
        return _passthrough()

    # 7. Normalize cwd from payload
    cwd = os.path.abspath(payload.get("cwd") or os.getcwd())

    # 8. Run parser (fail-open on exception)
    try:
        result = parse_invocation(spec, tail, cwd=cwd)
    except Exception:
        return _emit_warning(
            f"[lean4 parser crashed for /lean4:{name} — falling back to "
            "model parsing. Stack trace suppressed.]"
        )

    # 9. Hard parse errors → block
    if result.errors:
        reason = f"Lean4 /{name} rejected:\n- " + "\n- ".join(result.errors)
        return _emit({"decision": "block", "reason": reason})

    # 10. Success → write artifact + emit validated block
    session_id = payload.get("session_id")
    if session_id:
        try:
            out_dir = os.environ.get("CLAUDE_SESSION_DIR") or os.path.join(
                __import__("tempfile").gettempdir()
            )
            os.makedirs(out_dir, exist_ok=True)
            artifact_path = os.path.join(out_dir, f"lean4_invocation_{session_id}.json")
            with open(artifact_path, "w") as f:
                json.dump(result.to_dict(), f)
        except Exception:
            pass  # artifact is best-effort

    block = format_validated_block(result)
    _emit(
        {
            "hookSpecificOutput": {
                "hookEventName": "UserPromptSubmit",
                "additionalContext": block,
            }
        }
    )


if __name__ == "__main__":
    main()
