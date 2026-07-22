#!/usr/bin/env bash
set -euo pipefail

# Runtime smoke test for the bin/lean4-skills-* wrappers — the gate
# Check 28 (test_contracts.sh) deliberately stops short of: Check 28
# proves each wrapper's delegation *target exists*, this suite actually
# EXECUTES every wrapper and asserts its exact exit code. Converts the
# one-off manual smoke from PR #152 review into a permanent gate.
#
# Execution conditions are the hostile ones wrappers are designed for
# (#108/#148): argless, from a non-repository cwd, under a scrubbed
# environment with no LEAN4_* vars — so results are identical on dev
# machines (where the session bootstrap exports them; preflight would
# exit 0 there) and CI runners (where it exits 2).
#
# Expected codes are the wrappers' argless contract today:
#   2  argparse/usage errors and env-diagnosis failures
#   1  script-level "no input specified" errors
# A mismatch means a wrapper's argless behavior changed (update the
# table deliberately) — or, for 126/127, that the wrapper failed to
# exec its delegate at all (broken shebang, missing target, python3
# not found), which is exactly the regression class this suite exists
# to catch; those get a distinct message.
#
# Each wrapper gets two probes:
#   direct       — executes the wrapper itself, so the kernel resolves
#                  the shebang and the executable bit is on the hook;
#                  this is the probe that actually catches a broken
#                  shebang or a lost +x (as 126/127).
#   bash-compat  — forces $BASH_FOR_COMPAT (default /bin/bash) as the
#                  interpreter, pinning Bash 3.2 coverage in the macOS
#                  bash3-compat job regardless of how the scrubbed PATH
#                  resolves `env bash` (ubuntu's wrapper-smoke job runs
#                  the same probes under Bash 5).
# On hosts without /bin/bash the test SKIPs gracefully.

BASH_FOR_COMPAT="${BASH_FOR_COMPAT:-/bin/bash}"
if [[ ! -x "$BASH_FOR_COMPAT" ]]; then
    echo "SKIP: $BASH_FOR_COMPAT not found — cannot run wrapper runtime self-test"
    exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BIN_DIR="$PLUGIN_ROOT/bin"

PASS=0
FAIL=0

pass() { echo "  PASS: $1"; PASS=$((PASS + 1)); }
fail() { echo "  FAIL: $1"; FAIL=$((FAIL + 1)); }

# Non-repository cwd: wrappers must self-locate via BASH_SOURCE, never
# via git or the caller's cwd (#108's original symptom class).
SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"' EXIT
cd "$SCRATCH"

# Scrubbed PATH still needs python3 and coreutils; /usr/local/bin and
# /opt/homebrew/bin cover the macOS runner layouts (Bash 3.2 has no
# arrays-in-env tricks to do this more surgically).
CLEAN_PATH="/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin"

# name:expected-exit-code — one line per wrapper, kept in sync with
# bin/ by the completeness checks below (a wrapper missing from this
# table, or a table entry with no wrapper, both FAIL).
EXPECTED="
lean4-skills-analyze-let-usage:2
lean4-skills-check-axioms-inline:1
lean4-skills-cycle-tracker:2
lean4-skills-disprove-artifact-txn:2
lean4-skills-disprove-emit-artifact:2
lean4-skills-disprove-method-probe:2
lean4-skills-disprove-target-profile:2
lean4-skills-disprove-target-resolve:2
lean4-skills-find-exact-candidates:2
lean4-skills-find-golfable:2
lean4-skills-find-usages:1
lean4-skills-preflight:2
lean4-skills-search-mathlib:1
lean4-skills-smart-search:1
lean4-skills-sorry-analyzer:1
"

expected_for() {
    echo "$EXPECTED" | grep "^$1:" | cut -d: -f2
}

# Completeness, direction 1: every wrapper on disk has a table entry
# and is executable (the direct probe below would only report a lost
# +x as 126 — this names the actual defect).
for wrapper in "$BIN_DIR"/lean4-skills-*; do
    name=$(basename "$wrapper")
    if [[ -z "$(expected_for "$name")" ]]; then
        fail "$name exists in bin/ but has no expected-exit-code entry — add it to this suite"
    elif [[ ! -x "$wrapper" ]]; then
        fail "$name is not executable — wrappers must ship chmod +x"
    fi
done

# Completeness, direction 2: every table entry has a wrapper on disk.
for entry in $EXPECTED; do
    name=${entry%%:*}
    if [[ ! -f "$BIN_DIR/$name" ]]; then
        fail "table lists $name but bin/ has no such wrapper — remove or fix the entry"
    fi
done

# Runtime probes: direct (shebang + exec bit on the hook), then
# bash-compat (interpreter forced to $BASH_FOR_COMPAT).
for entry in $EXPECTED; do
    name=${entry%%:*}
    want=${entry##*:}
    wrapper="$BIN_DIR/$name"
    [[ -f "$wrapper" ]] || continue  # already FAILed above

    for mode in direct bash-compat; do
        got=0
        if [[ "$mode" == "direct" ]]; then
            out=$(env -i PATH="$CLEAN_PATH" HOME="$HOME" \
                "$wrapper" 2>&1) || got=$?
        else
            out=$(env -i PATH="$CLEAN_PATH" HOME="$HOME" \
                "$BASH_FOR_COMPAT" "$wrapper" 2>&1) || got=$?
        fi

        if [[ "$got" -eq 127 || "$got" -eq 126 ]]; then
            fail "$name ($mode): exit $got — failed to exec (broken shebang, lost +x, or unresolvable interpreter/delegate) (first line: $(echo "$out" | head -1))"
        elif echo "$out" | grep -qE 'Traceback \(most recent call last\)|can.t open file|command not found|bad interpreter|ModuleNotFoundError|ImportError|SyntaxError'; then
            # Exit code alone can false-green: a MISSING python delegate
            # exits 2 ("can't open file") and an uncaught traceback exits
            # 1 — both are "expected" codes for some wrappers. Reject
            # infrastructure-failure signatures regardless of exit code.
            # SyntaxError is listed separately because parse-time errors
            # print WITHOUT the "Traceback (most recent call last)"
            # header (verified empirically).
            fail "$name ($mode): output looks like an infrastructure failure, not the wrapper's usage contract (exit $got; first line: $(echo "$out" | head -1))"
        elif [[ "$got" -ne "$want" ]]; then
            fail "$name ($mode): exit $got, expected $want (first line: $(echo "$out" | head -1))"
        elif [[ -z "$out" && "$want" -ne 0 ]]; then
            fail "$name ($mode): expected a usage/error message on failure, got no output"
        else
            pass "$name ($mode): argless from non-repo cwd → exit $want"
        fi
    done
done

echo ""
echo "=== test_wrapper_runtime.sh: $PASS passed, $FAIL failed ==="
[[ $FAIL -eq 0 ]]
