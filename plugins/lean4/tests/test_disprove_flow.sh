#!/bin/bash
set -euo pipefail

# Integration smoke test for the /lean4:disprove dynamic-menus pipeline.
#
# Scope: the deterministic, scriptable components of a disprove session —
#   - target classification (disprove_target_resolve.py)
#   - parser → tracker init → kw-search counter → tick reset
#   - registry load + schema validation
# OUT OF SCOPE (model-mediated, cannot be unit-tested in shell):
#   - the cycling LLM's Step 1 / Step 2 menu ranking
#   - interactive Step 0 / Step 1 / Step 2 menus (LLM-proposed candidates)
#   - WebFetch verification of web-tier counterexample candidates
#   - findings.jsonl writes (the writer drops records without source_url)
#   - the artifact emitter's Lean snippet construction
# These paths are exercised by the model under live use; the contract here
# is that the surrounding deterministic plumbing is correct.

: "${TMPDIR:=/tmp}"
export TMPDIR

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN4_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRACKER="$LEAN4_ROOT/lib/scripts/cycle_tracker.sh"
RESOLVE="$LEAN4_ROOT/lib/scripts/disprove_target_resolve.py"

PASS=0
FAIL=0

pass() { echo "  PASS: $1"; (( ++PASS )); }
fail() { echo "  FAIL: $1"; echo "        $2"; (( ++FAIL )); }

assert_eq() {
  local desc="$1" expected="$2" actual="$3"
  if [[ "$actual" == "$expected" ]]; then pass "$desc"
  else fail "$desc" "expected $expected, got $actual"
  fi
}

assert_exit_eq() {
  local desc="$1" expected="$2" actual="$3"
  if [[ "$actual" -eq "$expected" ]]; then pass "$desc"
  else fail "$desc" "expected exit $expected, got $actual"
  fi
}

echo "=== /lean4:disprove integration smoke ==="

# -------------------------------------------------------------------------
echo ""
echo "-- Target classification (disprove_target_resolve.py) --"

OUT=$(python3 "$RESOLVE" "Foo.lean:42" 2>&1)
case "$OUT" in
  *'"kind": "file-line"'*'"file": "Foo.lean"'*'"line": 42'*) pass "file-line target classified" ;;
  *) fail "file-line target classified" "got: $OUT" ;;
esac

OUT=$(python3 "$RESOLVE" "MyNs.SubNs.myThm" 2>&1)
case "$OUT" in
  *'"kind": "qualified-name"'*'"name": "MyNs.SubNs.myThm"'*) pass "qualified-name target classified" ;;
  *) fail "qualified-name target classified" "got: $OUT" ;;
esac

set +e
python3 "$RESOLVE" "Foo.lean" >/dev/null 2>&1
EXIT=$?
set -e
assert_exit_eq "Foo.lean without :LINE rejected" 2 "$EXIT"

# -------------------------------------------------------------------------
echo ""
echo "-- Tracker init with --max-knowledge-search-per-cycle --"

LEAN4_SESSION_ID=$(bash "$TRACKER" init \
  --max-cycles=3 \
  --max-stuck=2 \
  --max-runtime=5m \
  --max-knowledge-search-per-cycle=3 \
  2>/dev/null)
export LEAN4_SESSION_ID
assert_exit_eq "init accepts --max-knowledge-search-per-cycle" 0 0

OUT=$(bash "$TRACKER" status)
case "$OUT" in
  *"kw_search_this_cycle=0/3"*) pass "status reports kw_search_this_cycle=0/3" ;;
  *) fail "status reports kw_search_this_cycle=0/3" "got: $OUT" ;;
esac
case "$OUT" in
  *"kw_search_total=0"*) pass "status reports kw_search_total=0" ;;
  *) fail "status reports kw_search_total=0" "got: $OUT" ;;
esac

# -------------------------------------------------------------------------
echo ""
echo "-- Step 0 budget enforcement (kw-search-can / kw-search / tick) --"

set +e
bash "$TRACKER" kw-search-can >/dev/null 2>&1
EXIT=$?
set -e
assert_exit_eq "kw-search-can allowed when fresh" 0 "$EXIT"

# Three visits exhausts the default cap of 3.
bash "$TRACKER" kw-search >/dev/null
bash "$TRACKER" kw-search >/dev/null
bash "$TRACKER" kw-search >/dev/null

set +e
OUT=$(bash "$TRACKER" kw-search-can 2>&1)
EXIT=$?
set -e
assert_exit_eq "kw-search-can denied after 3rd visit" 1 "$EXIT"
case "$OUT" in
  *"reason=max-knowledge-search-per-cycle"*) pass "denial reason surfaced" ;;
  *) fail "denial reason surfaced" "got: $OUT" ;;
esac

# tick clears kw_search_this_cycle but preserves kw_search_total.
bash "$TRACKER" tick --stuck=no >/dev/null
OUT=$(bash "$TRACKER" status)
case "$OUT" in
  *"kw_search_this_cycle=0/3"*) pass "tick reset kw_search_this_cycle" ;;
  *) fail "tick reset kw_search_this_cycle" "got: $OUT" ;;
esac
case "$OUT" in
  *"kw_search_total=3"*) pass "kw_search_total preserved across tick" ;;
  *) fail "kw_search_total preserved across tick" "got: $OUT" ;;
esac

set +e
bash "$TRACKER" kw-search-can >/dev/null 2>&1
EXIT=$?
set -e
assert_exit_eq "kw-search-can allowed again after tick" 0 "$EXIT"

bash "$TRACKER" stop || true
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID

# -------------------------------------------------------------------------
echo ""
echo "-- Registry loader smoke (lib/disprove_methods.py) --"

REGISTRY_OUT=$(python3 -c "
import sys
sys.path.insert(0, '$LEAN4_ROOT/lib')
from disprove_methods import load_registry
entries = load_registry()
print('count=' + str(len(entries)))
print('ids=' + ','.join(e.id for e in entries))
print('has-lookup=' + str(any(e.id == 'lookup' for e in entries)).lower())
")

echo "$REGISTRY_OUT"
case "$REGISTRY_OUT" in
  *"count=6"*) pass "registry has 6 entries" ;;
  *) fail "registry has 6 entries" "got: $REGISTRY_OUT" ;;
esac
case "$REGISTRY_OUT" in
  *"has-lookup=false"*) pass "lookup family removed" ;;
  *) fail "lookup family removed" "got: $REGISTRY_OUT" ;;
esac

# -------------------------------------------------------------------------
echo ""
echo "-- Custom budget (non-default --knowledge-search-budget) --"

LEAN4_SESSION_ID=$(bash "$TRACKER" init \
  --max-cycles=5 \
  --max-stuck=2 \
  --max-knowledge-search-per-cycle=1 \
  2>/dev/null)
export LEAN4_SESSION_ID

set +e
bash "$TRACKER" kw-search-can >/dev/null 2>&1
EXIT=$?
set -e
assert_exit_eq "kw-search-can allowed at budget=1, count=0" 0 "$EXIT"

bash "$TRACKER" kw-search >/dev/null
set +e
bash "$TRACKER" kw-search-can >/dev/null 2>&1
EXIT=$?
set -e
assert_exit_eq "kw-search-can denied at budget=1, count=1" 1 "$EXIT"

bash "$TRACKER" stop || true
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID

# -------------------------------------------------------------------------
echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]
