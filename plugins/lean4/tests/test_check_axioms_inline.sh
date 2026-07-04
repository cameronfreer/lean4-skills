#!/usr/bin/env bash
set -euo pipefail

# Self-test for check_axioms_inline.sh — regression coverage for #132.
# Verifies:
#   (a) namespace-stack walk produces correct qualified names on nested,
#       sibling, dotted, and section-mixed configurations;
#   (b) zero-coverage runs refuse to print the green verdict;
#   (c) directory-mode runs with any unverified file exit non-zero and do
#       NOT print the green verdict, even under --exit-zero-on-findings /
#       --report-only.
#
# Design: the script normally invokes `lake env lean`, which requires a
# real Lean toolchain. CI does not have one, so we put a fake `lake` shim
# on PATH. The shim emits canned "X depends on axioms:" output based on
# the requested name's prefix and logs every #print axioms name it saw
# into $SEEN_PRINTS_LOG, so we can assert on the appended region even
# though check_axioms_inline.sh restores the file before returning.
#
# Helpers invoke the script under $BASH_FOR_COMPAT (default /bin/bash) so
# the self-test runs under macOS Bash 3.2 in CI. On hosts without
# /bin/bash (e.g. NixOS) the test SKIPs gracefully.

BASH_FOR_COMPAT="${BASH_FOR_COMPAT:-/bin/bash}"
if [[ ! -x "$BASH_FOR_COMPAT" ]]; then
    echo "SKIP: $BASH_FOR_COMPAT not found — cannot run check_axioms_inline self-test"
    exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CHECK_SCRIPT="$PLUGIN_ROOT/lib/scripts/check_axioms_inline.sh"
FIXTURE_ROOT="$SCRIPT_DIR/fixtures/axiom_check"
SHIM_DIR="$FIXTURE_ROOT/bin"

if [[ ! -x "$CHECK_SCRIPT" ]]; then
    echo "FAIL: check_axioms_inline.sh not found at $CHECK_SCRIPT"
    exit 1
fi
if [[ ! -x "$SHIM_DIR/lake" ]]; then
    echo "FAIL: lake shim not executable at $SHIM_DIR/lake"
    exit 1
fi

PASS=0
FAIL=0

# Shared scratch root; each probe gets a numbered subdir. Cleaned up on EXIT.
SCRATCH_ROOT=$(mktemp -d)
trap 'rm -rf "$SCRATCH_ROOT"' EXIT
PROBE_COUNTER=0

# ---------------------------------------------------------------------------
# Runs check_axioms_inline.sh under the shim, with a per-probe SEEN_PRINTS_LOG.
# Copies the fixture(s) into a fresh subdir so a probe that mutates on failure
# doesn't corrupt the fixture source. The subdir persists until the EXIT trap
# so assertions can inspect PROBE_LOG after run_probe returns.
#
# Args:
#   $1  probe label (for output)
#   $2  path (relative to $FIXTURE_ROOT) OR "DIR:<f1>,<f2>,..."
#   $3+ extra args to pass to check_axioms_inline.sh
#
# Populates the globals PROBE_OUT, PROBE_EXIT, PROBE_LOG for the caller.
# ---------------------------------------------------------------------------
run_probe() {
    local label="$1"; shift
    local target_spec="$1"; shift
    ((++PROBE_COUNTER))
    local tmpdir="$SCRATCH_ROOT/probe-$PROBE_COUNTER"
    mkdir -p "$tmpdir"
    PROBE_LOG="$tmpdir/seen"
    : > "$PROBE_LOG"

    local target
    if [[ "$target_spec" == DIR:* ]]; then
        local files="${target_spec#DIR:}"
        local subdir="$tmpdir/dir"
        mkdir -p "$subdir"
        IFS=',' read -r -a _files <<< "$files"
        for f in "${_files[@]}"; do
            cp "$FIXTURE_ROOT/$f" "$subdir/"
        done
        target="$subdir"
    else
        cp "$FIXTURE_ROOT/$target_spec" "$tmpdir/"
        target="$tmpdir/$(basename "$target_spec")"
    fi

    set +e
    PROBE_OUT=$(
        PATH="$SHIM_DIR:$PATH" \
        SEEN_PRINTS_LOG="$PROBE_LOG" \
        "$BASH_FOR_COMPAT" "$CHECK_SCRIPT" "$target" "$@" 2>&1
    )
    PROBE_EXIT=$?
    set -e
}

# Fluent assertions ---------------------------------------------------------

assert_log_has() {
    local label="$1" want="$2"
    if grep -qxF "$want" "$PROBE_LOG"; then
        return 0
    fi
    echo "  FAIL: $label — expected SEEN_PRINTS_LOG line: $want"
    echo "        log contents:"
    sed 's/^/          /' "$PROBE_LOG" || true
    return 1
}

assert_log_missing() {
    local label="$1" bad="$2"
    if grep -qxF "$bad" "$PROBE_LOG"; then
        echo "  FAIL: $label — SEEN_PRINTS_LOG unexpectedly contains: $bad"
        echo "        log contents:"
        sed 's/^/          /' "$PROBE_LOG" || true
        return 1
    fi
}

assert_out_has() {
    local label="$1" want="$2"
    if grep -qF "$want" <<< "$PROBE_OUT"; then
        return 0
    fi
    echo "  FAIL: $label — expected output substring: $want"
    echo "        relevant output:"
    grep -F "${want:0:20}" <<< "$PROBE_OUT" | sed 's/^/          /' || true
    return 1
}

assert_out_missing() {
    local label="$1" bad="$2"
    if grep -qF "$bad" <<< "$PROBE_OUT"; then
        echo "  FAIL: $label — output unexpectedly contains: $bad"
        echo "        offending lines:"
        grep -F "$bad" <<< "$PROBE_OUT" | sed 's/^/          /' || true
        return 1
    fi
}

assert_exit() {
    local label="$1" want="$2"
    if [[ "$PROBE_EXIT" -eq "$want" ]]; then
        return 0
    fi
    echo "  FAIL: $label — expected exit $want, got $PROBE_EXIT"
    return 1
}

# ---------------------------------------------------------------------------
# Per-fixture probes (10)
# ---------------------------------------------------------------------------

# Probe 1 — single_namespace.lean (the #132 minimal repro)
run_probe "P1 single-ns" single_namespace.lean
p1_ok=1
assert_log_has "P1"    "Foo.bar"                     || p1_ok=0
assert_log_has "P1"    "Foo.baz"                     || p1_ok=0
assert_out_has "P1"    "Files checked: 1"            || p1_ok=0
assert_out_has "P1"    "Declarations checked: 2"     || p1_ok=0
assert_out_has "P1"    "All files use only standard axioms" || p1_ok=0
assert_exit    "P1" 0                                || p1_ok=0
if [[ $p1_ok -eq 1 ]]; then
    echo "  PASS: P1 single-ns — Foo.bar / Foo.baz resolve; 1/2 green"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 2 — nested_namespace.lean
run_probe "P2 nested" nested_namespace.lean
p2_ok=1
assert_log_has "P2"    "A.B.foo"                     || p2_ok=0
assert_log_missing "P2" "A.foo"                      || p2_ok=0
assert_log_missing "P2" "B.foo"                      || p2_ok=0
assert_out_has "P2"    "Declarations checked: 1"     || p2_ok=0
assert_exit    "P2" 0                                || p2_ok=0
if [[ $p2_ok -eq 1 ]]; then
    echo "  PASS: P2 nested — A.B.foo resolves (not A.foo, not B.foo)"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 3 — dotted_namespace.lean
run_probe "P3 dotted" dotted_namespace.lean
p3_ok=1
assert_log_has "P3"    "Foo.Bar.quux"                || p3_ok=0
assert_exit    "P3" 0                                || p3_ok=0
if [[ $p3_ok -eq 1 ]]; then
    echo "  PASS: P3 dotted — Foo.Bar.quux resolves as single frame"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 4 — multi_sibling_namespace.lean
run_probe "P4 siblings" multi_sibling_namespace.lean
p4_ok=1
assert_log_has "P4"    "A.foo"                       || p4_ok=0
assert_log_has "P4"    "B.bar"                       || p4_ok=0
assert_log_missing "P4" "A.bar"                      || p4_ok=0
assert_exit    "P4" 0                                || p4_ok=0
if [[ $p4_ok -eq 1 ]]; then
    echo "  PASS: P4 siblings — A.foo AND B.bar resolve (no cross-leak)"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 5 — bare_end.lean
run_probe "P5 bare-end" bare_end.lean
p5_ok=1
assert_log_has "P5"    "A.foo"                       || p5_ok=0
assert_log_has "P5"    "bar"                         || p5_ok=0
assert_log_missing "P5" "A.bar"                      || p5_ok=0
assert_exit    "P5" 0                                || p5_ok=0
if [[ $p5_ok -eq 1 ]]; then
    echo "  PASS: P5 bare-end — bare end pops; bar stays root-scope"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 6 — section_inside_namespace.lean
run_probe "P6 anon-section" section_inside_namespace.lean
p6_ok=1
assert_log_has "P6"    "A.sec_inside"                || p6_ok=0
assert_log_has "P6"    "A.after_sec"                 || p6_ok=0
assert_exit    "P6" 0                                || p6_ok=0
if [[ $p6_ok -eq 1 ]]; then
    echo "  PASS: P6 anon-section — sections don't leak; bare end pops sec only"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 7 — named_section_inside_namespace.lean
run_probe "P7 named-section" named_section_inside_namespace.lean
p7_ok=1
assert_log_has "P7"    "A.sec_named"                 || p7_ok=0
assert_log_has "P7"    "A.after_sec"                 || p7_ok=0
assert_exit    "P7" 0                                || p7_ok=0
if [[ $p7_ok -eq 1 ]]; then
    echo "  PASS: P7 named-section — section S doesn't prefix; end S pops it"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 8 — unqualified.lean
run_probe "P8 unqualified" unqualified.lean
p8_ok=1
assert_log_has "P8"    "foo"                         || p8_ok=0
assert_exit    "P8" 0                                || p8_ok=0
if [[ $p8_ok -eq 1 ]]; then
    echo "  PASS: P8 unqualified — bare foo, no prefix"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 9 — custom_axiom.lean
run_probe "P9 custom-axiom" custom_axiom.lean
p9_ok=1
assert_log_has "P9"    "Sorry.needs_sorry"           || p9_ok=0
assert_out_has "P9"    "uses non-standard axiom: sorryAx" || p9_ok=0
assert_exit    "P9" 1                                || p9_ok=0
if [[ $p9_ok -eq 1 ]]; then
    echo "  PASS: P9 custom-axiom — sorryAx flagged in RED, exit 1"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 8b — no_axioms.lean: parser handles `'X' does not depend on any
# axioms` (modern Lean's output for decls with no axiom deps, e.g. a
# `True := trivial` proof). Must be counted as VERIFIED, not unverified.
run_probe "P8b no-axioms" no_axioms.lean
p8b_ok=1
assert_log_has     "P8b" "NoAxioms.depends_on_nothing"      || p8b_ok=0
assert_out_has     "P8b" "Files checked: 1"                 || p8b_ok=0
assert_out_has     "P8b" "Declarations checked: 1"          || p8b_ok=0
assert_out_has     "P8b" "All files use only standard axioms" || p8b_ok=0
assert_out_missing "P8b" "Unverified files"                 || p8b_ok=0
assert_exit        "P8b" 0                                  || p8b_ok=0
if [[ $p8b_ok -eq 1 ]]; then
    echo "  PASS: P8b no-axioms — 'does not depend on any axioms' counted as verified"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 9b — legacy_format.lean: parser handles the older multi-line
# `#print axioms` output format. Locks in back-compat with older Lean
# 4 versions after the modern-format parser update.
run_probe "P9b legacy-format" legacy_format.lean
p9b_ok=1
assert_log_has "P9b"   "Legacy.old_format_ok"        || p9b_ok=0
assert_out_has "P9b"   "All declarations use only standard axioms" || p9b_ok=0
assert_out_missing "P9b" "uses non-standard axiom"   || p9b_ok=0
assert_exit    "P9b" 0                               || p9b_ok=0
if [[ $p9b_ok -eq 1 ]]; then
    echo "  PASS: P9b legacy-format — legacy multi-line output still parsed as clean"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe 10 — zero_coverage.lean (the primary regression for #132)
run_probe "P10 zero-coverage" zero_coverage.lean
p10_ok=1
assert_log_has     "P10" "Unknown.cant_resolve_a"           || p10_ok=0
assert_log_has     "P10" "Unknown.cant_resolve_b"           || p10_ok=0
assert_out_has     "P10" "Zero declarations were verified"  || p10_ok=0
assert_out_missing "P10" "All files use only standard axioms" || p10_ok=0
assert_exit        "P10" 1                                  || p10_ok=0
if [[ $p10_ok -eq 1 ]]; then
    echo "  PASS: P10 zero-coverage — verdict withheld, exit 1 (primary #132 regression)"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Aggregate/directory-mode probes (5) — the directory-mode silent-drop bug.
# ---------------------------------------------------------------------------

# Probe D1 — dir with one clean + one unverified
run_probe "D1 mixed-dir" "DIR:single_namespace.lean,zero_coverage.lean"
d1_ok=1
assert_exit        "D1" 1                                  || d1_ok=0
assert_out_has     "D1" "Unverified files"                 || d1_ok=0
assert_out_has     "D1" "zero_coverage.lean"               || d1_ok=0
assert_out_missing "D1" "All files use only standard axioms" || d1_ok=0
assert_out_has     "D1" "Files checked: 1"                 || d1_ok=0
if [[ $d1_ok -eq 1 ]]; then
    echo "  PASS: D1 mixed-dir — clean+unverified: no green, exit 1 (load-bearing dir-mode test)"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe D2 — D1 with --exit-zero-on-findings
run_probe "D2 mixed-dir --exit-zero-on-findings" "DIR:single_namespace.lean,zero_coverage.lean" --exit-zero-on-findings
d2_ok=1
assert_exit        "D2" 1                                  || d2_ok=0
assert_out_missing "D2" "All files use only standard axioms" || d2_ok=0
if [[ $d2_ok -eq 1 ]]; then
    echo "  PASS: D2 mixed-dir + --exit-zero-on-findings — still exit 1 (flag doesn't excuse coverage failure)"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe D3 — D1 with --report-only (alias)
run_probe "D3 mixed-dir --report-only" "DIR:single_namespace.lean,zero_coverage.lean" --report-only
d3_ok=1
assert_exit        "D3" 1                                  || d3_ok=0
assert_out_missing "D3" "All files use only standard axioms" || d3_ok=0
if [[ $d3_ok -eq 1 ]]; then
    echo "  PASS: D3 mixed-dir + --report-only — same as D2, alias behavior locked in"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe D4 — single-file zero-coverage
run_probe "D4 zero-only" zero_coverage.lean
d4_ok=1
assert_exit        "D4" 1                                  || d4_ok=0
assert_out_has     "D4" "Zero declarations were verified"  || d4_ok=0
assert_out_missing "D4" "All files use only standard axioms" || d4_ok=0
assert_out_has     "D4" "Declarations checked: 0"          || d4_ok=0
if [[ $d4_ok -eq 1 ]]; then
    echo "  PASS: D4 zero-only — single-file zero coverage: verdict withheld, exit 1"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe D5 — D4 with --exit-zero-on-findings
run_probe "D5 zero-only --exit-zero-on-findings" zero_coverage.lean --exit-zero-on-findings
d5_ok=1
assert_exit        "D5" 1                                  || d5_ok=0
assert_out_missing "D5" "All files use only standard axioms" || d5_ok=0
if [[ $d5_ok -eq 1 ]]; then
    echo "  PASS: D5 zero-only + --exit-zero-on-findings — flag doesn't suppress zero-coverage exit"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# Probe D6 — custom_axiom + zero_coverage combined. A run that has BOTH a
# real sorryAx finding AND an unverified file must surface the RED custom-
# axiom counts in the summary; the previous "verdict withheld because
# unverified" wording alone was false (the verified files were NOT clean).
# Reviewer-caught regression on the summary priority order.
run_probe "D6 custom+unverified" "DIR:custom_axiom.lean,zero_coverage.lean"
d6_ok=1
assert_exit        "D6" 1                                  || d6_ok=0
assert_out_has     "D6" "Files with non-standard axioms: 1" || d6_ok=0
assert_out_has     "D6" "uses non-standard axiom: sorryAx" || d6_ok=0
assert_out_has     "D6" "Unverified files"                 || d6_ok=0
assert_out_has     "D6" "Verdict also withheld"            || d6_ok=0
assert_out_missing "D6" "All files use only standard axioms" || d6_ok=0
assert_out_missing "D6" "Verified files use only standard axioms" || d6_ok=0
if [[ $d6_ok -eq 1 ]]; then
    echo "  PASS: D6 custom+unverified — RED count surfaces + yellow withhold note; no false-clean line"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
echo ""
echo "=== test_check_axioms_inline.sh: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]
