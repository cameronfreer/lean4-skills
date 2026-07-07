#!/usr/bin/env bash
set -euo pipefail

# Self-test for unused_declarations.sh — regression coverage for the
# silent-pass/false-positive hardening pass (sibling of #145's
# check_axioms_inline hardening). Verifies:
#   (a) rg-mode extraction produces bare decl names (the pre-fix
#       `path:name` corruption flagged EVERYTHING as unused);
#   (b) the expanded keyword set (axiom, constant, structure, and the
#       noncomputable/unsafe/partial/nonrec modifier prefixes) is
#       extracted and located;
#   (c) decl-free trees no longer kill the script under pipefail;
#   (d) trees whose only decls are unmatched shapes (private, indented)
#       warn and exit 1 instead of reporting a friendly zero;
#   (e) genuinely declaration-free trees still exit 0.
#
# Unlike test_check_axioms_inline.sh, no shim is needed: the script is
# pure grep/rg over the filesystem, so tests point it at fixture
# directories directly. Fixtures are copied to a temp dir per probe so
# the script can't disturb the sources.
#
# Probes invoke the script under $BASH_FOR_COMPAT (default /bin/bash) so
# the self-test runs under macOS Bash 3.2 in CI. On hosts without
# /bin/bash (e.g. NixOS) the test SKIPs gracefully.

BASH_FOR_COMPAT="${BASH_FOR_COMPAT:-/bin/bash}"
if [[ ! -x "$BASH_FOR_COMPAT" ]]; then
    echo "SKIP: $BASH_FOR_COMPAT not found — cannot run unused_declarations self-test"
    exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
UNUSED_SCRIPT="$PLUGIN_ROOT/lib/scripts/unused_declarations.sh"
FIXTURE_ROOT="$SCRIPT_DIR/fixtures/unused_decls"

if [[ ! -x "$UNUSED_SCRIPT" ]]; then
    echo "FAIL: unused_declarations.sh not found at $UNUSED_SCRIPT"
    exit 1
fi

# The script uses `grep -hoP` (PCRE) in its non-rg fallback, which BSD
# grep doesn't support. Require ripgrep OR a PCRE-capable grep; SKIP
# otherwise (matches the script's own degradation story).
if ! command -v rg >/dev/null 2>&1; then
    if ! echo x | grep -oP 'x' >/dev/null 2>&1; then
        echo "SKIP: neither ripgrep nor PCRE-capable grep available"
        exit 0
    fi
fi

PASS=0
FAIL=0

SCRATCH_ROOT=$(mktemp -d)
trap 'rm -rf "$SCRATCH_ROOT"' EXIT
PROBE_COUNTER=0

# ---------------------------------------------------------------------------
# Copies a fixture dir into scratch and runs unused_declarations.sh on it.
# Args: $1 probe label, $2 fixture subdir name, $3+ extra script args.
# Populates PROBE_OUT / PROBE_EXIT.
# ---------------------------------------------------------------------------
run_probe() {
    local label="$1"; shift
    local fixture="$1"; shift
    ((++PROBE_COUNTER))
    local tmpdir="$SCRATCH_ROOT/probe-$PROBE_COUNTER"
    mkdir -p "$tmpdir"
    cp -r "$FIXTURE_ROOT/$fixture/." "$tmpdir/"

    set +e
    PROBE_OUT=$("$BASH_FOR_COMPAT" "$UNUSED_SCRIPT" "$tmpdir" "$@" 2>&1)
    PROBE_EXIT=$?
    set -e
    # Strip ANSI color codes: the script embeds them mid-phrase (e.g.
    # "Found ${BOLD}9${NC} declarations"), which would break substring
    # assertions on the plain text. ESC comes from printf because BSD sed
    # (macOS CI) doesn't understand the \x1b escape in patterns.
    # shellcheck disable=SC2001  # regex replace — ${var//} can't do this
    PROBE_OUT=$(sed "s/$(printf '\033')\[[0-9;]*m//g" <<< "$PROBE_OUT")
}

assert_out_has() {
    local label="$1" want="$2"
    if grep -qF "$want" <<< "$PROBE_OUT"; then
        return 0
    fi
    echo "  FAIL: $label — expected output substring: $want"
    echo "        relevant output:"
    tail -20 <<< "$PROBE_OUT" | sed 's/^/          /'
    return 1
}

assert_out_missing() {
    local label="$1" bad="$2"
    if grep -qF "$bad" <<< "$PROBE_OUT"; then
        echo "  FAIL: $label — output unexpectedly contains: $bad"
        grep -F "$bad" <<< "$PROBE_OUT" | sed 's/^/          /'
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
# Probe 1 — has_unused: the pre-fix rg-mode regression. used_thm is
# referenced; only dead_thm may be flagged. Pre-fix (path:name
# corruption) flagged both and showed no locations.
# ---------------------------------------------------------------------------
run_probe "P1 has-unused" has_unused
p1_ok=1
assert_out_has     "P1" "Found 3 declarations"          || p1_ok=0
assert_out_has     "P1" "dead_thm"                      || p1_ok=0
assert_out_has     "P1" "Potentially unused: 1"         || p1_ok=0
assert_out_has     "P1" "Location:"                     || p1_ok=0
assert_exit        "P1" 1                               || p1_ok=0
if [[ $p1_ok -eq 1 ]]; then
    echo "  PASS: P1 has-unused — only dead_thm flagged, with location (rg path-prefix regression)"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 2 — expanded_classes: axiom/constant/structure + all four
# modifier-prefixed defs extracted; exactly the 8 dead ones flagged.
# ---------------------------------------------------------------------------
run_probe "P2 expanded-classes" expanded_classes
p2_ok=1
assert_out_has     "P2" "Found 9 declarations"          || p2_ok=0
assert_out_has     "P2" "dead_axiom"                    || p2_ok=0
assert_out_has     "P2" "dead_constant"                 || p2_ok=0
assert_out_has     "P2" "dead_noncomp"                  || p2_ok=0
assert_out_has     "P2" "dead_unsafe"                   || p2_ok=0
assert_out_has     "P2" "dead_partial"                  || p2_ok=0
assert_out_has     "P2" "dead_nonrec"                   || p2_ok=0
assert_out_has     "P2" "DeadStruct"                    || p2_ok=0
assert_out_has     "P2" "Potentially unused: 7"         || p2_ok=0
assert_exit        "P2" 1                               || p2_ok=0
if [[ $p2_ok -eq 1 ]]; then
    echo "  PASS: P2 expanded-classes — axiom/constant/struct/modifier defs all extracted"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 3 — all_used: every decl referenced; green verdict, exit 0.
# ---------------------------------------------------------------------------
run_probe "P3 all-used" all_used
p3_ok=1
assert_out_has     "P3" "All declarations appear to be used" || p3_ok=0
assert_exit        "P3" 0                                    || p3_ok=0
if [[ $p3_ok -eq 1 ]]; then
    echo "  PASS: P3 all-used — green verdict, exit 0"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 4 — private_only: extraction finds nothing, but the tree has
# decl-shaped content. Shape heuristic must warn + exit 1 (not the
# friendly "No declarations found" + exit 0).
# ---------------------------------------------------------------------------
run_probe "P4 private-only" private_only
p4_ok=1
assert_out_has     "P4" "declaration-shaped content exists" || p4_ok=0
assert_out_missing "P4" "No declarations found"             || p4_ok=0
assert_exit        "P4" 1                                   || p4_ok=0
if [[ $p4_ok -eq 1 ]]; then
    echo "  PASS: P4 private-only — shape heuristic warns, exit 1"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 5 — imports_only: genuinely decl-free. Pre-fix, pipefail killed
# the script mid-run here (rg exits 1 on no matches). Post-fix: clean
# "No declarations found" + exit 0, and no shape warning.
# ---------------------------------------------------------------------------
run_probe "P5 imports-only" imports_only
p5_ok=1
assert_out_has     "P5" "No declarations found"             || p5_ok=0
assert_out_missing "P5" "declaration-shaped content exists" || p5_ok=0
assert_exit        "P5" 0                                   || p5_ok=0
if [[ $p5_ok -eq 1 ]]; then
    echo "  PASS: P5 imports-only — clean exit 0 (pipefail crash regression)"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 6 — mixed_dir: cross-file usage counting. shared_thm defined in
# Used.lean, referenced in Dead.lean → used. local_dead referenced
# nowhere → flagged.
# ---------------------------------------------------------------------------
run_probe "P6 mixed-dir" mixed_dir
p6_ok=1
assert_out_has     "P6" "local_dead"                    || p6_ok=0
assert_out_has     "P6" "Potentially unused: 1"         || p6_ok=0
assert_exit        "P6" 1                               || p6_ok=0
if [[ $p6_ok -eq 1 ]]; then
    echo "  PASS: P6 mixed-dir — cross-file usage counted; only local_dead flagged"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 7 — --report-only on a tree with unused decls: findings exit 0.
# (Coverage failures like P4's shape warning deliberately do NOT get
# this treatment — mirroring check_axioms_inline's policy — but plain
# findings do.)
# ---------------------------------------------------------------------------
run_probe "P7 report-only" has_unused --report-only
p7_ok=1
assert_out_has     "P7" "Potentially unused: 1"         || p7_ok=0
assert_exit        "P7" 0                               || p7_ok=0
if [[ $p7_ok -eq 1 ]]; then
    echo "  PASS: P7 report-only — findings exit 0 under the flag"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 8 — --report-only does NOT excuse the shape-heuristic exit.
# A tree the analysis cannot cover must exit 1 regardless of the flag.
# ---------------------------------------------------------------------------
run_probe "P8 report-only shape" private_only --report-only
p8_ok=1
assert_out_has     "P8" "declaration-shaped content exists" || p8_ok=0
assert_exit        "P8" 1                                   || p8_ok=0
if [[ $p8_ok -eq 1 ]]; then
    echo "  PASS: P8 report-only+shape — coverage failure still exit 1"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 9 — indented_modifier: the only decl is indented AND
# modifier-prefixed (`  noncomputable def hidden`). Extraction can't see
# it; the shape heuristic must catch it (optional indent + optional
# modifier before the keyword) and exit 1. Reviewer-caught: first-pass
# heuristic matched indented `def` but not indented `noncomputable def`.
# ---------------------------------------------------------------------------
run_probe "P9 indented-modifier" indented_modifier
p9_ok=1
assert_out_has     "P9" "declaration-shaped content exists" || p9_ok=0
assert_out_missing "P9" "No declarations found"             || p9_ok=0
assert_exit        "P9" 1                                   || p9_ok=0
if [[ $p9_ok -eq 1 ]]; then
    echo "  PASS: P9 indented-modifier — heuristic catches indented noncomputable def"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 10 — no rg, no PCRE grep: the script must fail LOUDLY (exit 2
# with an error naming the requirement), not report "No declarations
# found" + exit 0. Reviewer-caught false green: with rg hidden and a
# BSD-style grep that rejects -P, `|| true` masked the extraction
# failure entirely.
#
# Simulated via a constrained PATH: symlinks to the real utilities the
# script needs, a `grep` shim that rejects any -P usage (BSD behavior),
# and NO rg.
# ---------------------------------------------------------------------------
((++PROBE_COUNTER))
P10_DIR="$SCRATCH_ROOT/probe-$PROBE_COUNTER"
mkdir -p "$P10_DIR/bin" "$P10_DIR/tree"
cp "$FIXTURE_ROOT/has_unused/Sample.lean" "$P10_DIR/tree/"

# Symlink the utilities the script needs (resolved from the current PATH).
for util in sort wc tr find sed awk head rm mktemp cat dirname; do
    src=$(command -v "$util" 2>/dev/null || true)
    [[ -n "$src" ]] && ln -s "$src" "$P10_DIR/bin/$util"
done
REAL_GREP=$(command -v grep)
cat > "$P10_DIR/bin/grep" <<EOF
#!$BASH_FOR_COMPAT
# BSD-style grep shim: reject any -P (PCRE) usage, delegate the rest.
for a in "\$@"; do
    case "\$a" in
        --) break ;;
        -*P*) echo "grep: invalid option -- P" >&2; exit 2 ;;
        -*) ;;
        *) break ;;
    esac
done
exec "$REAL_GREP" "\$@"
EOF
chmod +x "$P10_DIR/bin/grep"

set +e
PROBE_OUT=$(PATH="$P10_DIR/bin" "$BASH_FOR_COMPAT" "$UNUSED_SCRIPT" "$P10_DIR/tree" 2>&1)
PROBE_EXIT=$?
set -e
# shellcheck disable=SC2001  # regex replace — ${var//} can't do this
PROBE_OUT=$(sed "s/$(printf '\033')\[[0-9;]*m//g" <<< "$PROBE_OUT")

p10_ok=1
assert_out_has     "P10" "requires ripgrep"             || p10_ok=0
assert_out_missing "P10" "No declarations found"        || p10_ok=0
assert_exit        "P10" 2                              || p10_ok=0
if [[ $p10_ok -eq 1 ]]; then
    echo "  PASS: P10 no-PCRE-grep — loud config error, exit 2 (not false green)"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
echo ""
echo "=== test_unused_declarations.sh: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]
