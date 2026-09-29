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
#   (d) trees whose only decls are unmatched shapes (indented) warn and
#       exit 1 instead of reporting a friendly zero;
#   (e) genuinely declaration-free trees still exit 0;
#   (f) #184: private/protected/local decls are extracted, private ones
#       counted per file (a same-named private decl elsewhere is no cover);
#   (g) #185: comments and strings never count as usages and a
#       commented-out declaration is never extracted (code-only mirror),
#       under both the rg and the PCRE-grep backends; a missing python3 is
#       a loud exit 2, never a clean result.
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
    PROBE_TREE="$tmpdir"

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
assert_out_has     "P2" "Found 11 declarations"         || p2_ok=0
assert_out_has     "P2" "dead_axiom"                    || p2_ok=0
assert_out_has     "P2" "dead_constant"                 || p2_ok=0
assert_out_has     "P2" "dead_noncomp"                  || p2_ok=0
assert_out_has     "P2" "dead_unsafe"                   || p2_ok=0
assert_out_has     "P2" "dead_partial"                  || p2_ok=0
assert_out_has     "P2" "dead_nonrec"                   || p2_ok=0
assert_out_has     "P2" "DeadStruct"                    || p2_ok=0
assert_out_has     "P2" "DeadClass"                     || p2_ok=0
assert_out_has     "P2" "DeadInductive"                 || p2_ok=0
assert_out_has     "P2" "Potentially unused: 9"         || p2_ok=0
assert_exit        "P2" 1                               || p2_ok=0
if [[ $p2_ok -eq 1 ]]; then
    echo "  PASS: P2 expanded-classes — axiom/constant/struct/class/inductive/modifier defs all extracted"
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
# Probe 4 — private_decls (#184): private decls are extracted; `helper`
# is used in its file, `hidden` is flagged with its location.
# ---------------------------------------------------------------------------
run_probe "P4 private-decls" private_decls
p4_ok=1
assert_out_has     "P4" "Found 3 declarations"          || p4_ok=0
assert_out_has     "P4" "hidden"                        || p4_ok=0
assert_out_has     "P4" "(private)"                     || p4_ok=0
assert_out_has     "P4" "Location:"                     || p4_ok=0
assert_out_has     "P4" "Potentially unused: 1"         || p4_ok=0
assert_out_missing "P4" "declaration-shaped content exists" || p4_ok=0
assert_exit        "P4" 1                               || p4_ok=0
if [[ $p4_ok -eq 1 ]]; then
    echo "  PASS: P4 private-decls — private decls extracted; only hidden flagged"
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
run_probe "P8 report-only shape" indented_modifier --report-only
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
# Probe 11 — private_collision (#184): the same private name in two
# files. A.lean's copy is used there; B.lean's is not and must be flagged
# — project-wide counting would have hidden it. Location names B.lean.
# ---------------------------------------------------------------------------
run_probe "P11 private-collision" private_collision
p11_ok=1
assert_out_has     "P11" "helper"                        || p11_ok=0
assert_out_has     "P11" "(private)"                     || p11_ok=0
assert_out_has     "P11" "B.lean"                        || p11_ok=0
assert_out_has     "P11" "Potentially unused: 1"         || p11_ok=0
assert_out_has     "P11" "Total declarations: 4"         || p11_ok=0   # helper×2 files + useA + useB
assert_exit        "P11" 1                               || p11_ok=0
if [[ $p11_ok -eq 1 ]]; then
    echo "  PASS: P11 private-collision — file-local counting flags the dead copy in B.lean"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 12 — comments_strings (#185): mentions in a docstring, a nested
# block comment, a trailing line comment, a string literal and a
# multi-line string never count; a commented-out declaration is not
# extracted. real_thm is used by real code → only the four decls whose
# sole mention is in comment/string context are flagged.
# ---------------------------------------------------------------------------
_p12_assert() { # $1 label, $2 tree path the locations must be reported against
    local ok=1
    assert_out_has     "$1" "Found 8 declarations"          || ok=0   # commented_out not extracted
    assert_out_missing "$1" "commented_out"                 || ok=0
    assert_out_has     "$1" "doc_only_thm"                  || ok=0
    assert_out_has     "$1" "nested_only"                   || ok=0
    assert_out_has     "$1" "string_only"                   || ok=0
    assert_out_has     "$1" "line_only_in_string"           || ok=0
    assert_out_has     "$1" "Potentially unused: 4"         || ok=0
    assert_out_has     "$1" "Location: $2/Sample.lean"      || ok=0   # reported in the ORIGINAL tree, never the mirror
    assert_exit        "$1" 1                               || ok=0
    return $(( ok == 1 ? 0 : 1 ))
}
run_probe "P12 comments-strings" comments_strings
if _p12_assert "P12" "$PROBE_TREE"; then
    echo "  PASS: P12 comments-strings — comment/string mentions never count; commented-out decl not extracted"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 13 — the same fixture through the PCRE-grep fallback (rg hidden
# from PATH; the real grep must support -P, else SKIP). Both backends
# must agree.
# ---------------------------------------------------------------------------
if echo x | grep -oP 'x' >/dev/null 2>&1; then
    ((++PROBE_COUNTER))
    P13_DIR="$SCRATCH_ROOT/probe-$PROBE_COUNTER"
    mkdir -p "$P13_DIR/bin" "$P13_DIR/tree"
    cp -r "$FIXTURE_ROOT/comments_strings/." "$P13_DIR/tree/"
    for util in sort wc tr find sed awk head rm mktemp cat dirname grep python3; do
        src=$(command -v "$util" 2>/dev/null || true)
        [[ -n "$src" ]] && ln -s "$src" "$P13_DIR/bin/$util"
    done
    set +e
    PROBE_OUT=$(PATH="$P13_DIR/bin" "$BASH_FOR_COMPAT" "$UNUSED_SCRIPT" "$P13_DIR/tree" 2>&1)
    PROBE_EXIT=$?
    set -e
    # shellcheck disable=SC2001
    PROBE_OUT=$(sed "s/$(printf '\033')\[[0-9;]*m//g" <<< "$PROBE_OUT")
    p13_ok=1
    assert_out_has "P13" "ripgrep not found" || p13_ok=0   # the fallback really ran
    _p12_assert "P13" "$P13_DIR/tree" || p13_ok=0
    if [[ $p13_ok -eq 1 ]]; then
        echo "  PASS: P13 comments-strings via PCRE grep — fallback backend agrees"
        ((PASS++)) || true
    else
        ((FAIL++)) || true
    fi
else
    echo "  SKIP: P13 — no PCRE-capable grep to exercise the fallback"
fi

# ---------------------------------------------------------------------------
# Probe 14 — no python3: the code-only view cannot be built, so the
# script must fail LOUDLY (exit 2), never report a clean tree.
# ---------------------------------------------------------------------------
((++PROBE_COUNTER))
P14_DIR="$SCRATCH_ROOT/probe-$PROBE_COUNTER"
mkdir -p "$P14_DIR/bin" "$P14_DIR/tree"
cp "$FIXTURE_ROOT/all_used/Sample.lean" "$P14_DIR/tree/"
for util in sort wc tr find sed awk head rm mktemp cat dirname grep rg; do
    src=$(command -v "$util" 2>/dev/null || true)
    [[ -n "$src" ]] && ln -s "$src" "$P14_DIR/bin/$util"
done
set +e
PROBE_OUT=$(PATH="$P14_DIR/bin" "$BASH_FOR_COMPAT" "$UNUSED_SCRIPT" "$P14_DIR/tree" 2>&1)
PROBE_EXIT=$?
set -e
# shellcheck disable=SC2001
PROBE_OUT=$(sed "s/$(printf '\033')\[[0-9;]*m//g" <<< "$PROBE_OUT")
p14_ok=1
assert_out_has     "P14" "requires python3"                    || p14_ok=0
assert_out_missing "P14" "All declarations appear to be used"  || p14_ok=0
assert_exit        "P14" 2                                     || p14_ok=0
if [[ $p14_ok -eq 1 ]]; then
    echo "  PASS: P14 no-python3 — loud exit 2, never a clean result"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 15 — literals (#185 review): a char literal containing `"`, a raw
# string holding a declaration name, and an escaped newline inside a
# string. Exactly dead/dead2/dead3 flagged; `quote`, `text`, `s` used;
# dead3's location still says line 14 (newlines preserved).
# ---------------------------------------------------------------------------
run_probe "P15 literals" literals
p15_ok=1
assert_out_has     "P15" "Found 6 declarations"          || p15_ok=0
assert_out_has     "P15" "Potentially unused: 3"         || p15_ok=0
assert_out_has     "P15" "Location: $PROBE_TREE/Sample.lean:14:" || p15_ok=0
assert_exit        "P15" 1                               || p15_ok=0
for _used in quote text s; do
    if grep -qE "^  ✗ $_used\$" <<< "$PROBE_OUT"; then
        echo "  FAIL: P15 — used decl $_used flagged"; p15_ok=0
    fi
done
if [[ $p15_ok -eq 1 ]]; then
    echo "  PASS: P15 literals — char literal, raw string and escaped newline handled; lines preserved"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 16 — ignore_metadata (#185 review): `.ignore` excludes generated/.
# The rg backend must keep that exclusion when the search moves to the
# mirror, so `dead` (referenced only in generated/) is still flagged.
# (The PCRE-grep fallback has no exclusions, as before — rg only.)
# ---------------------------------------------------------------------------
if command -v rg >/dev/null 2>&1; then
    run_probe "P16 ignore-metadata" ignore_metadata
    p16_ok=1
    assert_out_has     "P16" "Mirrored 1 Lean file(s)"       || p16_ok=0
    assert_out_has     "P16" "dead"                          || p16_ok=0
    assert_out_has     "P16" "Potentially unused: 1"         || p16_ok=0
    assert_exit        "P16" 1                               || p16_ok=0
    if [[ $p16_ok -eq 1 ]]; then
        echo "  PASS: P16 ignore-metadata — rg exclusions preserved across the mirror"
        ((PASS++)) || true
    else
        ((FAIL++)) || true
    fi
else
    echo "  SKIP: P16 — ripgrep not available"
fi

# ---------------------------------------------------------------------------
# Probe 17 — private_count (#184 review): consistent summary units — two
# private `helper`s in two files are 2 declarations and 2 findings, never
# "Total 1, unused 2, usage rate -100%".
# ---------------------------------------------------------------------------
run_probe "P17 private-count" private_count
p17_ok=1
assert_out_has     "P17" "Total declarations: 2"         || p17_ok=0
assert_out_has     "P17" "Potentially unused: 2"         || p17_ok=0
assert_out_missing "P17" "Usage rate: -"                 || p17_ok=0
assert_exit        "P17" 1                               || p17_ok=0
if [[ $p17_ok -eq 1 ]]; then
    echo "  PASS: P17 private-count — summary units consistent"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 18 — unreadable directory (#185 review): a subdirectory the tool
# cannot traverse must make the analysis fail loudly (exit 2), never
# report a clean tree from the files it could read. Skipped as root.
# ---------------------------------------------------------------------------
if [[ "${EUID:-$(id -u)}" -ne 0 ]]; then
    ((++PROBE_COUNTER))
    P18_DIR="$SCRATCH_ROOT/probe-$PROBE_COUNTER"
    mkdir -p "$P18_DIR/secret"
    cp "$FIXTURE_ROOT/all_used/Sample.lean" "$P18_DIR/"
    printf 'def hidden_dead : Nat := 0\n' > "$P18_DIR/secret/Hidden.lean"
    chmod 000 "$P18_DIR/secret"
    set +e
    PROBE_OUT=$("$BASH_FOR_COMPAT" "$UNUSED_SCRIPT" "$P18_DIR" 2>&1)
    PROBE_EXIT=$?
    set -e
    chmod 755 "$P18_DIR/secret"
    # shellcheck disable=SC2001
    PROBE_OUT=$(sed "s/$(printf '\033')\[[0-9;]*m//g" <<< "$PROBE_OUT")
    p18_ok=1
    assert_out_has     "P18" "cannot analyze"                        || p18_ok=0
    assert_out_missing "P18" "All declarations appear to be used"    || p18_ok=0
    assert_exit        "P18" 2                                       || p18_ok=0
    if [[ $p18_ok -eq 1 ]]; then
        echo "  PASS: P18 unreadable-dir — loud exit 2, never a clean result"
        ((PASS++)) || true
    else
        ((FAIL++)) || true
    fi
else
    echo "  SKIP: P18 — running as root, directory permissions are not enforced"
fi

# ---------------------------------------------------------------------------
# Probe 19 — interpolation (#185 review): `{…}` inside s!"…" is code.
# `live` is used only from interpolations (one nested, three whose code
# holds a `}` inside a block comment / line comment / raw string) → used;
# `ghost` appears only in literal text and as the escaped `\{ghost}` →
# flagged; the `#check`s after those interpolations are not erased.
# ---------------------------------------------------------------------------
run_probe "P19 interpolation" interpolation
p19_ok=1
assert_out_has     "P19" "Found 8 declarations"          || p19_ok=0
assert_out_has     "P19" "Potentially unused: 1"         || p19_ok=0
assert_out_has     "P19" "  ✗ ghost"                     || p19_ok=0
assert_out_missing "P19" "  ✗ live"                      || p19_ok=0
assert_exit        "P19" 1                               || p19_ok=0
if [[ $p19_ok -eq 1 ]]; then
    echo "  PASS: P19 interpolation — interpolated code counts, literal text does not"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 20 — relative directory argument (#185 review): the documented
# `unused_declarations.sh src` form. The backend lists `src/Sample.lean`
# relative to the working directory; the mirror must resolve that the same
# way, and locations are reported with the relative path the user gave.
# ---------------------------------------------------------------------------
((++PROBE_COUNTER))
P20_DIR="$SCRATCH_ROOT/probe-$PROBE_COUNTER"
mkdir -p "$P20_DIR/src"
cp "$FIXTURE_ROOT/has_unused/Sample.lean" "$P20_DIR/src/"
set +e
PROBE_OUT=$(cd "$P20_DIR" && "$BASH_FOR_COMPAT" "$UNUSED_SCRIPT" src 2>&1)
PROBE_EXIT=$?
set -e
# shellcheck disable=SC2001
PROBE_OUT=$(sed "s/$(printf '\033')\[[0-9;]*m//g" <<< "$PROBE_OUT")
p20_ok=1
assert_out_has     "P20" "Location: src/Sample.lean:"    || p20_ok=0
assert_out_missing "P20" "cannot analyze"                || p20_ok=0
assert_exit        "P20" 1                               || p20_ok=0
if [[ $p20_ok -eq 1 ]]; then
    echo "  PASS: P20 relative-dir — 'unused_declarations.sh src' works, relative locations"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probes 21–23 (#185 review): token boundaries and interpolation starts.
# Each fixture has exactly one dead declaration and used declarations
# placed AFTER the tricky literal, so a literal that swallowed the rest of
# the file would show up as extra findings, not only as shifted lines.
# ---------------------------------------------------------------------------
_p21_23() {
    local label="$1" fixture="$2" found="$3"; shift 3
    run_probe "$label" "$fixture"
    local ok=1
    assert_out_has     "$label" "Found $found declarations"  || ok=0
    assert_out_has     "$label" "Potentially unused: 1"      || ok=0
    assert_out_has     "$label" "  ✗ dead"                   || ok=0
    assert_exit        "$label" 1                            || ok=0
    local used
    for used in "$@"; do
        if grep -qE "^  ✗ $used\$" <<< "$PROBE_OUT"; then
            echo "  FAIL: $label — used decl $used flagged"; ok=0
        fi
    done
    if [[ $ok -eq 1 ]]; then
        echo "  PASS: $label — only dead flagged"
        ((PASS++)) || true
    else
        ((FAIL++)) || true
    fi
}
_p21_23 "P21 unicode-tokens" unicode_tokens 3 live after
_p21_23 "P22 escaped-ident"  escaped_ident  2 live
_p21_23 "P23 interp-spacing" interp_spacing 3 live act

# ---------------------------------------------------------------------------
# Probe 24 (#185 review): which strings interpolate is Lean's syntax, not a
# name heuristic. `throwErrorAt ref "…"` (plain, indexed, `.missing` and
# `Syntax.«missing»` refs, comment before the string) and `trace[cls] "…"`
# interpolate → `live`, `used`, `usedDot`, `usedEsc` used; `logInfo`, `Lean.logInfo`, `panic!` take ordinary strings →
# `dead`, `dead2`, `dead3` (referenced only as `{…}` literal text) flagged.
# ---------------------------------------------------------------------------
run_probe "P24 interp-args" interp_args
p24_ok=1
assert_out_has     "P24" "Found 15 declarations"         || p24_ok=0
assert_out_has     "P24" "Potentially unused: 3"         || p24_ok=0
assert_exit        "P24" 1                               || p24_ok=0
for _d in dead dead2 dead3; do
    grep -qE "^  ✗ $_d\$" <<< "$PROBE_OUT" \
        || { echo "  FAIL: P24 — $_d (ordinary-string reference) not flagged"; p24_ok=0; }
done
for _u in live used usedDot usedEsc; do
    ! grep -qE "^  ✗ $_u\$" <<< "$PROBE_OUT" \
        || { echo "  FAIL: P24 — $_u (interpolated reference) flagged"; p24_ok=0; }
done
if [[ $p24_ok -eq 1 ]]; then
    echo "  PASS: P24 interp-args — throwErrorAt/trace[] interpolate; logInfo/panic! strings do not"
    ((PASS++)) || true
else
    ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
echo ""
echo "=== test_unused_declarations.sh: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]
