#!/usr/bin/env bash
set -euo pipefail

# Self-test for tools/release_notes.sh — the shared CHANGELOG extraction
# contract that release.yml, lint.yml's release-contract job, and
# lint_docs.sh Check 23 all depend on. Verifies against fixture
# changelogs (second positional arg) that the script:
#   (a) extracts exactly the requested section's body (heading excluded,
#       "###" subheadings retained, neighboring sections excluded);
#   (b) rejects malformed and missing versions;
#   (c) is not fooled by a prefix-colliding heading (v1.2.30 ≠ v1.2.3 —
#       the substring-grep failure mode Check 23 used to have);
#   (d) rejects an empty section body;
#   (e) rejects duplicate headings for the same version (which the
#       extraction pass alone would silently concatenate).
#
# Probes invoke the script under $BASH_FOR_COMPAT (default /bin/bash) so
# the suite exercises macOS Bash 3.2 in CI. On hosts without /bin/bash
# the test SKIPs gracefully.

BASH_FOR_COMPAT="${BASH_FOR_COMPAT:-/bin/bash}"
if [[ ! -x "$BASH_FOR_COMPAT" ]]; then
    echo "SKIP: $BASH_FOR_COMPAT not found — cannot run release_notes self-test"
    exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
NOTES_SCRIPT="$PLUGIN_ROOT/tools/release_notes.sh"

if [[ ! -f "$NOTES_SCRIPT" ]]; then
    echo "FAIL: release_notes.sh not found at $NOTES_SCRIPT"
    exit 1
fi

PASS=0
FAIL=0

SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"' EXIT

pass() { echo "  PASS: $1"; PASS=$((PASS + 1)); }
fail() { echo "  FAIL: $1"; FAIL=$((FAIL + 1)); }

# run <version> <changelog> — captures stdout in $OUT, stderr in $ERR,
# exit code in $CODE (set -e safe).
run() {
    local _out_file="$SCRATCH/out" _err_file="$SCRATCH/err"
    CODE=0
    "$BASH_FOR_COMPAT" "$NOTES_SCRIPT" "$1" "$2" \
        > "$_out_file" 2> "$_err_file" || CODE=$?
    OUT="$(cat "$_out_file")"
    ERR="$(cat "$_err_file")"
}

GOOD="$SCRATCH/good.md"
cat > "$GOOD" <<'EOF'
# Changelog

## v1.2.30 (Feb 2026)

Prefix-collision decoy section.

## v1.2.3 (Jan 2026)

Target summary line.

### Subheading kept

- bullet one

## v1.2.2 (Dec 2025)

Previous section body.
EOF

# (a) exact extraction: body only, subheading kept, neighbors excluded
run 1.2.3 "$GOOD"
EXPECTED="$(printf '\nTarget summary line.\n\n### Subheading kept\n\n- bullet one\n')"
if [[ $CODE -eq 0 && "$OUT" == "$EXPECTED" ]]; then
    pass "extracts exactly the v1.2.3 section body (subheading kept, neighbors excluded)"
else
    fail "extraction mismatch (exit=$CODE): $OUT"
fi

# (c) prefix collision: v1.2.30 exists, v9.9.9 nothing — but the sharper
# probe is a changelog where ONLY the long version exists.
PREFIX_ONLY="$SCRATCH/prefix.md"
printf '## v1.2.30 (Feb 2026)\n\nLong-version body.\n' > "$PREFIX_ONLY"
run 1.2.3 "$PREFIX_ONLY"
if [[ $CODE -ne 0 && "$ERR" == *"found 0"* ]]; then
    pass "v1.2.30 heading does not satisfy a request for 1.2.3"
else
    fail "prefix collision accepted (exit=$CODE): $ERR"
fi
run 1.2.30 "$PREFIX_ONLY"
if [[ $CODE -eq 0 && "$OUT" == *"Long-version body."* ]]; then
    pass "the long version itself still extracts"
else
    fail "long version extraction broke (exit=$CODE): $ERR"
fi

# (b) missing and malformed versions
run 9.9.9 "$GOOD"
if [[ $CODE -ne 0 && "$ERR" == *"found 0"* ]]; then
    pass "missing version rejected"
else
    fail "missing version accepted (exit=$CODE): $ERR"
fi
run "1.2" "$GOOD"
if [[ $CODE -ne 0 && "$ERR" == *"not X.Y.Z"* ]]; then
    pass "malformed version rejected"
else
    fail "malformed version accepted (exit=$CODE): $ERR"
fi

# (d) empty section body
EMPTY="$SCRATCH/empty.md"
printf '## v2.0.0 (Mar 2026)\n\n## v1.9.9 (Feb 2026)\n\nOlder body.\n' > "$EMPTY"
run 2.0.0 "$EMPTY"
if [[ $CODE -ne 0 && "$ERR" == *"is empty"* ]]; then
    pass "empty section rejected"
else
    fail "empty section accepted (exit=$CODE): $OUT"
fi

# (e) duplicate headings — extraction alone would concatenate both bodies
DUP="$SCRATCH/dup.md"
printf '## v3.0.0 (Apr 2026)\n\nfirst\n\n## v2.9.9 (Mar 2026)\n\nmid\n\n## v3.0.0 (Apr 2026)\n\nsecond\n' > "$DUP"
run 3.0.0 "$DUP"
if [[ $CODE -ne 0 && "$ERR" == *"found 2"* ]]; then
    pass "duplicate headings rejected (found 2)"
else
    fail "duplicate headings accepted (exit=$CODE): $OUT"
fi

# missing changelog path
run 1.2.3 "$SCRATCH/does-not-exist.md"
if [[ $CODE -ne 0 && "$ERR" == *"not found"* ]]; then
    pass "missing changelog file rejected"
else
    fail "missing changelog accepted (exit=$CODE)"
fi

echo ""
echo "=== test_release_notes.sh: $PASS passed, $FAIL failed ==="
[[ $FAIL -eq 0 ]]
