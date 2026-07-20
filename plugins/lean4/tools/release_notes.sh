#!/usr/bin/env bash
# release_notes.sh — extract one version's CHANGELOG section (release notes).
#
# Usage: bash release_notes.sh <X.Y.Z> [changelog-path]
#
# Prints the body of the "## vX.Y.Z (…)" section (heading excluded) to
# stdout. Exits 1 with a message on stderr when the version argument is
# malformed, the exact heading is missing or appears more than once, or
# the section body is empty. changelog-path defaults to the repo-root
# CHANGELOG.md; tests pass a fixture path instead.
#
# Single source of truth for the extraction contract, shared by:
#   - .github/workflows/release.yml   (builds the release notes at publish time)
#   - .github/workflows/lint.yml      (release-contract job validates it PR-time)
#   - tools/lint_docs.sh Check 23     (exact-heading + non-empty gate)
#
# The heading match is exact ($2 == "vX.Y.Z"), not a substring grep —
# "## v4.5.6" must not be satisfied by "## v4.5.60". "###" subheadings
# do not terminate a section; only the next "## " heading does.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"

version="${1:-}"
CHANGELOG="${2:-$REPO_ROOT/CHANGELOG.md}"

if ! echo "$version" | grep -Eq '^[0-9]+\.[0-9]+\.[0-9]+$'; then
    echo "release_notes.sh: version '$version' is not X.Y.Z" >&2
    exit 1
fi

if [[ ! -f "$CHANGELOG" ]]; then
    echo "release_notes.sh: CHANGELOG not found at $CHANGELOG" >&2
    exit 1
fi

# Exactly one heading, or the extraction below would silently
# concatenate the bodies of every duplicate section into one blob of
# release notes.
heading_count="$(awk -v ver="v$version" '$1 == "##" && $2 == ver { n++ } END { print n + 0 }' "$CHANGELOG")"
if [[ "$heading_count" -ne 1 ]]; then
    echo "release_notes.sh: expected exactly one '## v$version' heading in $CHANGELOG, found $heading_count" >&2
    exit 1
fi

notes="$(awk -v ver="v$version" '
    $1 == "##" && $2 == ver { found = 1; next }
    $1 == "##"              { found = 0 }
    found                   { print }
' "$CHANGELOG")"

if ! echo "$notes" | grep -q '[^[:space:]]'; then
    echo "release_notes.sh: '## v$version' section in $CHANGELOG is empty" >&2
    exit 1
fi

printf '%s\n' "$notes"
