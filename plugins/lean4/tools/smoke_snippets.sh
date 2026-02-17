#!/usr/bin/env bash
# Lightweight smoke checks for advanced reference snippets.
# This is intentionally static (no Lean build required): it catches obvious
# placeholder leftovers and malformed fenced blocks.

set -euo pipefail

PLUGIN_ROOT="${LEAN4_PLUGIN_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
REF_DIR="$PLUGIN_ROOT/skills/lean4/references"
ISSUES=0

warn() {
    echo "⚠️  $1"
    ((ISSUES++)) || true
}

ok() {
    echo "✓ $1"
}

advanced_refs=(
    "grind-tactic.md"
    "simproc-patterns.md"
    "metaprogramming-patterns.md"
    "linter-authoring.md"
    "ffi-patterns.md"
    "verso-docs.md"
    "profiling-workflows.md"
)

for base in "${advanced_refs[@]}"; do
    file="$REF_DIR/$base"
    if [[ ! -f "$file" ]]; then
        warn "$base: file not found"
        continue
    fi

    fence_count=$(grep -c '^```' "$file" 2>/dev/null || true)
    if (( fence_count % 2 != 0 )); then
        warn "$base: unmatched markdown code fences (count=$fence_count)"
    fi

    # Scan only Lean fenced blocks for obvious placeholders.
    while IFS= read -r hit; do
        line_no=$(echo "$hit" | cut -d: -f1)
        kind=$(echo "$hit" | cut -d: -f2)
        case "$kind" in
            placeholder_example)
                warn "$base:$line_no: placeholder goal in Lean snippet"
                ;;
            ellipsis)
                warn "$base:$line_no: ellipsis placeholder ('...') in Lean snippet"
                ;;
        esac
    done < <(
        awk '
            BEGIN { in_lean = 0 }
            /^```lean[[:space:]]*$/ { in_lean = 1; next }
            /^```[[:space:]]*$/ && in_lean { in_lean = 0; next }
            !in_lean { next }
            {
              if ($0 ~ /example[[:space:]]*:[[:space:]]*(goal|complex_goal|some_sum|some_property)\b/) {
                printf "%d:placeholder_example\n", NR
              }
              if ($0 ~ /(^|[^[:alnum:]_])\.\.\.([^[:alnum:]_]|$)/ && $0 !~ /\[\.\.\.\]/) {
                printf "%d:ellipsis\n", NR
              }
            }
        ' "$file"
    )
done

if [[ $ISSUES -eq 0 ]]; then
    ok "Advanced reference snippet smoke checks passed"
    exit 0
else
    echo "⚠️  $ISSUES snippet smoke issue(s) found"
    exit 1
fi
