#!/usr/bin/env bash
#
# dependency_graph.sh - Visualize theorem dependencies
#
# Usage:
#   ./dependency_graph.sh <file> [--format=dot|text]
#
# Analyzes a Lean file to extract theorem dependencies and outputs either:
#   - DOT format (for graphviz visualization)
#   - Text format (simple dependency tree)
#
# Examples:
#   ./dependency_graph.sh MyFile.lean
#   ./dependency_graph.sh MyFile.lean --format=dot | dot -Tpng > deps.png
#   ./dependency_graph.sh MyFile.lean --format=text

set -euo pipefail

# Configuration
FILE="${1:-}"
FORMAT="text"

# Parse format option
for arg in "$@"; do
    if [[ "$arg" == --format=* ]]; then
        FORMAT="${arg#--format=}"
    fi
done

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Validate input
if [[ -z "$FILE" ]]; then
    echo -e "${RED}Error: No file specified${NC}" >&2
    echo "Usage: $0 <file> [--format=dot|text]" >&2
    exit 1
fi

if [[ ! -f "$FILE" ]]; then
    echo -e "${RED}Error: $FILE is not a file${NC}" >&2
    exit 1
fi

if [[ ! "$FILE" =~ \.lean$ ]]; then
    echo -e "${RED}Error: $FILE is not a Lean file${NC}" >&2
    exit 1
fi

# Extract theorem names
THEOREMS=$(grep -E '^(theorem|lemma) ' "$FILE" | sed -E 's/^(theorem|lemma) +([^ :(]+).*/\2/' || true)

if [[ -z "$THEOREMS" ]]; then
    echo -e "${YELLOW}No theorems or lemmas found${NC}" >&2
    exit 0
fi

# For each theorem, find references to other theorems
case "$FORMAT" in
    dot)
        echo "digraph dependencies {"
        echo "  rankdir=TB;"
        echo "  node [shape=box, style=rounded];"
        echo ""

        # Add all nodes
        while IFS= read -r theorem; do
            echo "  \"$theorem\" [label=\"$theorem\"];"
        done <<< "$THEOREMS"

        echo ""

        # Add edges
        while IFS= read -r theorem; do
            # Find the theorem body (simplified - between theorem line and next theorem/end)
            BODY=$(awk "/^(theorem|lemma) $theorem /,/^(theorem|lemma|def|end) /" "$FILE" | tail -n +2)

            # Check which other theorems are referenced
            while IFS= read -r other; do
                if [[ "$other" != "$theorem" ]] && echo "$BODY" | grep -qw "$other"; then
                    echo "  \"$theorem\" -> \"$other\";"
                fi
            done <<< "$THEOREMS"
        done <<< "$THEOREMS"

        echo "}"
        ;;

    text)
        echo -e "${BLUE}Dependency tree for: ${YELLOW}$FILE${NC}"
        echo

        # Count dependencies for each theorem (Bash 3.2 compatible - no associative arrays)
        TEMP_COUNTS=$(mktemp)
        trap 'rm -f "$TEMP_COUNTS"' EXIT

        while IFS= read -r theorem; do
            BODY=$(awk "/^(theorem|lemma) $theorem /,/^(theorem|lemma|def|end) /" "$FILE" | tail -n +2)
            COUNT=0
            while IFS= read -r other; do
                if [[ "$other" != "$theorem" ]] && echo "$BODY" | grep -qw "$other"; then
                    ((COUNT++))
                fi
            done <<< "$THEOREMS"
            echo "$COUNT:$theorem" >> "$TEMP_COUNTS"
        done <<< "$THEOREMS"

        # Display theorems sorted by dependency count
        sort -rn "$TEMP_COUNTS" | while IFS=: read -r count theorem; do
            if [[ $count -eq 0 ]]; then
                echo -e "${GREEN}✓${NC} $theorem (leaf - no internal dependencies)"
            elif [[ $count -eq 1 ]]; then
                echo -e "${YELLOW}→${NC} $theorem (depends on 1 theorem)"
            else
                echo -e "${RED}→${NC} $theorem (depends on $count theorems)"
            fi

            # Show what it depends on
            BODY=$(awk "/^(theorem|lemma) $theorem /,/^(theorem|lemma|def|end) /" "$FILE" | tail -n +2)
            while IFS= read -r other; do
                if [[ "$other" != "$theorem" ]] && echo "$BODY" | grep -qw "$other"; then
                    echo "    ↳ $other"
                fi
            done <<< "$THEOREMS"
        done

        echo
        echo -e "${BLUE}Summary:${NC}"
        TOTAL=$(echo "$THEOREMS" | wc -l)
        LEAVES=$(cut -d: -f1 "$TEMP_COUNTS" | grep -c "^0$" || true)
        echo "  Total theorems: $TOTAL"
        echo "  Leaf theorems (no dependencies): $LEAVES"
        echo "  Internal theorems: $((TOTAL - LEAVES))"
        ;;

    *)
        echo -e "${RED}Error: Invalid format: $FORMAT${NC}" >&2
        echo "Valid formats: dot, text" >&2
        exit 1
        ;;
esac
