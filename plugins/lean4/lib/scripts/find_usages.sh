#!/usr/bin/env bash
#
# find_usages.sh - Find all uses of a theorem/lemma/definition in Lean project
#
# Usage:
#   ./find_usages.sh <identifier> [directory]
#
# Finds all locations where a Lean identifier (theorem, lemma, def, etc.) is used.
# Excludes the definition itself, focuses on actual usages.
#
# Examples:
#   ./find_usages.sh exchangeable_iff_contractable
#   ./find_usages.sh measure_eq_of_fin_marginals_eq src/
#   ./find_usages.sh prefixCylinder .
#
# Output:
#   - File locations with line numbers
#   - Context showing how the identifier is used
#   - Summary statistics
#
# Features:
#   - Auto-detects ripgrep for performance
#   - Shows context lines before/after usage
#   - Excludes comments and definition line
#   - Counts total usages

set -euo pipefail

# Configuration
IDENTIFIER="${1:-}"
SEARCH_DIR="${2:-.}"
CONTEXT_LINES=2

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

# Detect if ripgrep is available
if command -v rg &> /dev/null; then
    USE_RG=true
else
    USE_RG=false
fi

# Validate input
if [[ -z "$IDENTIFIER" ]]; then
    echo -e "${RED}Error: No identifier specified${NC}" >&2
    echo "Usage: $0 <identifier> [directory]" >&2
    echo "" >&2
    echo "Examples:" >&2
    echo "  $0 my_theorem" >&2
    echo "  $0 MyClass src/" >&2
    exit 1
fi

if [[ ! -d "$SEARCH_DIR" ]]; then
    echo -e "${RED}Error: Directory '$SEARCH_DIR' does not exist${NC}" >&2
    exit 1
fi

echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}Finding usages of: ${BOLD}$IDENTIFIER${NC}"
echo -e "${CYAN}Search directory: $SEARCH_DIR${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

# Temporary file for results
RESULTS_FILE=$(mktemp)
trap 'rm -f "$RESULTS_FILE"' EXIT

# Function to check if line is a definition
is_definition_line() {
    local line="$1"
    # Check if line defines the identifier (not just uses it)
    if echo "$line" | grep -qE "^[[:space:]]*(theorem|lemma|def|class|structure|inductive|axiom|instance|abbrev)[[:space:]]+$IDENTIFIER"; then
        return 0  # true - is definition
    fi
    return 1  # false - not definition
}

# Function to check if line is a comment
is_comment_line() {
    local line="$1"
    # Check if identifier only appears in comment
    local before_comment="${line%%--*}"
    if [[ "$before_comment" != *"$IDENTIFIER"* ]]; then
        return 0  # true - only in comment
    fi
    return 1  # false - not just in comment
}

# Search with ripgrep
if [[ "$USE_RG" == true ]]; then
    echo -e "${GREEN}Using ripgrep for fast search...${NC}"
    echo ""

    # Search for identifier in Lean files
    # -n: line numbers, -C: context, --color=always: colors
    rg -t lean \
        --line-number \
        --color=always \
        --heading \
        -C "$CONTEXT_LINES" \
        "\b$IDENTIFIER\b" \
        "$SEARCH_DIR" > "$RESULTS_FILE" 2>/dev/null || true

else
    echo -e "${YELLOW}Using grep (install ripgrep for better performance)${NC}"
    echo ""

    # Fallback to grep
    find "$SEARCH_DIR" -name "*.lean" -type f | while read -r file; do
        if grep -l "\b$IDENTIFIER\b" "$file" > /dev/null 2>&1; then
            echo -e "${BLUE}File: ${NC}$file"
            grep -n -C "$CONTEXT_LINES" --color=always "\b$IDENTIFIER\b" "$file" || true
            echo ""
        fi
    done > "$RESULTS_FILE"
fi

# Process results to filter out definitions and comments
USAGE_COUNT=0
FILE_COUNT=0
CURRENT_FILE=""

echo -e "${BOLD}USAGES:${NC}"
echo ""

while IFS= read -r line; do
    # Track file headers from ripgrep
    if [[ "$USE_RG" == true ]] && [[ "$line" =~ ^([^:]+)$ ]]; then
        # New file header
        if [[ -n "$CURRENT_FILE" ]]; then
            echo ""  # Blank line between files
        fi
        CURRENT_FILE="$1"
        FILE_COUNT=$((FILE_COUNT + 1))
        echo -e "${BLUE}${BOLD}$line${NC}"
        continue
    fi

    # Check if line contains the identifier
    if [[ "$line" == *"$IDENTIFIER"* ]]; then
        # Extract line content (after line number if present)
        if [[ "$line" =~ ^[[:space:]]*([0-9]+)[:-] ]]; then
            LINE_NUM="${BASH_REMATCH[1]}"
            LINE_CONTENT="${line#*:}"
            LINE_CONTENT="${LINE_CONTENT#*-}"  # Handle ripgrep context separator
        else
            LINE_CONTENT="$line"
        fi

        # Skip if it's a definition line
        if is_definition_line "$LINE_CONTENT"; then
            continue
        fi

        # Skip if only in comment
        if is_comment_line "$LINE_CONTENT"; then
            continue
        fi

        # This is a real usage!
        USAGE_COUNT=$((USAGE_COUNT + 1))
    fi

    # Print the line (with colors preserved)
    echo -e "$line"
done < "$RESULTS_FILE"

# Summary
echo ""
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}SUMMARY${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"

if [[ $USAGE_COUNT -eq 0 ]]; then
    echo -e "${YELLOW}No usages found${NC}"
    echo ""
    echo "Possible reasons:"
    echo "  • Identifier is defined but never used"
    echo "  • Identifier name is misspelled"
    echo "  • Identifier is only used in tests or other directories"
    echo ""
    echo "Try searching in the entire project:"
    echo "  $0 $IDENTIFIER ."
else
    echo -e "${GREEN}Found ${BOLD}$USAGE_COUNT${NC}${GREEN} usage(s) of '$IDENTIFIER'${NC}"

    # Estimate based on ripgrep output
    if [[ "$USE_RG" == true ]] && [[ -s "$RESULTS_FILE" ]]; then
        # Count unique files from ripgrep output
        FILE_COUNT=$(grep -E '^[^:]+\.lean$' "$RESULTS_FILE" 2>/dev/null | sort -u | wc -l | tr -d ' ')
        if [[ $FILE_COUNT -gt 0 ]]; then
            echo -e "${GREEN}Across ${BOLD}$FILE_COUNT${NC}${GREEN} file(s)${NC}"
        fi
    fi
fi

echo ""
echo -e "${CYAN}Tips:${NC}"
echo "  • Review usages before refactoring"
echo "  • Check if identifier can be private or removed"
echo "  • Use ${BOLD}#check $IDENTIFIER${NC} to see type"
echo "  • Use ${BOLD}#print $IDENTIFIER${NC} to see definition"
