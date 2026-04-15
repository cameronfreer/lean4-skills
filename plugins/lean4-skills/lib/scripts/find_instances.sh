#!/usr/bin/env bash
#
# find_instances.sh - Find type class instances in mathlib
#
# Usage:
#   ./find_instances.sh <type-class-name> [--verbose]
#
# Searches for instances of a given type class in mathlib. Useful when you need
# to understand how a type class is instantiated for different types, or to find
# patterns for writing your own instances.
#
# Examples:
#   ./find_instances.sh MeasurableSpace
#   ./find_instances.sh IsProbabilityMeasure --verbose
#   ./find_instances.sh Fintype

set -euo pipefail

# Configuration
MATHLIB_PATH="${MATHLIB_PATH:-.lake/packages/mathlib}"
QUERY="${1:-}"
VERBOSE="${2:-}"

# Escape regex metacharacters in query for use in grep/rg patterns
escape_regex() {
    printf '%s' "$1" | sed 's/[.[\*^$()+?{|\\]/\\&/g'
}

# Validate query
if [[ -z "$QUERY" ]]; then
    echo -e "Error: No type class name specified" >&2
    echo "Usage: $0 <type-class-name> [--verbose]" >&2
    echo "" >&2
    echo "Examples:" >&2
    echo "  $0 MeasurableSpace" >&2
    echo "  $0 IsProbabilityMeasure --verbose" >&2
    echo "  $0 Fintype" >&2
    exit 1
fi

# Escape query for regex matching
ESCAPED_QUERY=$(escape_regex "$QUERY")

# Lean identifier boundary pattern for word boundaries
# Prevents matching Fintype when searching for Fin
LEAN_ID_AFTER='($|[^A-Za-z0-9_'"'"'.])'

# Detect if ripgrep is available (faster)
if command -v rg &> /dev/null; then
    USE_RG=true
else
    USE_RG=false
fi

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Verify mathlib exists
if [[ ! -d "$MATHLIB_PATH" ]]; then
    echo -e "${RED}Error: mathlib not found at $MATHLIB_PATH${NC}" >&2
    echo "Set MATHLIB_PATH environment variable or run from a Lean project root" >&2
    exit 1
fi

echo -e "${BLUE}Searching for instances of: ${YELLOW}$QUERY${NC}"
echo

# Search for instance declarations (use escaped query with word boundary for regex safety)
echo -e "${GREEN}Instance declarations:${NC}"
if [[ "$USE_RG" == true ]]; then
    rg -t lean "^instance.*:.*$ESCAPED_QUERY$LEAN_ID_AFTER" "$MATHLIB_PATH" -n --heading --color=always | head -80
else
    find "$MATHLIB_PATH" -name "*.lean" -type f -exec grep -lE "^instance.*:.*$ESCAPED_QUERY$LEAN_ID_AFTER" {} \; | head -20 | while read -r file; do
        echo -e "${BLUE}File: ${NC}$file"
        grep -nE "^instance.*:.*$ESCAPED_QUERY$LEAN_ID_AFTER" "$file" | head -3
        echo
    done
fi

echo
echo -e "${GREEN}Deriving instances:${NC}"
if [[ "$USE_RG" == true ]]; then
    rg -t lean "deriving.*$ESCAPED_QUERY$LEAN_ID_AFTER" "$MATHLIB_PATH" -n --heading --color=always | head -40
else
    find "$MATHLIB_PATH" -name "*.lean" -type f -exec grep -lE "deriving.*$ESCAPED_QUERY$LEAN_ID_AFTER" {} \; | head -10 | while read -r file; do
        echo -e "${BLUE}File: ${NC}$file"
        grep -nE "deriving.*$ESCAPED_QUERY$LEAN_ID_AFTER" "$file" | head -2
        echo
    done
fi

if [[ "$VERBOSE" == "--verbose" ]]; then
    echo
    echo -e "${CYAN}Implicit instance arguments:${NC}"
    if [[ "$USE_RG" == true ]]; then
        rg -t lean "\[$ESCAPED_QUERY$LEAN_ID_AFTER" "$MATHLIB_PATH" -n --heading --color=always | head -40
    else
        find "$MATHLIB_PATH" -name "*.lean" -type f -exec grep -lE "\[$ESCAPED_QUERY$LEAN_ID_AFTER" {} \; | head -10 | while read -r file; do
            echo -e "${BLUE}File: ${NC}$file"
            grep -nE "\[$ESCAPED_QUERY$LEAN_ID_AFTER" "$file" | head -2
            echo
        done
    fi
fi

echo
echo -e "${YELLOW}Tip: Import the file with:${NC}"
echo -e "  import Mathlib.Path.To.File"
echo
echo -e "${YELLOW}Tip: Check instance with:${NC}"
echo -e "  #check (inferInstance : $QUERY YourType)"
echo
echo -e "${YELLOW}Tip: See all instances for a type:${NC}"
echo -e "  #synth $QUERY YourType"
