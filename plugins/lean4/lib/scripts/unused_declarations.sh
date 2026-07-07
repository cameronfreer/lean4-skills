#!/usr/bin/env bash
#
# unused_declarations.sh - Find unused theorems, lemmas, and definitions in Lean 4 project
#
# Usage:
#   ./unused_declarations.sh [directory] [--exit-zero-on-findings]
#
# Finds declarations (theorem, lemma, def) that are never used in the project.
#
# Examples:
#   ./unused_declarations.sh
#   ./unused_declarations.sh src/
#
# Output:
#   - List of unused declarations
#   - Suggestions for marking as private or removing
#   - Summary statistics

set -euo pipefail

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

# Configuration
EXIT_ZERO_ON_FINDINGS=""
SEARCH_DIR=""
for arg in "$@"; do
    case "$arg" in
        --exit-zero-on-findings|--report-only)
            EXIT_ZERO_ON_FINDINGS="true"
            ;;
        --*)
            echo -e "${RED}Error: Unknown flag: $arg${NC}" >&2
            exit 1
            ;;
        *)
            if [[ -n "$SEARCH_DIR" ]]; then
                echo -e "${RED}Error: Multiple directories specified: $SEARCH_DIR and $arg${NC}" >&2
                exit 1
            fi
            SEARCH_DIR="$arg"
            ;;
    esac
done
SEARCH_DIR="${SEARCH_DIR:-.}"

if [[ ! -d "$SEARCH_DIR" ]]; then
    echo -e "${RED}Error: $SEARCH_DIR is not a directory${NC}" >&2
    exit 1
fi

# Detect if ripgrep is available
if command -v rg &> /dev/null; then
    USE_RG=true
else
    USE_RG=false
    echo -e "${YELLOW}Note: ripgrep not found. Install ripgrep for 10-100x faster analysis${NC}"
    echo ""
fi

# Lean identifier boundary patterns
# Lean identifiers can contain: letters, digits, _, ' (prime), and . (qualified names)
# We need custom boundaries because \b doesn't work with ' or .
LEAN_ID_BEFORE='(^|[^A-Za-z0-9_'"'"'.])'
LEAN_ID_AFTER='($|[^A-Za-z0-9_'"'"'.])'

# Escape regex metacharacters in a declaration name
escape_regex() {
    printf '%s' "$1" | sed 's/[.[\*^$()+?{|\\]/\\&/g'
}

echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}UNUSED DECLARATIONS FINDER${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo -e "${BOLD}Searching in:${NC} $SEARCH_DIR"
echo ""

# Temporary files
DECLARATIONS=$(mktemp)
UNUSED=$(mktemp)
trap 'rm -f "$DECLARATIONS" "$UNUSED"' EXIT

echo -e "${GREEN}Step 1: Finding all declarations...${NC}"

# Extract all top-level declarations.
# Use [\w'.]+ to match Lean identifiers (allows primes and dots for qualified names).
# Keyword set covers definition-shaped forms plus `axiom|constant` (dead axioms
# are exactly what a cleanup pass should surface) and `structure|class|inductive`
# (type definitions can be dead code too). An optional modifier prefix covers
# `noncomputable def`, `unsafe def`, `partial def`, `nonrec def` — real Lean
# forms whose column-0 keyword is the modifier, not the decl keyword.
# `example` is deliberately absent: examples are anonymous, no name to track.
DECL_KEYWORDS='theorem|lemma|def|abbrev|instance|axiom|constant|structure|class|inductive'
DECL_MODIFIERS='noncomputable|unsafe|partial|nonrec'
if [[ "$USE_RG" == true ]]; then
    # --no-filename is load-bearing: without it, rg prefixes every match with
    # `path:` when searching a directory (even with --no-heading), so every
    # extracted "declaration" is actually `path:name`. The Step 2 usage search
    # then looks for `path:name` in file CONTENT, finds nothing, and flags
    # every declaration in the project as unused. This was the pre-fix
    # behavior whenever ripgrep was installed (the recommended configuration).
    rg -t lean "^(($DECL_MODIFIERS)\s+)?($DECL_KEYWORDS)\s+([\w'.]+)" \
        "$SEARCH_DIR" \
        --no-heading \
        --no-filename \
        --only-matching \
        --replace '$4' | sort -u > "$DECLARATIONS"
else
    find "$SEARCH_DIR" -name "*.lean" -type f -exec \
        grep -hoP "^(($DECL_MODIFIERS)\s+)?($DECL_KEYWORDS)\s+\K[\w'.]+" {} \; | \
        sort -u > "$DECLARATIONS"
fi

TOTAL_DECLS=$(wc -l < "$DECLARATIONS" | tr -d ' ')

echo -e "${GREEN}Found ${BOLD}$TOTAL_DECLS${NC}${GREEN} declarations${NC}"
echo ""

if [[ $TOTAL_DECLS -eq 0 ]]; then
    echo -e "${YELLOW}No declarations found in $SEARCH_DIR${NC}"
    exit 0
fi

echo -e "${GREEN}Step 2: Checking for usages...${NC}"
echo "This may take a while for large projects..."
echo ""

UNUSED_COUNT=0
PROGRESS=0

while IFS= read -r decl; do
    PROGRESS=$((PROGRESS + 1))

    # Show progress every 10 declarations
    if (( PROGRESS % 10 == 0 )); then
        echo -ne "\rChecking... $PROGRESS/$TOTAL_DECLS"
    fi

    # Skip common/likely exported names
    # (constructors, instances, etc. often "unused" but needed)
    if [[ "$decl" =~ ^(mk|instPure|instBind|instMonad|instFunctor|toFun|ofFun)$ ]]; then
        continue
    fi

    # Search for uses of this declaration
    # Escape for regex and use Lean-aware boundaries (handles ' and .)
    escaped_decl=$(escape_regex "$decl")
    if [[ "$USE_RG" == true ]]; then
        # Count usages (excluding definition)
        USAGE_COUNT=$(rg -t lean "$LEAN_ID_BEFORE$escaped_decl$LEAN_ID_AFTER" "$SEARCH_DIR" --count-matches 2>/dev/null | \
            awk -F: '{sum += $2} END {print sum}' || echo "0")
    else
        USAGE_COUNT=$(find "$SEARCH_DIR" -name "*.lean" -type f -exec \
            grep -Eo "$LEAN_ID_BEFORE$escaped_decl$LEAN_ID_AFTER" {} \; | wc -l | tr -d ' ')
    fi

    # If only 1 usage (the definition itself) or 0, it's likely unused
    if [[ $USAGE_COUNT -le 1 ]]; then
        echo "$decl" >> "$UNUSED"
        UNUSED_COUNT=$((UNUSED_COUNT + 1))
    fi
done < "$DECLARATIONS"

echo -ne "\r\033[K"  # Clear progress line

echo ""
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}RESULTS${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

if [[ $UNUSED_COUNT -eq 0 ]]; then
    echo -e "${GREEN}${BOLD}✓ All declarations appear to be used!${NC}"
    echo ""
    echo "Great! Your codebase has no obviously unused declarations."
else
    echo -e "${YELLOW}Found ${BOLD}$UNUSED_COUNT${NC}${YELLOW} potentially unused declaration(s):${NC}"
    echo ""

    # Show unused declarations with file locations
    while IFS= read -r decl; do
        # Find where it's defined (escape for regex). Keyword set + modifier
        # prefix must mirror the Step 1 extraction regex, else expanded-class
        # decls (axiom, noncomputable def, ...) report without a location.
        escaped_decl=$(escape_regex "$decl")
        if [[ "$USE_RG" == true ]]; then
            LOCATION=$(rg -t lean "^(($DECL_MODIFIERS)\s+)?($DECL_KEYWORDS)\s+$escaped_decl$LEAN_ID_AFTER" \
                "$SEARCH_DIR" --no-heading | head -1 || echo "")
        else
            LOCATION=$(find "$SEARCH_DIR" -name "*.lean" -type f -exec \
                grep -En "^(($DECL_MODIFIERS)\s+)?($DECL_KEYWORDS)\s+$escaped_decl$LEAN_ID_AFTER" {} + | \
                head -1 || echo "")
        fi

        if [[ -n "$LOCATION" ]]; then
            echo -e "  ${RED}✗${NC} ${BOLD}$decl${NC}"
            echo -e "    Location: $LOCATION"
        fi
    done < "$UNUSED"

    echo ""
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${CYAN}${BOLD}RECOMMENDATIONS${NC}"
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""

    echo "For each unused declaration, consider:"
    echo ""
    echo "1. ${BOLD}Remove it${NC} - If truly not needed"
    echo "   ${YELLOW}⚠${NC} But check if it's part of public API first!"
    echo ""
    echo "2. ${BOLD}Mark as private${NC} - If it's an implementation detail"
    echo "   ${GREEN}private${NC} theorem $decl ..."
    echo ""
    echo "3. ${BOLD}Add to public API${NC} - If it should be exported"
    echo "   Document it properly and mark it as part of the interface"
    echo ""
    echo "4. ${BOLD}Use it${NC} - If you forgot to apply it somewhere"
    echo "   Check if there are places where this lemma would be useful"
    echo ""

    echo -e "${YELLOW}${BOLD}Important:${NC}"
    echo "• This analysis may have false positives (e.g., exported API, instances)"
    echo -e "• ${RED}⚠ Usages in comments and strings ARE counted${NC} (may inflate usage counts)"
    echo "  This is a known limitation - stripping comments requires Lean parsing."
    echo "• Always verify before removing declarations"
    echo "• Use ${BOLD}find_usages.sh <decl>${NC} to double-check specific declarations"
    echo ""
fi

# Summary
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}SUMMARY${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo -e "Total declarations: ${BOLD}$TOTAL_DECLS${NC}"
echo -e "Potentially unused: ${BOLD}$UNUSED_COUNT${NC}"

if [[ $UNUSED_COUNT -gt 0 ]]; then
    USAGE_RATE=$(( (TOTAL_DECLS - UNUSED_COUNT) * 100 / TOTAL_DECLS ))
    echo -e "Usage rate: ${BOLD}${USAGE_RATE}%${NC}"
fi

echo ""

# Exit code: 0 if all used, 1 if unused found
if [[ $UNUSED_COUNT -eq 0 || -n "$EXIT_ZERO_ON_FINDINGS" ]]; then
    exit 0
else
    exit 1
fi
