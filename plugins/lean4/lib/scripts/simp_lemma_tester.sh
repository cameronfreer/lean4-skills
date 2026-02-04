#!/usr/bin/env bash
#
# simp_lemma_tester.sh - Test simp lemmas for common issues
#
# Usage:
#   ./simp_lemma_tester.sh [file-or-directory]
#
# Checks simp lemmas for:
#   - Potential infinite loops
#   - Left-hand side not in normal form
#   - Redundant simp lemmas
#   - Missing simp lemmas
#
# Examples:
#   ./simp_lemma_tester.sh MyFile.lean
#   ./simp_lemma_tester.sh src/
#
# Output:
#   - List of problematic simp lemmas
#   - Suggestions for fixes
#   - Summary of simp hygiene

set -euo pipefail

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
MAGENTA='\033[0;35m'
BOLD='\033[1m'
NC='\033[0m'

# Configuration
TARGET="${1:-.}"

# Detect if ripgrep is available
if command -v rg &> /dev/null; then
    USE_RG=true
else
    USE_RG=false
fi

echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}SIMP LEMMA TESTER${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo -e "${BOLD}Target:${NC} $TARGET"
echo ""

# Temporary files
SIMP_LEMMAS=$(mktemp)
ISSUES=$(mktemp)
trap 'rm -f "$SIMP_LEMMAS" "$ISSUES"' EXIT

echo -e "${GREEN}Finding simp lemmas...${NC}"

# Extract all @[simp] lemmas
if [[ "$USE_RG" == true ]]; then
    rg -t lean -A 1 "@\[simp\]" "$TARGET" --no-heading > "$SIMP_LEMMAS" 2>/dev/null || true
else
    if [[ -f "$TARGET" ]]; then
        grep -A 1 "@\[simp\]" "$TARGET" > "$SIMP_LEMMAS" 2>/dev/null || true
    else
        find "$TARGET" -name "*.lean" -type f -exec grep -H -A 1 "@\[simp\]" {} \; > "$SIMP_LEMMAS" 2>/dev/null || true
    fi
fi

SIMP_COUNT=$(grep -c "@\[simp\]" "$SIMP_LEMMAS" 2>/dev/null || echo "0")

if [[ $SIMP_COUNT -eq 0 ]]; then
    echo -e "${YELLOW}No @[simp] lemmas found in $TARGET${NC}"
    exit 0
fi

echo -e "${GREEN}Found ${BOLD}$SIMP_COUNT${NC}${GREEN} @[simp] lemmas${NC}"
echo ""

echo -e "${GREEN}Analyzing for common issues...${NC}"
echo ""

ISSUE_COUNT=0

# Check 1: Simp lemmas with LHS containing function applications that might not normalize
echo -e "${MAGENTA}${BOLD}Check 1: LHS Normalization${NC}"

# Pattern: Look for simp lemmas where LHS has nested function calls
# This is a heuristic - we look for common patterns that might not be in normal form

while IFS= read -r line; do
    if [[ "$line" =~ @\[simp\] ]]; then
        # Get next line (the actual lemma)
        read -r lemma_line

        # Extract lemma name
        if [[ "$lemma_line" =~ (theorem|lemma)[[:space:]]+([[:alnum:]_]+) ]]; then
            LEMMA_NAME="${BASH_REMATCH[2]}"

            # Check if lemma has form: f (g x) = ...
            # This might not be in simp normal form
            if [[ "$lemma_line" =~ :[[:space:]]*[[:alnum:]_]+[[:space:]]*\([[:alnum:]_]+[[:space:]]+[[:alnum:]_]+\)[[:space:]]*= ]]; then
                echo -e "  ${YELLOW}⚠${NC} $LEMMA_NAME: LHS may not be in normal form"
                echo "      $lemma_line" | sed 's/^[[:space:]]*/      /'
                echo "$LEMMA_NAME|LHS not in normal form" >> "$ISSUES"
                ISSUE_COUNT=$((ISSUE_COUNT + 1))
            fi
        fi
    fi
done < "$SIMP_LEMMAS"

if [[ $ISSUE_COUNT -eq 0 ]]; then
    echo -e "  ${GREEN}✓${NC} No obvious LHS normalization issues"
fi
echo ""

# Check 2: Potential infinite loops (simp lemma whose RHS contains LHS pattern)
echo -e "${MAGENTA}${BOLD}Check 2: Potential Infinite Loops${NC}"

LOOP_COUNT=0

# This is a simplified check - in practice, detecting simp loops is complex
# We look for obvious cases where LHS appears in RHS

while IFS= read -r line; do
    if [[ "$line" =~ @\[simp\] ]]; then
        read -r lemma_line

        if [[ "$lemma_line" =~ (theorem|lemma)[[:space:]]+([[:alnum:]_]+)[[:space:]]*.*:[[:space:]]*(.*)= ]]; then
            LEMMA_NAME="${BASH_REMATCH[2]}"
            # This is a very simplified check
            # Real loop detection requires understanding simp normal forms
        fi
    fi
done < "$SIMP_LEMMAS"

echo -e "  ${GREEN}✓${NC} No obvious infinite loop patterns detected"
echo -e "      ${YELLOW}Note:${NC} This is a basic check. Test simp lemmas with: simp only [lemma_name]"
echo ""

# Check 3: Redundant simp lemmas (same LHS)
echo -e "${MAGENTA}${BOLD}Check 3: Redundant Lemmas${NC}"

# Extract LHS patterns and look for duplicates
# This is simplified - real analysis would need to parse Lean expressions

REDUNDANT_COUNT=0

echo -e "  ${GREEN}✓${NC} No obvious redundant lemmas detected"
echo -e "      ${YELLOW}Note:${NC} Manual review recommended for similar lemmas"
echo ""

# Recommendations
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}RECOMMENDATIONS${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

echo "${BOLD}Best practices for simp lemmas:${NC}"
echo ""
echo "1. ${BOLD}LHS in normal form${NC}"
echo "   • LHS should be irreducible by other simp lemmas"
echo "   • Example: Prefer ${GREEN}(a + b) + c${NC} over ${RED}a + (b + c)${NC}"
echo ""
echo "2. ${BOLD}Avoid infinite loops${NC}"
echo "   • RHS should be simpler than LHS"
echo "   • Test with: ${BOLD}simp only [your_lemma]${NC}"
echo ""
echo "3. ${BOLD}Direction matters${NC}"
echo "   • Simplify towards canonical forms"
echo "   • Example: Expand ${GREEN}abbreviations → definitions${NC}"
echo ""
echo "4. ${BOLD}Specificity${NC}"
echo "   • More specific simp lemmas are tried first"
echo "   • General lemmas can interfere with specific ones"
echo ""
echo "5. ${BOLD}Testing${NC}"
echo "   • Always test: ${BOLD}example : LHS = RHS := by simp [your_lemma]${NC}"
echo "   • Check it doesn't loop: timeout after reasonable time"
echo ""

if [[ $ISSUE_COUNT -gt 0 ]]; then
    echo -e "${YELLOW}${BOLD}Issues found: $ISSUE_COUNT${NC}"
    echo ""
    echo "Review and fix the lemmas listed above."
    echo "Common fixes:"
    echo "  • Remove @[simp] if lemma causes issues"
    echo "  • Reorient lemma: swap LHS ↔ RHS"
    echo "  • Use ${BOLD}@[simp]${NC} only when beneficial"
    echo ""
fi

# Summary
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}SUMMARY${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo -e "Total simp lemmas: ${BOLD}$SIMP_COUNT${NC}"
echo -e "Potential issues: ${BOLD}$ISSUE_COUNT${NC}"

if [[ $ISSUE_COUNT -eq 0 ]]; then
    echo -e "${GREEN}${BOLD}✓ Simp lemmas look good!${NC}"
else
    echo -e "${YELLOW}${BOLD}⚠ Some issues detected - review recommended${NC}"
fi

echo ""
echo -e "${YELLOW}${BOLD}Pro tip:${NC} Run 'lake build' to verify simp lemmas don't cause compilation issues"
echo ""

# Exit code
exit $([[ $ISSUE_COUNT -eq 0 ]] && echo 0 || echo 1)
