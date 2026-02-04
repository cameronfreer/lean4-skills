#!/usr/bin/env bash
#
# proof_complexity.sh - Analyze proof length and complexity metrics
#
# Usage:
#   ./proof_complexity.sh <file-or-directory> [--sort-by=lines|tokens|sorries]
#
# Analyzes Lean 4 files to provide metrics on proof complexity:
#   - Lines per proof (from theorem/lemma to end)
#   - Estimated token count
#   - Number of tactics used
#   - Presence of sorries
#
# Examples:
#   ./proof_complexity.sh MyFile.lean
#   ./proof_complexity.sh src/ --sort-by=lines
#   ./proof_complexity.sh . --sort-by=sorries

set -euo pipefail

# Configuration
TARGET="${1:-.}"
SORT_BY="${2:-lines}"

# Parse sort option
if [[ "$SORT_BY" == --sort-by=* ]]; then
    SORT_BY="${SORT_BY#--sort-by=}"
fi

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m'

# Validate target
if [[ ! -e "$TARGET" ]]; then
    echo -e "${RED}Error: $TARGET does not exist${NC}" >&2
    exit 1
fi

# Find all .lean files
if [[ -f "$TARGET" ]]; then
    FILES=("$TARGET")
elif [[ -d "$TARGET" ]]; then
    mapfile -t FILES < <(find "$TARGET" -name "*.lean" -type f)
else
    echo -e "${RED}Error: $TARGET is neither a file nor a directory${NC}" >&2
    exit 1
fi

if [[ ${#FILES[@]} -eq 0 ]]; then
    echo -e "${RED}Error: No Lean files found${NC}" >&2
    exit 1
fi

echo -e "${BLUE}Analyzing proof complexity in ${#FILES[@]} file(s)${NC}"
echo

# Temporary file for results
RESULTS=$(mktemp)
trap 'rm -f "$RESULTS"' EXIT

# Analyze each file
for file in "${FILES[@]}"; do
    # Extract theorem/lemma blocks with line numbers
    awk '
    /^(theorem|lemma) / {
        in_proof = 1
        name = $2
        start_line = NR
        proof_lines = ""
        next
    }
    in_proof {
        proof_lines = proof_lines "\n" $0
        if (/^(theorem|lemma|def|class|structure|inductive|instance|axiom) / && NR > start_line) {
            # New declaration - end previous proof
            in_proof = 0
        }
    }
    in_proof && NF == 0 && prev_empty {
        # Two consecutive empty lines often indicate end of proof
        if (proof_lines != "") {
            lines = NR - start_line
            tokens = split(proof_lines, arr, /[[:space:]]+/)
            tactics = gsub(/(^|[[:space:]])(apply|exact|intro|cases|induction|simp|rw|have|by|calc|refine|constructor|use)([[:space:]]|$)/, "&", proof_lines)
            sorries = gsub(/sorry/, "&", proof_lines)
            printf "%s:%d:%s:%d:%d:%d:%d\n", FILENAME, start_line, name, lines, tokens, tactics, sorries
        }
        in_proof = 0
    }
    { prev_empty = (NF == 0) }
    END {
        # Handle proof at end of file
        if (in_proof && proof_lines != "") {
            lines = NR - start_line
            tokens = split(proof_lines, arr, /[[:space:]]+/)
            tactics = gsub(/(^|[[:space:]])(apply|exact|intro|cases|induction|simp|rw|have|by|calc|refine|constructor|use)([[:space:]]|$)/, "&", proof_lines)
            sorries = gsub(/sorry/, "&", proof_lines)
            printf "%s:%d:%s:%d:%d:%d:%d\n", FILENAME, start_line, name, lines, tokens, tactics, sorries
        }
    }
    ' "$file" >> "$RESULTS"
done

if [[ ! -s "$RESULTS" ]]; then
    echo -e "${YELLOW}No theorems or lemmas found${NC}"
    exit 0
fi

# Count totals
TOTAL_PROOFS=$(wc -l < "$RESULTS")
TOTAL_WITH_SORRY=$(grep -c ":.*:[1-9][0-9]*$" "$RESULTS" || true)

# Sort results
case "$SORT_BY" in
    lines)
        SORTED=$(sort -t: -k4 -rn "$RESULTS")
        ;;
    tokens)
        SORTED=$(sort -t: -k5 -rn "$RESULTS")
        ;;
    sorries)
        SORTED=$(sort -t: -k7 -rn "$RESULTS")
        ;;
    *)
        echo -e "${RED}Error: Invalid sort option: $SORT_BY${NC}" >&2
        echo "Valid options: lines, tokens, sorries" >&2
        exit 1
        ;;
esac

# Display top 20 most complex
echo -e "${CYAN}Top 20 most complex proofs (sorted by $SORT_BY):${NC}"
echo
printf "${BLUE}%-50s %6s %8s %8s %8s${NC}\n" "Proof" "Lines" "Tokens" "Tactics" "Sorries"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

echo "$SORTED" | head -20 | while IFS=: read -r file line name lines tokens tactics sorries; do
    # Truncate name if too long
    if [[ ${#name} -gt 40 ]]; then
        display_name="${name:0:37}..."
    else
        display_name="$name"
    fi

    # Color sorries red
    if [[ $sorries -gt 0 ]]; then
        sorry_color="${RED}"
    else
        sorry_color="${GREEN}"
    fi

    printf "%-50s ${YELLOW}%6d${NC} %8d %8d ${sorry_color}%8d${NC}\n" \
        "${display_name} ($file:$line)" "$lines" "$tokens" "$tactics" "$sorries"
done

# Summary statistics
echo
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${BLUE}Summary Statistics:${NC}"

AVG_LINES=$(awk -F: '{sum+=$4} END {printf "%.1f", sum/NR}' "$RESULTS")
AVG_TOKENS=$(awk -F: '{sum+=$5} END {printf "%.1f", sum/NR}' "$RESULTS")
AVG_TACTICS=$(awk -F: '{sum+=$6} END {printf "%.1f", sum/NR}' "$RESULTS")

echo "  Total proofs: $TOTAL_PROOFS"
echo "  Proofs with sorry: $TOTAL_WITH_SORRY"
echo "  Average lines per proof: $AVG_LINES"
echo "  Average tokens per proof: $AVG_TOKENS"
echo "  Average tactics per proof: $AVG_TACTICS"

# Complexity distribution
SMALL=$(awk -F: '$4 <= 10' "$RESULTS" | wc -l)
MEDIUM=$(awk -F: '$4 > 10 && $4 <= 50' "$RESULTS" | wc -l)
LARGE=$(awk -F: '$4 > 50 && $4 <= 100' "$RESULTS" | wc -l)
HUGE=$(awk -F: '$4 > 100' "$RESULTS" | wc -l)

echo
echo -e "${CYAN}Proof size distribution:${NC}"
echo "  Small (≤10 lines):    $SMALL"
echo "  Medium (11-50 lines): $MEDIUM"
echo "  Large (51-100 lines): $LARGE"
echo "  Huge (>100 lines):    $HUGE"

if [[ $TOTAL_WITH_SORRY -gt 0 ]]; then
    echo
    echo -e "${YELLOW}Note: $TOTAL_WITH_SORRY proof(s) contain sorry - metrics may be incomplete${NC}"
fi
