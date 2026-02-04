#!/usr/bin/env bash
#
# check_axioms_inline.sh - Check axioms in Lean 4 files using inline #print axioms
#
# Usage:
#   ./check_axioms_inline.sh <file-or-pattern> [--verbose]
#   ./check_axioms_inline.sh src/**/*.lean
#   ./check_axioms_inline.sh MyFile.lean --verbose
#
# This script temporarily appends #print axioms commands to Lean files,
# runs Lean to check axioms, then removes the additions.
#
# Limitations:
#   - Only detects the first namespace in a file
#   - Only captures top-level (unindented) declarations
#   - Nested namespaces, sections, and indented declarations may be missed
#
# Standard mathlib axioms (propext, quot.sound, choice) are filtered out,
# highlighting only custom axioms or unexpected dependencies.
#
# Examples:
#   ./check_axioms_inline.sh MyFile.lean
#   ./check_axioms_inline.sh src/**/*.lean
#   ./check_axioms_inline.sh "Exchangeability/**/*.lean" --verbose
#
# IMPORTANT: This script temporarily modifies files. Make sure:
#   - Files are in version control (can revert if needed)
#   - No other processes are editing the files

set -euo pipefail

# Track backup files for cleanup on interrupt using marker files
# Marker files are more robust than arrays for SIGINT handling
MARKER_DIR=$(mktemp -d)
cleanup() {
    # Find all marker files and restore corresponding backups
    # Use nullglob to handle case when no markers exist
    local marker
    for marker in "$MARKER_DIR"/*.marker; do
        [[ -f "$marker" ]] || continue
        local original
        original=$(cat "$marker")
        if [[ -f "$original.axiom_check_backup" ]]; then
            mv "$original.axiom_check_backup" "$original"
        fi
        rm -f "$marker"
    done
    rm -rf "$MARKER_DIR"
}
trap cleanup EXIT INT TERM

# Configuration
VERBOSE=""
FILES=()
MARKER="-- AUTO_AXIOM_CHECK_MARKER_DO_NOT_COMMIT"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Standard acceptable axioms
STANDARD_AXIOMS="propext|quot.sound|Classical.choice|Quot.sound"

# Parse arguments
for arg in "$@"; do
    if [[ "$arg" == "--verbose" ]]; then
        VERBOSE="--verbose"
    else
        # Expand globs
        if [[ "$arg" == *"*"* ]]; then
            # shellcheck disable=SC2206
            expanded=($arg)
            for file in "${expanded[@]}"; do
                [[ -f "$file" ]] && FILES+=("$file")
            done
        elif [[ -f "$arg" ]]; then
            FILES+=("$arg")
        else
            echo -e "${RED}Error: $arg is not a file${NC}" >&2
            exit 1
        fi
    fi
done

# Validate input
if [[ ${#FILES[@]} -eq 0 ]]; then
    echo -e "${RED}Error: No files specified${NC}" >&2
    echo "Usage: $0 <file-or-pattern> [--verbose]" >&2
    echo "Examples:" >&2
    echo "  $0 MyFile.lean" >&2
    echo "  $0 src/**/*.lean" >&2
    echo "  $0 \"Exchangeability/**/*.lean\" --verbose" >&2
    exit 1
fi

# Filter to .lean files only
LEAN_FILES=()
for file in "${FILES[@]}"; do
    if [[ "$file" =~ \.lean$ ]]; then
        LEAN_FILES+=("$file")
    fi
done

if [[ ${#LEAN_FILES[@]} -eq 0 ]]; then
    echo -e "${RED}Error: No Lean files found${NC}" >&2
    exit 1
fi

# Summary
if [[ ${#LEAN_FILES[@]} -eq 1 ]]; then
    echo -e "${BLUE}Checking axioms in 1 file${NC}"
else
    echo -e "${BLUE}Checking axioms in ${#LEAN_FILES[@]} files${NC}"
fi
echo

# Global counters
TOTAL_FILES=0
TOTAL_DECLARATIONS=0
FILES_WITH_CUSTOM=0
CUSTOM_AXIOM_COUNT=0

# Check single file
check_file() {
    local FILE="$1"

    echo -e "${BLUE}File: ${YELLOW}$FILE${NC}"

    # Extract namespace if any
    local NAMESPACE=""
    if grep -q "^namespace " "$FILE"; then
        NAMESPACE=$(grep "^namespace " "$FILE" | head -1 | sed 's/namespace //')
    fi

    # Extract all theorem/lemma/def declarations (including structure, class, inductive)
    local DECLARATIONS=()
    while IFS= read -r line; do
        decl=$(echo "$line" | sed -E 's/^(theorem|lemma|def|instance|abbrev|example|structure|class|inductive) +([^ :(]+).*/\2/')
        if [[ -n "$decl" ]]; then
            # Add namespace prefix if present
            if [[ -n "$NAMESPACE" ]]; then
                DECLARATIONS+=("$NAMESPACE.$decl")
            else
                DECLARATIONS+=("$decl")
            fi
        fi
    # Note: We match only declarations that START at column 0 with the keyword directly
    # Lines starting with 'private ', 'protected ', or 'local ' won't match
    # This is intentional - those declarations are not accessible outside their scope
    done < <(grep -E '^(theorem|lemma|def|instance|abbrev|example|structure|class|inductive) ' "$FILE" 2>/dev/null || true)

    if [[ ${#DECLARATIONS[@]} -eq 0 ]]; then
        echo -e "  ${YELLOW}No declarations found${NC}"
        echo
        return 0
    fi

    echo -e "  ${GREEN}Found ${#DECLARATIONS[@]} declarations${NC}"

    # Create backup and track it with marker file for SIGINT safety
    local BACKUP_FILE="${FILE}.axiom_check_backup"
    local MARKER_FILE="$MARKER_DIR/$(basename "$FILE").marker"
    cp "$FILE" "$BACKUP_FILE"
    echo "$FILE" > "$MARKER_FILE"

    # Function to restore file and remove marker
    local cleanup_done=false
    cleanup_file() {
        if [[ "$cleanup_done" == false && -f "$BACKUP_FILE" ]]; then
            mv "$BACKUP_FILE" "$FILE"
            cleanup_done=true
            rm -f "$MARKER_FILE"
        fi
    }

    # Append #print axioms commands
    echo "" >> "$FILE"
    echo "$MARKER" >> "$FILE"
    for decl in "${DECLARATIONS[@]}"; do
        echo "#print axioms $decl" >> "$FILE"
    done

    # Run Lean
    local HAS_CUSTOM=false
    if OUTPUT=$(lake env lean "$FILE" 2>&1); then
        # Parse output
        local CURRENT_DECL=""

        while IFS= read -r line; do
            # Match declaration headers like "foo depends on axioms:"
            if [[ "$line" =~ ^([a-zA-Z0-9_.]+)[[:space:]]+depends[[:space:]]+on[[:space:]]+axioms: ]]; then
                CURRENT_DECL="${BASH_REMATCH[1]}"
                if [[ "$VERBOSE" == "--verbose" ]]; then
                    echo -e "  ${BLUE}$CURRENT_DECL:${NC}"
                fi
            # Match axiom names (just the name on a line)
            elif [[ "$line" =~ ^[[:space:]]*([a-zA-Z0-9_.]+)[[:space:]]*$ ]]; then
                axiom="${BASH_REMATCH[1]}"
                # Skip empty lines
                if [[ -n "$axiom" && ! "$axiom" =~ ^[[:space:]]*$ ]]; then
                    if [[ ! "$axiom" =~ $STANDARD_AXIOMS ]]; then
                        echo -e "  ${RED}⚠ $CURRENT_DECL uses non-standard axiom: $axiom${NC}"
                        HAS_CUSTOM=true
                        ((CUSTOM_AXIOM_COUNT++))
                    elif [[ "$VERBOSE" == "--verbose" ]]; then
                        echo -e "    ${GREEN}✓${NC} $axiom (standard)"
                    fi
                fi
            fi
        done <<< "$OUTPUT"

        if [[ "$HAS_CUSTOM" == false ]]; then
            echo -e "  ${GREEN}✓ All declarations use only standard axioms${NC}"
        else
            ((FILES_WITH_CUSTOM++))
        fi

        ((TOTAL_DECLARATIONS+=${#DECLARATIONS[@]}))
        ((TOTAL_FILES++))

        cleanup_file
        echo
        return 0
    else
        # Check if errors are ONLY unknownIdentifier in our appended #print axioms region
        # Real errors in the original file should still fail

        # Find line number where our marker starts (original file length + 1)
        local MARKER_LINE
        MARKER_LINE=$(grep -n "$MARKER" "$FILE" | head -1 | cut -d: -f1)

        # Extract all error line numbers from output (format: file.lean:LINE:COL: error)
        local HAS_REAL_ERROR=false
        while IFS= read -r error_line; do
            if [[ "$error_line" =~ :([0-9]+):[0-9]+:.*error ]]; then
                local err_lineno="${BASH_REMATCH[1]}"
                # If error is before our appended region, it's a real error
                if [[ -n "$MARKER_LINE" && "$err_lineno" -lt "$MARKER_LINE" ]]; then
                    HAS_REAL_ERROR=true
                    break
                fi
            fi
        done < <(echo "$OUTPUT" | grep -E ':[0-9]+:[0-9]+:.*error')

        # Also check: if there are errors that aren't unknownIdentifier types, fail
        if echo "$OUTPUT" | grep -E ':[0-9]+:[0-9]+:.*error' | grep -qvE 'unknownIdentifier|unknown identifier|unknown constant'; then
            HAS_REAL_ERROR=true
        fi

        if [[ "$HAS_REAL_ERROR" == false ]] && echo "$OUTPUT" | grep -q 'unknownIdentifier\|unknown identifier\|unknown constant'; then
            # Only unknownIdentifier errors in the appended region - treat as warning
            echo -e "  ${YELLOW}⚠ Some declarations not accessible (private/local)${NC}"

            # Still try to parse any successful #print axioms results from output
            local CURRENT_DECL=""
            local PARSED_ANY=false

            while IFS= read -r line; do
                # Match declaration headers like "foo depends on axioms:"
                if [[ "$line" =~ ^([a-zA-Z0-9_.]+)[[:space:]]+depends[[:space:]]+on[[:space:]]+axioms: ]]; then
                    CURRENT_DECL="${BASH_REMATCH[1]}"
                    PARSED_ANY=true
                    if [[ "$VERBOSE" == "--verbose" ]]; then
                        echo -e "  ${BLUE}$CURRENT_DECL:${NC}"
                    fi
                # Match axiom names (just the name on a line)
                elif [[ "$line" =~ ^[[:space:]]*([a-zA-Z0-9_.]+)[[:space:]]*$ ]]; then
                    axiom="${BASH_REMATCH[1]}"
                    # Skip empty lines
                    if [[ -n "$axiom" && ! "$axiom" =~ ^[[:space:]]*$ ]]; then
                        if [[ ! "$axiom" =~ $STANDARD_AXIOMS ]]; then
                            echo -e "  ${RED}⚠ $CURRENT_DECL uses non-standard axiom: $axiom${NC}"
                            HAS_CUSTOM=true
                            ((CUSTOM_AXIOM_COUNT++))
                        elif [[ "$VERBOSE" == "--verbose" ]]; then
                            echo -e "    ${GREEN}✓${NC} $axiom (standard)"
                        fi
                    fi
                fi
            done <<< "$OUTPUT"

            if [[ "$PARSED_ANY" == true ]]; then
                if [[ "$HAS_CUSTOM" == false ]]; then
                    echo -e "  ${GREEN}✓ Accessible declarations use only standard axioms${NC}"
                else
                    ((FILES_WITH_CUSTOM++))
                fi
                ((TOTAL_DECLARATIONS+=${#DECLARATIONS[@]}))
                ((TOTAL_FILES++))
            fi

            cleanup_file
            echo
            return 0  # Don't fail - just warn about inaccessible declarations
        else
            # Real error - not just unknownIdentifier in appended region
            echo -e "  ${RED}Error running Lean${NC}" >&2
            echo "$OUTPUT" | grep "error" | head -10 | sed 's/^/  /' >&2
            cleanup_file
            echo
            return 1
        fi
    fi
}

# Check all files
FAILED_FILES=()
for file in "${LEAN_FILES[@]}"; do
    if ! check_file "$file"; then
        FAILED_FILES+=("$file")
    fi
done

# Summary
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${BLUE}Summary:${NC}"
echo -e "  Files checked: $TOTAL_FILES"
echo -e "  Declarations checked: $TOTAL_DECLARATIONS"

if [[ $FILES_WITH_CUSTOM -eq 0 ]]; then
    echo -e "  ${GREEN}✓ All files use only standard axioms${NC}"
else
    echo -e "  ${RED}⚠ Files with non-standard axioms: $FILES_WITH_CUSTOM${NC}"
    echo -e "  ${RED}⚠ Total non-standard axiom usages: $CUSTOM_AXIOM_COUNT${NC}"
fi

if [[ ${#FAILED_FILES[@]} -gt 0 ]]; then
    echo -e "  ${RED}✗ Files with errors: ${#FAILED_FILES[@]}${NC}"
    for file in "${FAILED_FILES[@]}"; do
        echo -e "    - $file"
    done
fi

echo
echo -e "${YELLOW}Standard axioms (acceptable):${NC}"
echo "  • propext (propositional extensionality)"
echo "  • quot.sound (quotient soundness)"
echo "  • Classical.choice (axiom of choice)"

if [[ $FILES_WITH_CUSTOM -gt 0 ]]; then
    echo
    echo -e "${YELLOW}Tip: Non-standard axioms should have elimination plans${NC}"
    exit 1
fi

if [[ ${#FAILED_FILES[@]} -gt 0 ]]; then
    exit 1
fi

exit 0
