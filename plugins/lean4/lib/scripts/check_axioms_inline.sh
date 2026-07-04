#!/usr/bin/env bash
#
# check_axioms_inline.sh - Check axioms in Lean 4 files using inline #print axioms
#
# Usage:
#   ./check_axioms_inline.sh <file-or-dir-or-pattern> [--verbose] [--exit-zero-on-findings]
#   ./check_axioms_inline.sh src/**/*.lean
#   ./check_axioms_inline.sh MyFile.lean --verbose --report-only
#   ./check_axioms_inline.sh .
#   ./check_axioms_inline.sh src/
#
# This script temporarily appends #print axioms commands to Lean files,
# runs Lean to check axioms, then removes the additions.
#
# Limitations:
#   - Only captures top-level (unindented) declarations
#   - Identifier regex is ASCII-only ([A-Za-z0-9_.]+): unicode-letter
#     namespaces (`namespace α`) fall through to the not-accessible branch
#     and are surfaced as unverified rather than passing silently.
#   - Sections with `variable` declarations may still hit the not-accessible
#     branch. When they do, they are surfaced via the UNVERIFIED_FILES
#     summary and cause the run to exit non-zero rather than pass silently.
#
# Standard mathlib axioms (propext, quot.sound, choice) are filtered out,
# highlighting only custom axioms or unexpected dependencies.
#
# Examples:
#   ./check_axioms_inline.sh MyFile.lean
#   ./check_axioms_inline.sh src/**/*.lean
#   ./check_axioms_inline.sh "Exchangeability/**/*.lean" --verbose
#   ./check_axioms_inline.sh .                          # scan entire project
#   ./check_axioms_inline.sh src/ --report-only         # scan directory
#
# IMPORTANT: This script temporarily modifies files. Make sure:
#   - Files are in version control (can revert if needed)
#   - No other processes are editing the files

set -euo pipefail

# Track backup files for cleanup on interrupt using marker files
# Marker files are more robust than arrays for SIGINT handling
MARKER_DIR=$(mktemp -d)
# shellcheck disable=SC2329,SC2317  # invoked via trap below; SC2317 fires per-line in the body for the same reason
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
EXIT_ZERO_ON_FINDINGS=""
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

# Global counter for unique marker filenames (avoids basename collisions)
MARKER_COUNT=0

# Parse arguments: collect flags first, then positional args
# This ensures --report-only works regardless of position
POSITIONAL=()
for arg in "$@"; do
    case "$arg" in
        --verbose)
            VERBOSE="--verbose"
            ;;
        --exit-zero-on-findings|--report-only)
            EXIT_ZERO_ON_FINDINGS="true"
            ;;
        --*)
            echo -e "${RED}Error: Unknown flag: $arg${NC}" >&2
            exit 1
            ;;
        *)
            POSITIONAL+=("$arg")
            ;;
    esac
done

# Resolve positional args to files
for arg in "${POSITIONAL[@]}"; do
    if [[ "$arg" == *"*"* ]]; then
        # Expand globs
        # shellcheck disable=SC2206
        expanded=($arg)
        for file in "${expanded[@]}"; do
            [[ -f "$file" ]] && FILES+=("$file")
        done
    elif [[ -d "$arg" ]]; then
        dir_files_found=false
        while IFS= read -r -d '' file; do
            FILES+=("$file")
            dir_files_found=true
        done < <(find "$arg" -type d \( -name .lake -o -name .git \) -prune -o -type f -name '*.lean' -print0)
        if [[ "$dir_files_found" == false ]]; then
            if [[ -n "$EXIT_ZERO_ON_FINDINGS" ]]; then
                echo -e "${YELLOW}Warning: no .lean files found under: $arg; skipping.${NC}" >&2
            else
                echo -e "${RED}Error: no .lean files found under: $arg${NC}" >&2
                exit 1
            fi
        fi
    elif [[ -f "$arg" ]]; then
        FILES+=("$arg")
    else
        echo -e "${RED}Error: $arg is not a file or directory${NC}" >&2
        exit 1
    fi
done

# Normalize paths and dedup for deterministic ordering (handles overlapping args like ". src/A.lean")
if [[ ${#FILES[@]} -gt 0 ]]; then
    DEDUPED=()
    while IFS= read -r f; do
        DEDUPED+=("$f")
    done < <(
        for f in "${FILES[@]}"; do
            realpath "$f" 2>/dev/null \
                || (cd "$(dirname "$f")" && echo "$(pwd -P)/$(basename "$f")") \
                || echo "$f"
        done | sort -u
    )
    FILES=("${DEDUPED[@]}")
fi

# Validate input
if [[ ${#FILES[@]} -eq 0 ]]; then
    if [[ ${#POSITIONAL[@]} -eq 0 ]]; then
        # No arguments at all — always an error
        echo -e "${RED}Error: No files specified${NC}" >&2
        echo "Usage: $0 <file-or-dir-or-pattern> [--verbose] [--exit-zero-on-findings]" >&2
        echo "Examples:" >&2
        echo "  $0 MyFile.lean" >&2
        echo "  $0 src/**/*.lean" >&2
        echo "  $0 ." >&2
        echo "  $0 src/ --report-only" >&2
        echo "  $0 \"Exchangeability/**/*.lean\" --verbose" >&2
        exit 1
    elif [[ -n "$EXIT_ZERO_ON_FINDINGS" ]]; then
        # Args given but resolved to zero files in report-only mode — soft exit
        echo -e "${YELLOW}Warning: no Lean files found; nothing to check.${NC}" >&2
        exit 0
    else
        echo -e "${RED}Error: No Lean files found in specified paths${NC}" >&2
        exit 1
    fi
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

    # Walk the file linearly with a kind-tagged frame stack tracking namespace
    # and section scopes. Each frame is "ns:Name" or "sec:Name" (Name may be
    # empty for anonymous sections). Only ns: frames contribute to declaration
    # qualification. Bare `end` pops the top frame; `end X` pops iff top has
    # name X. Mismatched `end X` leaves the stack alone — Lean would fail to
    # compile such a file and the real-error branch below will surface that.
    #
    # Note: We match declarations that START at column 0 with the keyword
    # directly. Lines starting with 'private ', 'protected ', or 'local '
    # won't match; those are intentionally not accessible outside their scope
    # and, if all decls in a file are inaccessible, the file is surfaced via
    # the UNVERIFIED_FILES summary rather than passing silently.
    local FRAME_STACK=()
    local DECLARATIONS=()
    local line

    # Regex patterns kept in variables — required to work around shellcheck's
    # parser choking on character classes containing `:(` inline in [[ =~ ]].
    local ns_re='^namespace[[:space:]]+([A-Za-z0-9_.]+)'
    local sec_re='^section([[:space:]]+([A-Za-z0-9_.]+))?[[:space:]]*$'
    local end_re='^end([[:space:]]+([A-Za-z0-9_.]+))?[[:space:]]*$'
    local decl_re='^(theorem|lemma|def|instance|abbrev|example|structure|class|inductive)[[:space:]]+([^[:space:]:(]+)'

    while IFS= read -r line; do
        if [[ "$line" =~ $ns_re ]]; then
            FRAME_STACK+=("ns:${BASH_REMATCH[1]}")
        elif [[ "$line" =~ $sec_re ]]; then
            FRAME_STACK+=("sec:${BASH_REMATCH[2]:-}")
        elif [[ "$line" =~ $end_re ]]; then
            local end_name="${BASH_REMATCH[2]:-}"
            if [[ ${#FRAME_STACK[@]} -gt 0 ]]; then
                local top_idx=$((${#FRAME_STACK[@]} - 1))
                local top="${FRAME_STACK[$top_idx]}"
                local top_name="${top#*:}"
                if [[ -z "$end_name" || "$end_name" == "$top_name" ]]; then
                    unset "FRAME_STACK[$top_idx]"
                    # Re-pack safely: bare "${arr[@]}" on empty errors under set -u.
                    if [[ ${#FRAME_STACK[@]} -gt 0 ]]; then
                        FRAME_STACK=("${FRAME_STACK[@]}")
                    else
                        FRAME_STACK=()
                    fi
                fi
            fi
        elif [[ "$line" =~ $decl_re ]]; then
            local short="${BASH_REMATCH[2]}"
            if [[ -n "$short" ]]; then
                local prefix=""
                if [[ ${#FRAME_STACK[@]} -gt 0 ]]; then
                    local frame
                    for frame in "${FRAME_STACK[@]}"; do
                        if [[ "$frame" == ns:* ]]; then
                            prefix+="${frame#ns:}."
                        fi
                    done
                fi
                DECLARATIONS+=("${prefix}${short}")
            fi
        fi
    done < "$FILE"

    if [[ ${#DECLARATIONS[@]} -eq 0 ]]; then
        echo -e "  ${YELLOW}No declarations found${NC}"
        echo
        return 0
    fi

    echo -e "  ${GREEN}Found ${#DECLARATIONS[@]} declarations${NC}"

    # Create backup and track it with marker file for SIGINT safety
    local BACKUP_FILE="${FILE}.axiom_check_backup"
    ((++MARKER_COUNT))
    local MARKER_FILE="$MARKER_DIR/${MARKER_COUNT}.marker"
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
                        ((++CUSTOM_AXIOM_COUNT))
                    elif [[ "$VERBOSE" == "--verbose" ]]; then
                        echo -e "    ${GREEN}✓${NC} $axiom (standard)"
                    fi
                fi
            fi
        done <<< "$OUTPUT"

        if [[ "$HAS_CUSTOM" == false ]]; then
            echo -e "  ${GREEN}✓ All declarations use only standard axioms${NC}"
        else
            ((++FILES_WITH_CUSTOM))
        fi

        ((TOTAL_DECLARATIONS+=${#DECLARATIONS[@]}))
        ((++TOTAL_FILES))

        cleanup_file
        echo
        return 0
    else
        # Check if errors are ONLY unknownIdentifier in our appended #print axioms region
        # Real errors in the original file should still fail

        # Find line number where our marker starts (original file length + 1)
        local MARKER_LINE
        MARKER_LINE=$(grep -nF -- "$MARKER" "$FILE" | head -1 | cut -d: -f1)

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
                            ((++CUSTOM_AXIOM_COUNT))
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
                    ((++FILES_WITH_CUSTOM))
                fi
                ((TOTAL_DECLARATIONS+=${#DECLARATIONS[@]}))
                ((++TOTAL_FILES))
            else
                # Zero declarations resolved — a gate that can't answer must
                # not silently pass. Track for the summary; the run's exit
                # code will surface this (see summary block below).
                UNVERIFIED_FILES+=("$FILE")
            fi

            cleanup_file
            echo
            return 0  # Warned inline; UNVERIFIED_FILES surfaces the gap in the summary.
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
UNVERIFIED_FILES=()
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

# Surface unverified files first (informational; feeds the verdict block below).
# Length-guard the array read — bare "${arr[@]}" on empty errors under set -u.
if [[ ${#UNVERIFIED_FILES[@]} -gt 0 ]]; then
    echo -e "  ${YELLOW}⚠ Unverified files (declarations did not resolve): ${#UNVERIFIED_FILES[@]}${NC}"
    for file in "${UNVERIFIED_FILES[@]}"; do
        echo -e "    - $file"
    done
fi

# Verdict — the green branch requires FULL coverage AND no custom axioms.
# Priority: withhold > red > green. UNVERIFIED_FILES nonempty MUST suppress
# the green verdict even when the files that were verified are clean —
# otherwise a mixed clean+unverified directory run silently drops the
# unverified files while showing green (#132's directory-mode manifestation).
if [[ ${#UNVERIFIED_FILES[@]} -gt 0 || $TOTAL_DECLARATIONS -eq 0 ]]; then
    if [[ $TOTAL_DECLARATIONS -eq 0 ]]; then
        echo -e "  ${YELLOW}⚠ Zero declarations were verified — verdict withheld${NC}"
    else
        echo -e "  ${YELLOW}⚠ Verified files use only standard axioms, but verdict withheld because some files were unverified${NC}"
    fi
elif [[ $FILES_WITH_CUSTOM -eq 0 ]]; then
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
    if [[ -z "$EXIT_ZERO_ON_FINDINGS" ]]; then exit 1; fi
fi

if [[ ${#FAILED_FILES[@]} -gt 0 ]]; then
    exit 1
fi

# UNVERIFIED_FILES nonempty and TOTAL_DECLARATIONS==0 are coverage failures
# — the gate could not make a determination for one or more files. This
# overrides --exit-zero-on-findings: `--report-only` means "treat findings
# as non-fatal", not "silently drop what you couldn't check."
if [[ ${#UNVERIFIED_FILES[@]} -gt 0 || $TOTAL_DECLARATIONS -eq 0 ]]; then
    exit 1
fi

exit 0
