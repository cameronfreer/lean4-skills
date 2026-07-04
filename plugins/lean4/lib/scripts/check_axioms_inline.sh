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
# Anchored + dot-escaped. Without ^…$ + `\.`, the classifier would treat any
# axiom whose name *contains* a standard axiom as substring as standard —
# e.g. a custom axiom `my.propext.bad` or `ClassicalxChoice` would slip
# through. Reviewer-caught. `.` in ERE is any char, so `quot.sound` used to
# match e.g. `quotXsound` too.
STANDARD_AXIOMS='^(propext|quot\.sound|Quot\.sound|Classical\.choice)$'

# Parse a `#print axioms` OUTPUT block, handling both Lean 4 output formats:
#   modern (Lean 4.x current):   'X' depends on axioms: [a, b, c]
#   legacy (older Lean 4):       X depends on axioms:
#                                  a
#                                  b
# Inputs:
#   $1 = captured OUTPUT string
#   $2 = expected decl names (newline-separated). If non-empty, header
#        lines whose name is NOT in this set are ignored — neither counted
#        toward coverage nor classified for axioms. Defense against a
#        misbehaving Lean/shim emitting unrelated headers (reviewer-caught
#        "wrong-name" attack). Pass empty string to accept all names.
# Outputs (via globals — bash 3.2 has no return-by-reference):
#   _AXPARSER_HAS_CUSTOM   = true iff any non-standard axiom was seen (in
#                            an expected-name header only)
#   _AXPARSER_PARSED_ANY   = true iff any expected header line was matched
#   _AXPARSER_PARSED_COUNT = number of DISTINCT expected decl names seen in
#                            headers (deduplicated — caller compares against
#                            ${#DECLARATIONS[@]} to detect partial coverage)
# Side effects:
#   Increments global CUSTOM_AXIOM_COUNT for each non-standard axiom found
#   Emits per-axiom colored lines to stdout inline
# Uses caller-scoped VERBOSE and STANDARD_AXIOMS. Regex patterns kept in
# vars — inline `[^]]` inside [[ =~ ]] confuses shellcheck's parser.
parse_axioms_output() {
    local OUTPUT="$1"
    local EXPECTED_NAMES="${2:-}"
    _AXPARSER_HAS_CUSTOM=false
    _AXPARSER_PARSED_ANY=false
    _AXPARSER_PARSED_COUNT=0
    local CURRENT_DECL=""
    # State: are we currently inside a LEGACY multi-line axioms block?
    # Only set to true when a plain (unquoted) `X depends on axioms:` header
    # arrived WITHOUT a bracketed tail. Reset on any modern header or blank
    # line. Gates the bare-identifier axiom-name matcher so unrelated Lean
    # output like `#eval` results can't false-positive as axioms.
    local IN_LEGACY_AXIOMS=false
    # Deduplication track for expected names already counted, so a shim
    # emitting two headers for the same decl doesn't inflate PARSED_COUNT
    # above extracted_count (which would fail the caller's equality check).
    local SEEN_NAMES=""

    # Header lines. Lean identifiers can contain apostrophes (foo', foo'',
    # etc. — common style for "primed" variants). The character class
    # [a-zA-Z0-9_.] would exclude those, silently misclassifying every such
    # decl as unrecognized and (post-parser-update) as "no axioms". So we
    # split by shape: QUOTED forms (modern Lean 4) capture broadly inside
    # the single quotes; UNQUOTED forms (legacy multi-line) match a
    # whitespace-delimited token. `.+` is greedy, so `'foo'' depends on
    # axioms: [x]` correctly captures `foo'` — backtracking finds the last
    # single-quote before ` depends`.
    local quoted_dep_re="^'(.+)'[[:space:]]+depends[[:space:]]+on[[:space:]]+axioms:(.*)$"
    local plain_dep_re="^([^[:space:]'][^[:space:]]*)[[:space:]]+depends[[:space:]]+on[[:space:]]+axioms:(.*)$"
    # "does not depend on any axioms" — modern Lean's output for decls
    # whose only deps are built-in (e.g. `trivial` proofs of `True`).
    # Must be counted as verified even though there's nothing to classify;
    # otherwise mixed accessible+inaccessible runs misreport clean decls
    # as unverified.
    local quoted_noaxioms_re="^'(.+)'[[:space:]]+does[[:space:]]+not[[:space:]]+depend[[:space:]]+on[[:space:]]+any[[:space:]]+axioms[[:space:]]*$"
    local plain_noaxioms_re="^([^[:space:]'][^[:space:]]*)[[:space:]]+does[[:space:]]+not[[:space:]]+depend[[:space:]]+on[[:space:]]+any[[:space:]]+axioms[[:space:]]*$"
    # Bracketed axiom list capture — for the modern one-line format.
    local bracket_re='\[([^]]*)\]'
    # Bare axiom name on its own line — for the legacy multi-line format.
    local ident_re='^[[:space:]]*([a-zA-Z0-9_.]+)[[:space:]]*$'

    local line rest axiom_list axiom_name matched_dep matched_no header_shape
    while IFS= read -r line; do
        matched_dep=0
        matched_no=0
        header_shape=""
        # Quoted form first — `[^']` would exclude apostrophes, so we must
        # check the quoted variant before the plain one (plain_dep_re's
        # first-char guard excludes `'`, but the order still reads better).
        if [[ "$line" =~ $quoted_dep_re ]]; then
            CURRENT_DECL="${BASH_REMATCH[1]}"
            rest="${BASH_REMATCH[2]}"
            matched_dep=1
            header_shape="quoted"
        elif [[ "$line" =~ $plain_dep_re ]]; then
            CURRENT_DECL="${BASH_REMATCH[1]}"
            rest="${BASH_REMATCH[2]}"
            matched_dep=1
            header_shape="plain"
        elif [[ "$line" =~ $quoted_noaxioms_re ]]; then
            CURRENT_DECL="${BASH_REMATCH[1]}"
            matched_no=1
        elif [[ "$line" =~ $plain_noaxioms_re ]]; then
            CURRENT_DECL="${BASH_REMATCH[1]}"
            matched_no=1
        fi

        # Any new header line ends a legacy-multi-line block. Blank lines
        # also end it (below).
        if [[ $matched_dep -eq 1 || $matched_no -eq 1 ]]; then
            IN_LEGACY_AXIOMS=false
        elif [[ -z "$line" ]]; then
            IN_LEGACY_AXIOMS=false
            continue
        fi

        # Expected-name filter: if a filter is set and CURRENT_DECL isn't in
        # it, ignore this header entirely (don't count, don't classify).
        # Reviewer-caught defense against a Lean/shim misbehavior injecting
        # a header for a name we never asked about.
        if [[ ($matched_dep -eq 1 || $matched_no -eq 1) && -n "$EXPECTED_NAMES" ]]; then
            if ! grep -qFx -- "$CURRENT_DECL" <<< "$EXPECTED_NAMES"; then
                # Unexpected name — reset CURRENT_DECL so any legacy bare
                # lines that follow don't get attributed to this alien header
                # under the expected-name whitelist.
                CURRENT_DECL=""
                matched_dep=0
                matched_no=0
                continue
            fi
        fi

        if [[ $matched_dep -eq 1 ]]; then
            # Dedupe: only count each expected name once toward PARSED_COUNT.
            if ! grep -qFx -- "$CURRENT_DECL" <<< "$SEEN_NAMES"; then
                SEEN_NAMES="${SEEN_NAMES}${CURRENT_DECL}"$'\n'
                _AXPARSER_PARSED_ANY=true
                ((++_AXPARSER_PARSED_COUNT))
            fi
            if [[ "$VERBOSE" == "--verbose" ]]; then
                echo -e "  ${BLUE}$CURRENT_DECL:${NC}"
            fi
            # Modern format: axioms on the same line inside brackets.
            if [[ "$rest" =~ $bracket_re ]]; then
                axiom_list="${BASH_REMATCH[1]}"
                local _saved_ifs="$IFS"
                local -a _axiom_arr=()
                IFS=',' read -r -a _axiom_arr <<< "$axiom_list"
                IFS="$_saved_ifs"
                if [[ ${#_axiom_arr[@]} -gt 0 ]]; then
                    for axiom_name in "${_axiom_arr[@]}"; do
                        axiom_name="${axiom_name#"${axiom_name%%[![:space:]]*}"}"
                        axiom_name="${axiom_name%"${axiom_name##*[![:space:]]}"}"
                        if [[ -n "$axiom_name" ]]; then
                            _classify_axiom "$CURRENT_DECL" "$axiom_name"
                        fi
                    done
                fi
            elif [[ "$header_shape" == "plain" ]]; then
                # Legacy multi-line format — bare identifier lines that follow
                # are axiom names. Enter the gated state.
                IN_LEGACY_AXIOMS=true
            fi
        elif [[ $matched_no -eq 1 ]]; then
            if ! grep -qFx -- "$CURRENT_DECL" <<< "$SEEN_NAMES"; then
                SEEN_NAMES="${SEEN_NAMES}${CURRENT_DECL}"$'\n'
                _AXPARSER_PARSED_ANY=true
                ((++_AXPARSER_PARSED_COUNT))
            fi
            if [[ "$VERBOSE" == "--verbose" ]]; then
                echo -e "  ${BLUE}$CURRENT_DECL:${NC} ${GREEN}✓${NC} (no axioms)"
            fi
        elif [[ "$IN_LEGACY_AXIOMS" == true && "$line" =~ $ident_re ]]; then
            # Legacy format: one axiom per subsequent line — but ONLY when
            # we're currently inside a legacy `X depends on axioms:` block.
            # Gate prevents unrelated Lean output (e.g. `#eval` results,
            # elaboration diagnostics) from being misclassified as axioms.
            axiom_name="${BASH_REMATCH[1]}"
            if [[ -n "$axiom_name" && "$axiom_name" != "depends" ]]; then
                _classify_axiom "$CURRENT_DECL" "$axiom_name"
            fi
        elif [[ "$IN_LEGACY_AXIOMS" == true ]]; then
            # Any non-identifier line inside a legacy block ends it.
            IN_LEGACY_AXIOMS=false
        fi
    done <<< "$OUTPUT"
}

# Classify one axiom name as standard or custom, emitting the RED warn line
# and incrementing counters as appropriate. Uses caller-scoped VERBOSE.
_classify_axiom() {
    local current_decl="$1"
    local axiom="$2"
    if [[ ! "$axiom" =~ $STANDARD_AXIOMS ]]; then
        echo -e "  ${RED}⚠ $current_decl uses non-standard axiom: $axiom${NC}"
        _AXPARSER_HAS_CUSTOM=true
        ((++CUSTOM_AXIOM_COUNT))
    elif [[ "$VERBOSE" == "--verbose" ]]; then
        echo -e "    ${GREEN}✓${NC} $axiom (standard)"
    fi
}

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
    # Declaration keywords include:
    #   theorem|lemma|def|instance|abbrev|example|structure|class|inductive
    #     — the definition-shaped forms
    #   axiom|constant
    #     — for an AXIOM CHECKER, missing `axiom foo : ...` at top level was
    #       a real silent-green path in mixed-directory runs
    # Optional modifier prefix covers `noncomputable def`, `unsafe def`,
    # `partial def`, `nonrec def` — real Lean forms whose column-0 keyword
    # is the modifier, not `def`.
    # Group 1 = modifier (optional), Group 2 = keyword, Group 3 = short name.
    local decl_re='^(noncomputable[[:space:]]+|unsafe[[:space:]]+|partial[[:space:]]+|nonrec[[:space:]]+)?(theorem|lemma|def|instance|abbrev|example|structure|class|inductive|axiom|constant)[[:space:]]+([^[:space:]:(]+)'

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
            # BASH_REMATCH indices with the new decl_re:
            #   [1] optional modifier ("noncomputable ", "unsafe ", etc.)
            #   [2] the declaration keyword
            #   [3] the short (unqualified) name
            local short="${BASH_REMATCH[3]}"
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
        # Build newline-delimited expected-name list from DECLARATIONS so
        # the parser can filter out headers for unexpected names.
        local _expected_names
        _expected_names=$(printf '%s\n' "${DECLARATIONS[@]}")
        parse_axioms_output "$OUTPUT" "$_expected_names"
        HAS_CUSTOM="$_AXPARSER_HAS_CUSTOM"

        # Coverage invariant: for a file to count as verified we need EVERY
        # appended `#print axioms X` to have produced a recognizable header
        # line in OUTPUT. If the parser missed any (unrecognized format,
        # future Lean format change, silent skip), treat the file as
        # unverified rather than trusting a "no custom axioms" verdict on
        # partial coverage. Custom-axiom findings from the parsed portion
        # still surface (a real finding is never suppressed by coverage
        # incompleteness).
        if [[ "$HAS_CUSTOM" == true ]]; then
            ((++FILES_WITH_CUSTOM))
        fi

        if [[ "$_AXPARSER_PARSED_COUNT" -eq ${#DECLARATIONS[@]} ]]; then
            if [[ "$HAS_CUSTOM" == false ]]; then
                echo -e "  ${GREEN}✓ All declarations use only standard axioms${NC}"
            fi
            ((++TOTAL_FILES))
        else
            echo -e "  ${YELLOW}⚠ Only $_AXPARSER_PARSED_COUNT of ${#DECLARATIONS[@]} declarations were parseable — file marked unverified${NC}"
            UNVERIFIED_FILES+=("$FILE")
        fi

        # Only count declarations we actually parsed — silently-lost decls
        # inflate the "Declarations checked" counter without any coverage.
        ((TOTAL_DECLARATIONS+=_AXPARSER_PARSED_COUNT))

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

            # Parse whatever DID resolve, then apply the coverage invariant.
            # Build newline-delimited expected-name list from DECLARATIONS so
        # the parser can filter out headers for unexpected names.
        local _expected_names
        _expected_names=$(printf '%s\n' "${DECLARATIONS[@]}")
        parse_axioms_output "$OUTPUT" "$_expected_names"
            HAS_CUSTOM="$_AXPARSER_HAS_CUSTOM"

            # Custom findings from the resolved portion still surface — a real
            # finding is never suppressed by coverage incompleteness.
            if [[ "$HAS_CUSTOM" == true ]]; then
                ((++FILES_WITH_CUSTOM))
            fi

            # Coverage invariant: any decl that didn't resolve marks the file
            # as unverified. This catches the same-file partial case: one
            # accessible + one inaccessible previously counted the file as
            # verified based on PARSED_ANY=true, silently dropping the
            # inaccessible decl. Reviewer-caught.
            if [[ "$_AXPARSER_PARSED_COUNT" -eq ${#DECLARATIONS[@]} ]]; then
                if [[ "$HAS_CUSTOM" == false ]]; then
                    echo -e "  ${GREEN}✓ Accessible declarations use only standard axioms${NC}"
                fi
                ((++TOTAL_FILES))
            else
                UNVERIFIED_FILES+=("$FILE")
                if [[ "$_AXPARSER_PARSED_COUNT" -gt 0 ]]; then
                    echo -e "  ${YELLOW}⚠ Only $_AXPARSER_PARSED_COUNT of ${#DECLARATIONS[@]} declarations resolved — file marked unverified${NC}"
                fi
            fi

            ((TOTAL_DECLARATIONS+=_AXPARSER_PARSED_COUNT))

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
# Priority order below is deliberately shaped by what the user needs to see:
#   1. If any file used a custom axiom, ALWAYS surface that (red) — a real
#      finding is never suppressed by unverified files.
#   2. Additionally, if any file is unverified, ALSO surface the coverage
#      gap (yellow) so the user knows the run isn't a full pass either way.
#   3. Otherwise, zero-decls-verified is the load-bearing #132 withhold case.
#   4. Some verified but some unverified → verified-clean-but-withheld.
#   5. Full clean coverage → green.
if [[ $FILES_WITH_CUSTOM -gt 0 ]]; then
    echo -e "  ${RED}⚠ Files with non-standard axioms: $FILES_WITH_CUSTOM${NC}"
    echo -e "  ${RED}⚠ Total non-standard axiom usages: $CUSTOM_AXIOM_COUNT${NC}"
    if [[ ${#UNVERIFIED_FILES[@]} -gt 0 ]]; then
        echo -e "  ${YELLOW}⚠ Verdict also withheld because some files were unverified${NC}"
    fi
elif [[ ${#UNVERIFIED_FILES[@]} -gt 0 || $TOTAL_DECLARATIONS -eq 0 ]]; then
    if [[ $TOTAL_DECLARATIONS -eq 0 ]]; then
        echo -e "  ${YELLOW}⚠ Zero declarations were verified — verdict withheld${NC}"
    else
        echo -e "  ${YELLOW}⚠ Verified files use only standard axioms, but verdict withheld because some files were unverified${NC}"
    fi
else
    echo -e "  ${GREEN}✓ All files use only standard axioms${NC}"
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
