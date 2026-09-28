#!/usr/bin/env bash
#
# unused_declarations.sh - Find unused declarations in a Lean 4 project
#
# Usage:
#   ./unused_declarations.sh [directory] [--exit-zero-on-findings]
#
# Finds top-level declarations that are never used in the project.
# Covered keywords: theorem, lemma, def, abbrev, instance, axiom,
# constant, structure, class, inductive — optionally prefixed by an
# access modifier (private, protected, local) and/or noncomputable,
# unsafe, partial, nonrec (#184). A `private` declaration is file-local in
# Lean, so its usages are counted within its own file only — a same-named
# private declaration in another file cannot mask it.
#
# The analysis runs over a code-only mirror of the tree (#185,
# lib/scripts/lean_code_view.py): comments — line, nested block, docstrings
# — and string literals are blanked, with line numbers preserved, so a
# mention in a docstring, a commented-out proof or a `#guard_msgs` string
# never counts as a usage, and a commented-out declaration is never
# extracted. Requires python3 (loud exit 2 otherwise).
#
# Examples:
#   ./unused_declarations.sh
#   ./unused_declarations.sh src/
#
# Output:
#   - List of unused declarations
#   - Suggestions for marking as private or removing
#   - Summary statistics
#
# Known limitations (grep-based analysis, no Lean elaboration):
#   - Namespace-qualified usage is NOT credited: a decl `foo` inside
#     `namespace A` referenced elsewhere as `A.foo` is still flagged
#     unused, because extraction records the short name and the usage
#     boundary deliberately excludes `.`-prefixed forms. Verify with
#     find_usages.sh before removing anything namespaced.
#   - Indented, @[attr]-prefixed and mutual-block decls are not extracted;
#     trees containing ONLY those are reported as unverifiable (exit 1)
#     rather than clean.
#   - Advisory only: "potentially unused" is a grep-level verdict, never a
#     certification of dead code and never an automatic deletion.

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
    # The fallback extraction uses grep -P (PCRE, for \K). BSD grep (macOS)
    # doesn't support -P: without this hard check, the extraction pipeline
    # would fail, the `|| true` guard would mask it, and a tree full of
    # ordinary declarations would report "No declarations found" with
    # exit 0 — a false green. A tool that can't run must say so loudly.
    if ! echo x | grep -oP 'x' >/dev/null 2>&1; then
        echo -e "${RED}Error: this script requires ripgrep (rg) or a PCRE-capable grep (grep -P).${NC}" >&2
        echo -e "${RED}Neither is available — cannot analyze. Install ripgrep: https://github.com/BurntSushi/ripgrep${NC}" >&2
        exit 2
    fi
    echo -e "${YELLOW}Note: ripgrep not found. Install ripgrep for 10-100x faster analysis${NC}"
    echo ""
fi

# The code-only mirror (#185). Same policy as the rg/PCRE check above: a
# missing tool or a failed mirror must be loud (exit 2), never a false
# "no findings".
if ! command -v python3 >/dev/null 2>&1; then
    echo -e "${RED}Error: this script requires python3 (to build the comment/string-free code view).${NC}" >&2
    exit 2
fi
CODE_VIEW="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lean_code_view.py"
if [[ ! -f "$CODE_VIEW" ]]; then
    echo -e "${RED}Error: lean_code_view.py not found beside this script — cannot analyze.${NC}" >&2
    exit 2
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
PRIVATE_MAP=$(mktemp)
MIRROR=$(mktemp -d)
trap 'rm -rf "$DECLARATIONS" "$UNUSED" "$PRIVATE_MAP" "$MIRROR"' EXIT

echo -e "${GREEN}Step 0: Building the code-only view (comments and strings blanked)...${NC}"
if ! _mirrored=$(python3 "$CODE_VIEW" "$SEARCH_DIR" "$MIRROR"); then
    echo -e "${RED}Error: could not build the code-only view of $SEARCH_DIR — cannot analyze.${NC}" >&2
    exit 2
fi
echo -e "Mirrored ${BOLD}${_mirrored}${NC} Lean file(s)"
echo ""
# Locations found in the mirror are reported against the original tree.
_loc_fix() { sed "s|^$MIRROR/|$SEARCH_DIR/|"; }

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
# Access modifiers come BEFORE decl modifiers, as in Lean's declModifiers
# grammar (`private noncomputable def`; the reverse is not valid Lean).
DECL_ACCESS='private|protected|local'
# rg capture numbering with the access group in front: $6 is the name.
DECL_RE="^(($DECL_ACCESS)\s+)?(($DECL_MODIFIERS)\s+)?($DECL_KEYWORDS)\s+"
if [[ "$USE_RG" == true ]]; then
    # --no-filename is load-bearing: without it, rg prefixes every match with
    # `path:` when searching a directory (even with --no-heading), so every
    # extracted "declaration" is actually `path:name`. The Step 2 usage search
    # then looks for `path:name` in file CONTENT, finds nothing, and flags
    # every declaration in the project as unused. This was the pre-fix
    # behavior whenever ripgrep was installed (the recommended configuration).
    # `|| true` is load-bearing: rg exits 1 when it finds no matches, and
    # under `set -euo pipefail` that killed the whole script mid-run on any
    # declaration-free tree — exit 1 with no summary, making the
    # TOTAL_DECLS==0 branch below unreachable in rg mode.
    rg -t lean "${DECL_RE}([\w'.]+)" \
        "$MIRROR" \
        --no-heading \
        --no-filename \
        --only-matching \
        --replace '$6' | sort -u > "$DECLARATIONS" || true
    # private declarations, with their file: usages are counted per file
    rg -t lean "^private\s+(($DECL_MODIFIERS)\s+)?($DECL_KEYWORDS)\s+([\w'.]+)" \
        "$MIRROR" \
        --no-heading \
        --with-filename \
        --only-matching \
        --replace '$4' | sed 's|^\(.*\):\([^:]*\)$|\1\t\2|' | sort -u > "$PRIVATE_MAP" || true
else
    find "$MIRROR" -name "*.lean" -type f -exec \
        grep -hoP "${DECL_RE}\K[\w'.]+" {} \; | \
        sort -u > "$DECLARATIONS" || true
    while IFS= read -r _pf; do
        grep -oP "^private\s+(($DECL_MODIFIERS)\s+)?($DECL_KEYWORDS)\s+\K[\w'.]+" "$_pf" 2>/dev/null | \
            sed "s|^|$_pf\t|" || true
    done < <(find "$MIRROR" -name "*.lean" -type f) | sort -u > "$PRIVATE_MAP"
fi

TOTAL_DECLS=$(wc -l < "$DECLARATIONS" | tr -d ' ')

echo -e "${GREEN}Found ${BOLD}$TOTAL_DECLS${NC}${GREEN} declarations${NC}"
echo ""

if [[ $TOTAL_DECLS -eq 0 ]]; then
    # Distinguish two cases (same policy as check_axioms_inline.sh, #145):
    #   (a) legitimately declaration-free tree (imports only, comments only,
    #       or no .lean files at all) — safe to report and exit 0
    #   (b) tree HAS declaration-shaped content the extraction regex missed
    #       (indented decls, private/protected/local prefixes, @[attr]
    #       lines, mutual blocks) — the analysis can't see those, so a
    #       "no declarations" report would be false reassurance; exit 1.
    # grep -r --include (supported by both GNU and BSD grep) avoids the
    # find|xargs pitfalls: BSD xargs skips empty input (making the pipeline
    # exit 0 → false positive on decl-free dirs) while GNU xargs would run
    # grep against stdin; and head-terminated pipes risk SIGPIPE flakiness
    # under pipefail.
    #
    # Shape regex: any line that is optional-indent + optional access
    # modifier + optional decl modifier + a decl keyword — at ANY indent
    # depth, including column 0. Since this branch only runs when the
    # extraction found NOTHING, a column-0 match here means the extraction
    # itself failed (regex bug, tool misbehavior) and must be loud, not a
    # friendly zero. Also catches @[attr] lines and mutual blocks.
    _shape_re="^[[:space:]]*((private|protected|local)[[:space:]]+)?(($DECL_MODIFIERS)[[:space:]]+)?($DECL_KEYWORDS)[[:space:]]|^[[:space:]]*@\[|^[[:space:]]*mutual[[:space:]]*$"
    if grep -rqE --include='*.lean' "$_shape_re" "$MIRROR" 2>/dev/null; then
        echo -e "${YELLOW}⚠ No top-level declarations matched, but declaration-shaped content exists (indented / @[attr] / mutual) — analysis cannot cover it${NC}"
        exit 1
    fi
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

    # Search for uses of this declaration in the code-only mirror.
    # Escape for regex and use Lean-aware boundaries (handles ' and .)
    escaped_decl=$(escape_regex "$decl")
    _usage_re="$LEAN_ID_BEFORE$escaped_decl$LEAN_ID_AFTER"

    # Files where this name is a PRIVATE declaration: file-local counting.
    _priv_files=$(awk -F'\t' -v n="$decl" '$2 == n {print $1}' "$PRIVATE_MAP")
    _priv_n=0
    if [[ -n "$_priv_files" ]]; then
        while IFS= read -r _pf; do
            [[ -n "$_pf" ]] || continue
            _priv_n=$((_priv_n + 1))
            _c=$(grep -Eo "$_usage_re" "$_pf" 2>/dev/null | wc -l | tr -d ' ')
            if [[ "${_c:-0}" -le 1 ]]; then
                printf '%s\t%s\n' "$decl" "$_pf" >> "$UNUSED"
                UNUSED_COUNT=$((UNUSED_COUNT + 1))
            fi
        done <<< "$_priv_files"
    fi

    # Definition sites that are NOT private: project-wide counting (as before).
    if [[ "$USE_RG" == true ]]; then
        _sites=$(rg -t lean "${DECL_RE}${escaped_decl}${LEAN_ID_AFTER}" "$MIRROR" --count-matches 2>/dev/null | \
            awk -F: '{sum += $2} END {print sum+0}' || echo "0")
    else
        _sites=$(find "$MIRROR" -name "*.lean" -type f -exec \
            grep -Eo "${DECL_RE}${escaped_decl}${LEAN_ID_AFTER}" {} \; | wc -l | tr -d ' ')
    fi
    if [[ "${_sites:-0}" -gt "$_priv_n" ]]; then
        if [[ "$USE_RG" == true ]]; then
            USAGE_COUNT=$(rg -t lean "$_usage_re" "$MIRROR" --count-matches 2>/dev/null | \
                awk -F: '{sum += $2} END {print sum+0}' || echo "0")
        else
            USAGE_COUNT=$(find "$MIRROR" -name "*.lean" -type f -exec \
                grep -Eo "$_usage_re" {} \; | wc -l | tr -d ' ')
        fi
        # Only the definition sites themselves (public + private) → unused.
        if [[ "${USAGE_COUNT:-0}" -le "$_sites" ]]; then
            printf '%s\t\n' "$decl" >> "$UNUSED"
            UNUSED_COUNT=$((UNUSED_COUNT + 1))
        fi
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

    # Show unused declarations with file locations (a private finding
    # carries its file; a public one is located project-wide). The
    # location regex must mirror the Step 1 extraction regex.
    while IFS=$'\t' read -r decl _pfile; do
        escaped_decl=$(escape_regex "$decl")
        _loc_re="${DECL_RE}${escaped_decl}${LEAN_ID_AFTER}"
        if [[ -n "$_pfile" ]]; then
            LOCATION=$(grep -En "$_loc_re" "$_pfile" 2>/dev/null | head -1 | sed "s|^|$_pfile:|" | _loc_fix || echo "")
        elif [[ "$USE_RG" == true ]]; then
            LOCATION=$(rg -t lean -n "$_loc_re" "$MIRROR" --no-heading | head -1 | _loc_fix || echo "")
        else
            LOCATION=$(find "$MIRROR" -name "*.lean" -type f -exec \
                grep -EHn "$_loc_re" {} + | head -1 | _loc_fix || echo "")
        fi

        if [[ -n "$LOCATION" ]]; then
            if [[ -n "$_pfile" ]]; then
                echo -e "  ${RED}✗${NC} ${BOLD}$decl${NC} (private)"
            else
                echo -e "  ${RED}✗${NC} ${BOLD}$decl${NC}"
            fi
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
    echo "• Usages in comments and strings are NOT counted (code-only view); namespace-qualified"
    echo "  usages (A.foo) are not credited either — a grep-level verdict, not a certification"
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
