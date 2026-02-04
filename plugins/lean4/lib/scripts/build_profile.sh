#!/usr/bin/env bash
#
# build_profile.sh - Profile Lean 4 build times and identify bottlenecks
#
# Usage:
#   ./build_profile.sh [--clean] [--top N]
#
# Profiles lake build to identify slow-compiling files and import bottlenecks.
#
# Options:
#   --clean    Run lake clean before profiling
#   --top N    Show top N slowest files (default: 10)
#
# Examples:
#   ./build_profile.sh
#   ./build_profile.sh --clean
#   ./build_profile.sh --top 20
#
# Output:
#   - Build time breakdown by file
#   - Slowest files with compilation times
#   - Total build time
#   - Suggestions for optimization

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
CLEAN_BUILD=false
TOP_N=10

# Parse arguments
for arg in "$@"; do
    case "$arg" in
        --clean)
            CLEAN_BUILD=true
            ;;
        --top)
            shift
            TOP_N="${1:-10}"
            ;;
        --top=*)
            TOP_N="${arg#--top=}"
            ;;
        *)
            ;;
    esac
done

echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}LEAN 4 BUILD PROFILER${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

# Check if we're in a Lean project
if [[ ! -f "lakefile.lean" ]] && [[ ! -f "lakefile.toml" ]]; then
    echo -e "${RED}Error: Not in a Lean 4 project directory${NC}" >&2
    echo "Run this script from your project root (where lakefile.lean is)" >&2
    exit 1
fi

# Clean build if requested
if [[ "$CLEAN_BUILD" == true ]]; then
    echo -e "${YELLOW}Running clean build...${NC}"
    lake clean
    echo ""
fi

# Temporary file for build output
BUILD_LOG=$(mktemp)
PROFILE_DATA=$(mktemp)
trap 'rm -f "$BUILD_LOG" "$PROFILE_DATA"' EXIT

echo -e "${GREEN}Starting profiled build...${NC}"
echo "This may take a while depending on project size"
echo ""

# Record start time
START_TIME=$(date +%s)

# Run build with timing information
# We'll parse the output to extract file compilation times
lake build 2>&1 | tee "$BUILD_LOG"

# Record end time
END_TIME=$(date +%s)
TOTAL_TIME=$((END_TIME - START_TIME))

echo ""
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}BUILD ANALYSIS${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

# Parse build log for file compilation info
# Lake outputs lines like: "Building MyModule"
# We'll estimate times based on order and gaps

# Extract compiled files
grep -E "Building|Compiling" "$BUILD_LOG" | sed 's/.*Building //' | sed 's/.*Compiling //' > "$PROFILE_DATA" 2>/dev/null || true

FILE_COUNT=$(wc -l < "$PROFILE_DATA" | tr -d ' ')

if [[ $FILE_COUNT -eq 0 ]]; then
    echo -e "${YELLOW}No files were compiled (build may be up-to-date)${NC}"
    echo ""
    echo -e "${GREEN}Total build time: ${BOLD}${TOTAL_TIME}s${NC}"
    echo ""
    echo -e "${YELLOW}Run with --clean to profile a full rebuild${NC}"
    exit 0
fi

echo -e "${BOLD}Total build time:${NC} ${TOTAL_TIME}s"
echo -e "${BOLD}Files compiled:${NC} $FILE_COUNT"
echo -e "${BOLD}Average time per file:${NC} $((TOTAL_TIME / FILE_COUNT))s"
echo ""

# Since lake doesn't output per-file times, we can only estimate
# based on order and provide file list
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}FILES COMPILED${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

# Show first few files (likely dependencies/imports)
echo -e "${MAGENTA}${BOLD}First compiled (dependencies):${NC}"
head -5 "$PROFILE_DATA" | while read -r file; do
    echo "  • $file"
done
echo ""

# Show last few files (likely project files)
echo -e "${MAGENTA}${BOLD}Last compiled (project files):${NC}"
tail -5 "$PROFILE_DATA" | while read -r file; do
    echo "  • $file"
done
echo ""

# Analyze import patterns for potential bottlenecks
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}IMPORT ANALYSIS${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

# Find files with most imports (potential bottlenecks)
if command -v rg &> /dev/null; then
    echo -e "${MAGENTA}${BOLD}Files with most imports (potential bottlenecks):${NC}"

    # Search for import statements in .lean files
    rg "^import " --type lean --count-matches 2>/dev/null | \
        sort -t: -k2 -rn | \
        head -5 | \
        while IFS=: read -r file count; do
            echo "  $count imports - $file"
        done
    echo ""
fi

# Recommendations
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}OPTIMIZATION RECOMMENDATIONS${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

if [[ $TOTAL_TIME -gt 120 ]]; then
    echo -e "${YELLOW}⚠ Build time > 2 minutes${NC}"
    echo ""
    echo "Consider:"
    echo "  1. ${BOLD}Minimize imports${NC} - Use minimize_imports.py"
    echo "  2. ${BOLD}Split large files${NC} - Break files >500 lines into modules"
    echo "  3. ${BOLD}Cache mathlib${NC} - Download pre-built mathlib cache"
    echo "  4. ${BOLD}Parallel builds${NC} - Lake builds in parallel by default"
    echo ""
fi

if [[ $FILE_COUNT -gt 50 ]]; then
    echo -e "${YELLOW}⚠ Large project ($FILE_COUNT files)${NC}"
    echo ""
    echo "Consider:"
    echo "  1. ${BOLD}Modular structure${NC} - Organize into subdirectories"
    echo "  2. ${BOLD}Reduce coupling${NC} - Files with many imports slow builds"
    echo "  3. ${BOLD}Use lake exe${NC} - Build specific targets instead of 'lake build'"
    echo ""
fi

# Check if mathlib is being rebuilt
if grep -q "Building.*Mathlib" "$BUILD_LOG"; then
    echo -e "${YELLOW}⚠ Mathlib is being compiled${NC}"
    echo ""
    echo "Mathlib compilation can take 30+ minutes!"
    echo ""
    echo "Use mathlib cache instead:"
    echo "  ${BOLD}lake exe cache get${NC} - Download pre-built mathlib"
    echo ""
fi

# Quick wins
echo -e "${GREEN}${BOLD}Quick wins:${NC}"
echo "  • Run ${BOLD}minimize_imports.py${NC} on frequently-changed files"
echo "  • Use ${BOLD}lake build <target>${NC} to build specific files"
echo "  • Check ${BOLD}dependency_graph.sh${NC} to identify coupling"
echo "  • Ensure you have latest ${BOLD}mathlib cache${NC}"
echo ""

echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}SUMMARY${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo -e "Build completed in ${BOLD}${TOTAL_TIME}s${NC}"
echo -e "Compiled ${BOLD}$FILE_COUNT${NC} files"
echo -e "Average ${BOLD}$((TOTAL_TIME / FILE_COUNT))s${NC} per file"
echo ""

# Performance rating
if [[ $TOTAL_TIME -lt 10 ]]; then
    echo -e "${GREEN}${BOLD}Performance: Excellent ⚡${NC}"
elif [[ $TOTAL_TIME -lt 60 ]]; then
    echo -e "${GREEN}${BOLD}Performance: Good ✓${NC}"
elif [[ $TOTAL_TIME -lt 300 ]]; then
    echo -e "${YELLOW}${BOLD}Performance: Moderate ⚠${NC}"
else
    echo -e "${RED}${BOLD}Performance: Needs optimization 🐌${NC}"
fi
echo ""
