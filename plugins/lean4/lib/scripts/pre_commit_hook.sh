#!/usr/bin/env bash
#
# pre_commit_hook.sh - Comprehensive pre-commit checks for Lean 4 projects
#
# Usage:
#   ./pre_commit_hook.sh [--quick] [--strict]
#
# Runs a series of quality checks before committing:
#   - Build verification
#   - Axiom usage check
#   - Sorry count
#   - Import cleanup suggestions
#   - Simp lemma hygiene
#
# Options:
#   --quick   Skip slow checks (build, import minimization)
#   --strict  Fail on any warnings (not just errors)
#
# Examples:
#   ./pre_commit_hook.sh
#   ./pre_commit_hook.sh --quick
#   ./pre_commit_hook.sh --strict
#
# Git Hook Installation:
#   ln -s ../../scripts/pre_commit_hook.sh .git/hooks/pre-commit

set -euo pipefail

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

# Configuration
QUICK_MODE=false
STRICT_MODE=false
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Parse arguments
for arg in "$@"; do
    case "$arg" in
        --quick)
            QUICK_MODE=true
            ;;
        --strict)
            STRICT_MODE=true
            ;;
    esac
done

# Track failures
ERRORS=0
WARNINGS=0

echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}PRE-COMMIT QUALITY CHECKS${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

if [[ "$QUICK_MODE" == true ]]; then
    echo -e "${YELLOW}Running in QUICK mode (skipping slow checks)${NC}"
    echo ""
fi

if [[ "$STRICT_MODE" == true ]]; then
    echo -e "${YELLOW}Running in STRICT mode (warnings = errors)${NC}"
    echo ""
fi

# Check 1: Build Verification
if [[ "$QUICK_MODE" == false ]]; then
    echo -e "${BOLD}[1/5] Building project...${NC}"
    if lake build 2>&1 | tee /tmp/build.log; then
        echo -e "${GREEN}✓ Build successful${NC}"
    else
        echo -e "${RED}✗ Build failed${NC}"
        echo ""
        echo "Fix compilation errors before committing."
        tail -20 /tmp/build.log
        ERRORS=$((ERRORS + 1))
    fi
    echo ""
else
    echo -e "${YELLOW}[1/5] Skipping build (quick mode)${NC}"
    echo ""
fi

# Check 2: Axiom Usage
echo -e "${BOLD}[2/5] Checking axiom usage...${NC}"

# Get list of changed .lean files
CHANGED_FILES=$(git diff --cached --name-only --diff-filter=ACM | grep "\.lean$" || true)

if [[ -n "$CHANGED_FILES" ]]; then
    if [[ -x "$SCRIPT_DIR/check_axioms_inline.sh" ]]; then
        AXIOM_RESULT=0
        for file in $CHANGED_FILES; do
            "$SCRIPT_DIR/check_axioms_inline.sh" "$file" &> /tmp/axiom_check.log || AXIOM_RESULT=$?
        done

        if [[ $AXIOM_RESULT -eq 0 ]]; then
            echo -e "${GREEN}✓ All axioms are standard${NC}"
        else
            echo -e "${RED}✗ Non-standard axioms detected${NC}"
            cat /tmp/axiom_check.log | grep "⚠"
            ERRORS=$((ERRORS + 1))
        fi
    else
        echo -e "${YELLOW}⚠ Axiom checker not found, skipping${NC}"
        WARNINGS=$((WARNINGS + 1))
    fi
else
    echo -e "${GREEN}✓ No .lean files changed${NC}"
fi
echo ""

# Check 3: Sorry Count
echo -e "${BOLD}[3/5] Counting sorries...${NC}"

if [[ -n "$CHANGED_FILES" ]] && [[ -x "$SCRIPT_DIR/sorry_analyzer.py" ]]; then
    SORRY_COUNT=0
    for file in $CHANGED_FILES; do
        FILE_SORRIES=$("$SCRIPT_DIR/sorry_analyzer.py" "$file" 2>/dev/null | grep -c "sorry" || echo "0")
        SORRY_COUNT=$((SORRY_COUNT + FILE_SORRIES))
    done

    if [[ $SORRY_COUNT -eq 0 ]]; then
        echo -e "${GREEN}✓ No sorries in changed files${NC}"
    elif [[ $SORRY_COUNT -le 3 ]]; then
        echo -e "${YELLOW}⚠ $SORRY_COUNT sorry/sorries found${NC}"
        echo "  Make sure they're documented with TODO comments"
        WARNINGS=$((WARNINGS + 1))
    else
        echo -e "${YELLOW}⚠ $SORRY_COUNT sorries found${NC}"
        echo "  Consider breaking work into smaller commits"
        WARNINGS=$((WARNINGS + 1))
    fi
else
    echo -e "${GREEN}✓ No .lean files changed${NC}"
fi
echo ""

# Check 4: Import Cleanup
if [[ "$QUICK_MODE" == false ]]; then
    echo -e "${BOLD}[4/5] Checking for unused imports...${NC}"

    if [[ -n "$CHANGED_FILES" ]] && [[ -x "$SCRIPT_DIR/minimize_imports.py" ]]; then
        IMPORTS_NEED_CLEANUP=false

        for file in $CHANGED_FILES; do
            if "$SCRIPT_DIR/minimize_imports.py" "$file" --dry-run 2>&1 | grep -q "Unused imports:"; then
                IMPORTS_NEED_CLEANUP=true
                echo -e "${YELLOW}⚠ $file has unused imports${NC}"
            fi
        done

        if [[ "$IMPORTS_NEED_CLEANUP" == true ]]; then
            echo ""
            echo "Run: minimize_imports.py <file> to clean up"
            WARNINGS=$((WARNINGS + 1))
        else
            echo -e "${GREEN}✓ No unused imports detected${NC}"
        fi
    else
        echo -e "${GREEN}✓ No .lean files changed${NC}"
    fi
    echo ""
else
    echo -e "${YELLOW}[4/5] Skipping import check (quick mode)${NC}"
    echo ""
fi

# Check 5: Simp Lemma Hygiene
echo -e "${BOLD}[5/5] Checking simp lemmas...${NC}"

if [[ -n "$CHANGED_FILES" ]] && [[ -x "$SCRIPT_DIR/simp_lemma_tester.sh" ]]; then
    SIMP_ISSUES=false

    for file in $CHANGED_FILES; do
        if grep -q "@\[simp\]" "$file"; then
            if ! "$SCRIPT_DIR/simp_lemma_tester.sh" "$file" &> /tmp/simp_check.log; then
                SIMP_ISSUES=true
                echo -e "${YELLOW}⚠ Potential simp issues in $file${NC}"
            fi
        fi
    done

    if [[ "$SIMP_ISSUES" == true ]]; then
        cat /tmp/simp_check.log | grep "⚠"
        WARNINGS=$((WARNINGS + 1))
    else
        echo -e "${GREEN}✓ Simp lemmas look good${NC}"
    fi
else
    echo -e "${GREEN}✓ No simp lemmas in changed files${NC}"
fi
echo ""

# Summary
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}SUMMARY${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

if [[ $ERRORS -eq 0 ]]; then
    echo -e "${GREEN}${BOLD}✓ All checks passed!${NC}"
else
    echo -e "${RED}${BOLD}✗ $ERRORS error(s) found${NC}"
fi

if [[ $WARNINGS -gt 0 ]]; then
    echo -e "${YELLOW}${BOLD}⚠ $WARNINGS warning(s) found${NC}"
fi

echo ""

# Exit status
if [[ $ERRORS -gt 0 ]]; then
    echo -e "${RED}Commit blocked due to errors${NC}"
    echo "Fix the issues above and try again"
    exit 1
fi

if [[ "$STRICT_MODE" == true ]] && [[ $WARNINGS -gt 0 ]]; then
    echo -e "${YELLOW}Commit blocked due to warnings (strict mode)${NC}"
    echo "Fix the warnings or run without --strict"
    exit 1
fi

if [[ $WARNINGS -gt 0 ]]; then
    echo -e "${YELLOW}Warnings detected but not blocking commit${NC}"
    echo "Consider fixing them before committing"
fi

echo -e "${GREEN}Proceeding with commit...${NC}"
echo ""

exit 0
