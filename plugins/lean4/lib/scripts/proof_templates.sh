#!/usr/bin/env bash
#
# proof_templates.sh - Generate structured proof skeletons for Lean 4
#
# Usage:
#   ./proof_templates.sh --theorem "<theorem-statement>"
#   ./proof_templates.sh --induction "<goal>"
#   ./proof_templates.sh --cases "<goal>"
#
# Generates proof templates with structured `sorry` placeholders.
#
# Templates:
#   --theorem    General theorem template
#   --induction  Induction proof skeleton
#   --cases      Case analysis skeleton
#   --calc       Calculation chain template
#   --exists     Existential proof template
#
# Examples:
#   ./proof_templates.sh --theorem "my_theorem (n : ℕ) : n + 0 = n"
#   ./proof_templates.sh --induction "∀ n : ℕ, P n"
#   ./proof_templates.sh --cases "a ∨ b → c"
#
# Output:
#   Structured proof skeleton with sorry placeholders and TODO comments

set -euo pipefail

# Colors
CYAN='\033[0;36m'
YELLOW='\033[1;33m'
BOLD='\033[1m'
NC='\033[0m'

# Parse arguments
TEMPLATE_TYPE=""
STATEMENT=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --theorem)
            TEMPLATE_TYPE="theorem"
            shift
            STATEMENT="$1"
            shift
            ;;
        --induction)
            TEMPLATE_TYPE="induction"
            shift
            STATEMENT="$1"
            shift
            ;;
        --cases)
            TEMPLATE_TYPE="cases"
            shift
            STATEMENT="$1"
            shift
            ;;
        --calc)
            TEMPLATE_TYPE="calc"
            shift
            STATEMENT="$1"
            shift
            ;;
        --exists)
            TEMPLATE_TYPE="exists"
            shift
            STATEMENT="$1"
            shift
            ;;
        *)
            echo "Unknown option: $1" >&2
            exit 1
            ;;
    esac
done

if [[ -z "$TEMPLATE_TYPE" ]] || [[ -z "$STATEMENT" ]]; then
    cat <<'EOF'
Usage: ./proof_templates.sh [OPTIONS] "<statement>"

Options:
  --theorem     General theorem template
  --induction   Induction proof skeleton
  --cases       Case analysis skeleton
  --calc        Calculation chain template
  --exists      Existential proof template

Examples:
  ./proof_templates.sh --theorem "my_theorem (n : ℕ) : n + 0 = n"
  ./proof_templates.sh --induction "∀ n : ℕ, P n"
  ./proof_templates.sh --cases "a ∨ b → c"
EOF
    exit 1
fi

echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${CYAN}${BOLD}PROOF TEMPLATE GENERATOR${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo -e "${BOLD}Template type:${NC} $TEMPLATE_TYPE"
echo -e "${BOLD}Statement:${NC} $STATEMENT"
echo ""
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

# Generate template based on type
case "$TEMPLATE_TYPE" in
    theorem)
        cat <<EOF
-- General theorem template
theorem $STATEMENT := by
  -- TODO: Strategy - Describe proof approach here
  -- Step 1: [Describe what needs to be shown]
  have h1 : _ := by
    sorry
    -- TODO: Prove first key property

  -- Step 2: [Describe next step]
  have h2 : _ := by
    sorry
    -- TODO: Prove second key property

  -- Step 3: Combine results
  sorry
  -- TODO: Apply h1 and h2 to conclude
EOF
        ;;

    induction)
        cat <<EOF
-- Induction proof template
theorem $STATEMENT := by
  intro n
  induction n with
  | zero =>
    -- Base case: n = 0
    sorry
    -- TODO: Prove base case

  | succ n ih =>
    -- Inductive step: assume P(n), prove P(n+1)
    -- Inductive hypothesis: ih : P(n)
    sorry
    -- TODO: Use ih to prove P(n+1)
    -- Strategy: [Describe how to use ih]
EOF
        ;;

    cases)
        cat <<EOF
-- Case analysis proof template
theorem $STATEMENT := by
  intro h
  cases h with
  | inl h_left =>
    -- Case 1: Left branch
    sorry
    -- TODO: Handle left case
    -- Available: h_left

  | inr h_right =>
    -- Case 2: Right branch
    sorry
    -- TODO: Handle right case
    -- Available: h_right
EOF
        ;;

    calc)
        cat <<EOF
-- Calculation chain template
theorem $STATEMENT := by
  calc a = b := by
      sorry
      -- TODO: Prove a = b
      -- Hint: [Which lemma applies?]
    _ = c := by
      sorry
      -- TODO: Prove b = c
      -- Hint: [Simplify or rewrite?]
    _ = d := by
      sorry
      -- TODO: Prove c = d
      -- Hint: [Final step]
EOF
        ;;

    exists)
        cat <<EOF
-- Existential proof template
theorem $STATEMENT := by
  -- Strategy: Construct witness, then prove property
  use ?witness
  -- TODO: Provide the witness value

  constructor
  · -- Prove first property
    sorry
    -- TODO: Show witness satisfies first condition

  · -- Prove second property
    sorry
    -- TODO: Show witness satisfies second condition
EOF
        ;;
esac

echo ""
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${YELLOW}${BOLD}NEXT STEPS${NC}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo "1. Copy the template above into your Lean file"
echo "2. Fill in the TODO sections one at a time"
echo "3. Use ${BOLD}suggest_tactics.sh${NC} for tactic suggestions at each sorry"
echo "4. Build frequently: ${BOLD}lake env lean YourFile.lean${NC}"
echo "5. Use ${BOLD}sorry_analyzer.py --interactive${NC} to navigate sorries"
echo ""
echo -e "${YELLOW}Pro tip:${NC} Start with the easiest sorry (often base case or simple properties)"
echo ""
