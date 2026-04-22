#!/usr/bin/env bash
# ---------------------------------------------------------------------------
# Bash 3.2 Compatibility Lint
# ---------------------------------------------------------------------------
# Scans all .sh files in the plugin runtime path (hooks/ and lib/scripts/)
# for Bash 4+ constructs that break on macOS's default /bin/bash 3.2.
#
# Policy: every .sh file in hooks/ and lib/scripts/ must run on Bash 3.2.
# If a script genuinely requires Bash 4+, it must say so in its shebang
# (e.g. #!/opt/homebrew/bin/bash) and NOT be called from the plugin
# runtime path.
#
# Run:  bash plugins/lean4/tools/lint_bash_compat.sh
# ---------------------------------------------------------------------------
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

ISSUES=0

warn() {
  echo "⚠️  $1"
  ((ISSUES++)) || true
}

ok() {
  echo "✓ $1"
}

# Collect all .sh files in the runtime path
mapfile_compat() {
  # Can't use mapfile itself — this lint must run on Bash 3.2 too!
  local arr_name="$1"
  local i=0
  while IFS= read -r line; do
    eval "${arr_name}[$i]=\"\$line\""
    ((i++)) || true
  done
}

SHELL_FILES=()
mapfile_compat SHELL_FILES < <(find \
  "$PLUGIN_ROOT/hooks" \
  "$PLUGIN_ROOT/lib/scripts" \
  -name '*.sh' -type f 2>/dev/null | sort)

if [[ ${#SHELL_FILES[@]} -eq 0 ]]; then
  echo "No .sh files found under hooks/ or lib/scripts/"
  exit 0
fi

echo "Scanning ${#SHELL_FILES[@]} shell scripts for Bash 4+ constructs..."
echo ""

# ---------------------------------------------------------------------------
# Check 1: case-modifier syntax ${var,,}, ${var,}, ${var^^}, ${var^} (Bash 4.0+)
#
# This check is intentionally a HEURISTIC, not a full Bash parameter-expansion
# parser. The regex excludes all parameter-expansion operators that can
# legitimately contain , or ^ before a closing } (substitution /, prefix-
# removal #, suffix-removal %, colon forms :-/:=/:+/:?, non-colon forms
# -/=/?/+). It catches all common case-modifier forms but has one known
# false-negative: case-modifiers on arithmetic subscripts like ${arr[i-1],,}
# or ${arr[i+1]^} do not match because the - and + are excluded. This is an
# accepted trade-off; the alternative is building a full Bash parser.
# ---------------------------------------------------------------------------
echo "-- Check 1: case-modifier syntax (\${var,,} / \${var,} / \${var^^} / \${var^}) --"
found=0
for f in "${SHELL_FILES[@]}"; do
  while IFS= read -r match; do
    warn "$match"
    found=1
  done < <(grep -En '\$\{[^}/#%:=?+-]*((\^\^?)|(,,?))[^}]*\}' "$f" 2>/dev/null | sed "s|^|$(basename "$f"):|")
done
[[ $found -eq 0 ]] && ok "No case-modifier syntax found"

# ---------------------------------------------------------------------------
# Check 2: associative arrays (declare|local|typeset -...A..., Bash 4.0+)
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 2: associative arrays (declare -A / local -A / typeset -A) --"
found=0
for f in "${SHELL_FILES[@]}"; do
  while IFS= read -r match; do
    warn "$match"
    found=1
  done < <(grep -En '(declare|local|typeset)[[:space:]]+[-+][[:alpha:]]*A' "$f" 2>/dev/null | sed "s|^|$(basename "$f"):|")
done
[[ $found -eq 0 ]] && ok "No associative arrays found"

# ---------------------------------------------------------------------------
# Check 3: namerefs (declare|local|typeset -...n..., Bash 4.3+)
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 3: namerefs (declare -n / local -n / typeset -n) --"
found=0
for f in "${SHELL_FILES[@]}"; do
  while IFS= read -r match; do
    warn "$match"
    found=1
  done < <(grep -En '(declare|local|typeset)[[:space:]]+[-+][[:alpha:]]*n' "$f" 2>/dev/null | sed "s|^|$(basename "$f"):|")
done
[[ $found -eq 0 ]] && ok "No namerefs found"

# ---------------------------------------------------------------------------
# Check 4: mapfile / readarray (Bash 4.0+)
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 4: mapfile / readarray --"
found=0
for f in "${SHELL_FILES[@]}"; do
  while IFS= read -r match; do
    warn "$match"
    found=1
  done < <(grep -n '\bmapfile\b\|\breadarray\b' "$f" 2>/dev/null | sed "s|^|$(basename "$f"):|")
done
[[ $found -eq 0 ]] && ok "No mapfile/readarray found"

# ---------------------------------------------------------------------------
# Check 5: coproc (Bash 4.0+)
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 5: coproc --"
found=0
for f in "${SHELL_FILES[@]}"; do
  while IFS= read -r match; do
    warn "$match"
    found=1
  done < <(grep -n '\bcoproc\b' "$f" 2>/dev/null | sed "s|^|$(basename "$f"):|")
done
[[ $found -eq 0 ]] && ok "No coproc found"

# ---------------------------------------------------------------------------
# Check 6: ${var@Q} and other ${var@op} expansions (Bash 4.4+)
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 6: \${var@op} expansions --"
found=0
for f in "${SHELL_FILES[@]}"; do
  while IFS= read -r match; do
    warn "$match"
    found=1
  done < <(grep -n '\${[^}]*@[A-Za-z]}' "$f" 2>/dev/null | sed "s|^|$(basename "$f"):|")
done
[[ $found -eq 0 ]] && ok "No \${var@op} expansions found"

# ---------------------------------------------------------------------------
# Check 7: mktemp with suffix after X's (BSD mktemp incompatibility)
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 7: mktemp with suffix after X's --"
found=0
for f in "${SHELL_FILES[@]}"; do
  while IFS= read -r match; do
    warn "$match"
    found=1
  done < <(grep -n 'mktemp.*XXXXXX[^"'\''[:space:])]*[^X"'\''[:space:])]' "$f" 2>/dev/null | sed "s|^|$(basename "$f"):|")
done
[[ $found -eq 0 ]] && ok "No mktemp with post-X suffix found"

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "================================"
if [[ $ISSUES -eq 0 ]]; then
  echo "✓ All ${#SHELL_FILES[@]} scripts are Bash 3.2 compatible"
  exit 0
else
  echo "⚠️  $ISSUES issue(s) found — these constructs break on macOS /bin/bash 3.2"
  exit 1
fi
