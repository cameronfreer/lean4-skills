#!/usr/bin/env bash
# ---------------------------------------------------------------------------
# Runtime Portability Lint
# ---------------------------------------------------------------------------
# Scans .sh and .py files in the plugin runtime path (hooks/ and
# lib/scripts/) for portability issues across three policies:
#
#   * Bash 3.2 compatibility (Checks 1-7) — Bash 4+ / BSD-incompatible
#     constructs that break on macOS's default /bin/bash 3.2
#   * Shebang portability (Checks 8-9) — env-based shebangs only,
#     no absolute paths or polyglot trampolines
#   * Path structure (Check 10) — no shortcut paths that bypass
#     guardrail detectors
#
# Bash 3.2 policy: every .sh file in hooks/ and lib/scripts/ must run on Bash 3.2.
# If a script genuinely requires Bash 4+, it must say so in its shebang
# (e.g. #!/opt/homebrew/bin/bash) and NOT be called from the plugin
# runtime path.
#
# Shebang policy (Check 8): every .sh file in hooks/ and lib/scripts/ must
# start with exactly '#!/usr/bin/env bash' on its first line. Rejected:
# absolute Bash shebangs (#!/bin/bash, #!/opt/homebrew/bin/bash, ...),
# env-bash with extra arguments (#!/usr/bin/env bash -e — not portable on
# Linux without env -S, which interprets 'bash -e' as one program name),
# and files with no shebang at all. Bash-4+ opt-out scripts must live
# outside this scope per the policy above. Set flags via 'set -...'
# inside the script body, not via shebang args.
#
# Python shebang policy (Check 9): every .py file in hooks/ and lib/scripts/
# that has a shebang must use exactly '#!/usr/bin/env python3'. Library
# modules without a shebang are out of scope. The intent is to forbid the
# '#!/usr/bin/env sh' polyglot trampoline pattern (which buries shell in
# __doc__ and leaks into --help output) and absolute interpreter paths.
#
# Path policy (Check 10): plugins/lean4/bin must not exist as a symlink,
# file, or directory. Such a shortcut would let callers invoke runtime
# scripts via paths that guardrails.sh's Lean-script stderr-suppression
# detector doesn't recognize (it matches lib/scripts/ and scripts/ only),
# silently bypassing the safety check. Reintroduce only with a matching
# guardrail update.
#
# Run:  bash plugins/lean4/tools/lint_runtime_portability.sh
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

# Collect all .sh files in the runtime path.
#
# Note on the "${arr[@]+"${arr[@]}"}" idiom used below in the check
# loops: on Bash 3.2 (macOS) with set -u, expanding "${arr[@]}" on an
# empty array errors with "unbound variable" — a quirk fixed in Bash 4.4.
# The alternative-value form "${arr[@]+...}" expands to nothing when the
# array is empty and to "${arr[@]}" otherwise, dodging the bug. SHELL_FILES
# and PY_FILES can each be empty during self-tests (when a probe of one
# type is present without the other), so every loop over them uses this
# guarded form.
mapfile_compat() {
  # Can't use mapfile itself — this lint must run on Bash 3.2 too!
  local arr_name="$1"
  local i=0
  # shellcheck disable=SC2034  # $line consumed indirectly via eval
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

PY_FILES=()
mapfile_compat PY_FILES < <(find \
  "$PLUGIN_ROOT/hooks" \
  "$PLUGIN_ROOT/lib/scripts" \
  -name '*.py' -type f 2>/dev/null | sort)

echo "Scanning ${#SHELL_FILES[@]} shell scripts and ${#PY_FILES[@]} Python files for runtime-portability issues..."
echo ""
# Note: we don't early-exit on empty arrays here. Check 10 (no bin shortcut
# path) is a structural check that must always run regardless of file
# counts; the per-file Checks 1–9 are no-ops with empty arrays anyway.

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
for f in "${SHELL_FILES[@]+"${SHELL_FILES[@]}"}"; do
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
for f in "${SHELL_FILES[@]+"${SHELL_FILES[@]}"}"; do
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
for f in "${SHELL_FILES[@]+"${SHELL_FILES[@]}"}"; do
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
for f in "${SHELL_FILES[@]+"${SHELL_FILES[@]}"}"; do
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
for f in "${SHELL_FILES[@]+"${SHELL_FILES[@]}"}"; do
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
for f in "${SHELL_FILES[@]+"${SHELL_FILES[@]}"}"; do
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
for f in "${SHELL_FILES[@]+"${SHELL_FILES[@]}"}"; do
  while IFS= read -r match; do
    warn "$match"
    found=1
  done < <(grep -n 'mktemp.*XXXXXX[^"'\''[:space:])]*[^X"'\''[:space:])]' "$f" 2>/dev/null | sed "s|^|$(basename "$f"):|")
done
[[ $found -eq 0 ]] && ok "No mktemp with post-X suffix found"

# ---------------------------------------------------------------------------
# Check 8: portable shebangs in runtime path
#
# Hooks (invoked directly via hooks.json) and lib/scripts/ must start with
# exactly '#!/usr/bin/env bash' so they work on hosts without /bin/bash
# (NixOS, minimal containers). Rejected:
#   * absolute Bash paths: #!/bin/bash, #!/opt/homebrew/bin/bash, ...
#   * env-bash with arguments: #!/usr/bin/env bash -e (not portable on
#     Linux — env interprets 'bash -e' as one program name; needs env -S)
#   * any non-bash interpreter
#   * no shebang at all (runtime scripts must declare their interpreter)
# Set flags via 'set -...' inside the script body, not via shebang args.
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 8: portable shebangs in runtime path --"
found=0
for f in "${SHELL_FILES[@]+"${SHELL_FILES[@]}"}"; do
  first_line=$(head -n1 "$f")
  if [[ "$first_line" != "#!/usr/bin/env bash" ]]; then
    warn "$(basename "$f"):1: non-portable shebang '$first_line' — runtime scripts must use exactly '#!/usr/bin/env bash'"
    found=1
  fi
done
[[ $found -eq 0 ]] && ok "All runtime scripts use #!/usr/bin/env bash"

# ---------------------------------------------------------------------------
# Check 9: portable Python shebangs in hooks/ and lib/scripts/
#
# Every .py file under hooks/ and lib/scripts/ (recursively, including
# lib/scripts/tests/) that HAS a shebang must use exactly
# '#!/usr/bin/env python3'. Library modules without a shebang (imported,
# not executed) are out of scope. Intent: forbid the '#!/usr/bin/env sh'
# polyglot trampoline (which leaks 'exec "$0"' into __doc__ and surfaces
# in --help output) and absolute interpreter paths.
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 9: portable Python shebangs in hooks/ and lib/scripts/ --"
found=0
for f in "${PY_FILES[@]+"${PY_FILES[@]}"}"; do
  first_line=$(head -n1 "$f")
  # Only validate files that declare a shebang. No-shebang library
  # modules can't be polyglot regressions and stay out of scope.
  case "$first_line" in
    "#!"*) ;;
    *) continue ;;
  esac
  if [[ "$first_line" != "#!/usr/bin/env python3" ]]; then
    warn "$(basename "$f"):1: non-portable Python shebang '$first_line' — runtime .py with a shebang must use exactly '#!/usr/bin/env python3'"
    found=1
  fi
done
[[ $found -eq 0 ]] && ok "All shebanged Python runtime files use #!/usr/bin/env python3"

# ---------------------------------------------------------------------------
# Check 10: no plugins/lean4/bin shortcut path
#
# plugins/lean4/bin (as symlink, dir, or file) gives callers a shorter
# invocation path that bypasses guardrails.sh's Lean-script
# stderr-suppression detector, which matches '$LEAN4_SCRIPTS/...',
# 'plugins/lean4/lib/scripts/...', and './scripts/...' only. A reappearance
# means the safety check can be silently bypassed via 'bin/foo.py 2>/dev/null'.
# Reintroduce only together with a matching detector update.
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 10: no plugins/lean4/bin shortcut path --"
if [[ -L "$PLUGIN_ROOT/bin" || -e "$PLUGIN_ROOT/bin" ]]; then
  warn "$PLUGIN_ROOT/bin exists — shortcut bypasses guardrails.sh stderr-suppression detector (matches lib/scripts/ and scripts/ only). Drop the path or update the detector first."
else
  ok "No plugins/lean4/bin shortcut path"
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "================================"
if [[ $ISSUES -eq 0 ]]; then
  echo "✓ All ${#SHELL_FILES[@]} shell + ${#PY_FILES[@]} Python runtime files pass portability checks"
  exit 0
else
  echo "⚠️  $ISSUES issue(s) found — see Checks 1–10 for context (Bash 3.2 compat, runtime shebangs, shortcut path)"
  exit 1
fi
