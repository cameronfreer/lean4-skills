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
# Bin/ shape policy (Check 10): plugins/lean4/bin must EITHER not exist
# OR be a real directory containing only `lean4-skills-*` regular
# executable files (no symlinks-to-dir, no non-prefixed files, no
# non-executable files). The model-facing wrapper scripts under bin/
# (added in #129 to fix issue #117) get Claude Code's auto-PATH
# allowlist; the guardrails.sh stderr-suppression detector recognizes
# both bare and path-form invocations of `lean4-skills-*`. Check 10
# enforces shape only — adding a new wrapper file doesn't require
# editing this check; the expected wrapper-coverage assertion lives
# separately in test_contracts.sh.
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

# Curated model-facing wrappers under bin/ (see issue #117). Extensionless
# executables, named `lean4-skills-*`. Scanned alongside .sh files by
# Checks 1-8 (Bash 3.2 portability + shebang), and validated separately
# by Check 10 (shape: name pattern + regular file + exec bit).
WRAPPER_FILES=()
mapfile_compat WRAPPER_FILES < <(find \
  "$PLUGIN_ROOT/bin" \
  -maxdepth 1 -name 'lean4-skills-*' -type f 2>/dev/null | sort)

# Append wrappers to SHELL_FILES so Checks 1-8 scan their bodies for
# Bash 4+ / BSD-incompat constructs without code duplication. Check 10
# below additionally enforces the bin/ shape constraints.
for _w in "${WRAPPER_FILES[@]+"${WRAPPER_FILES[@]}"}"; do
  SHELL_FILES+=("$_w")
done

echo "Scanning ${#SHELL_FILES[@]} shell files (${#WRAPPER_FILES[@]} bin/ wrappers + $((${#SHELL_FILES[@]} - ${#WRAPPER_FILES[@]})) under hooks/+lib/scripts/) and ${#PY_FILES[@]} Python files for runtime-portability issues..."
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
# Check 10: bin/ shape — curated lean4-skills-* wrappers only
#
# plugins/lean4/bin is allowed (and expected, post-#129) to exist as a real
# directory containing the model-facing wrapper scripts. The shape rules:
#
#   * bin/ must be a directory, not a symlink. A whole-directory symlink
#     (e.g. bin -> lib/scripts) was the original PR #120 approach that
#     bypassed the guardrails detector wholesale; banned permanently.
#   * Every entry directly under bin/ must:
#     - be a regular file (no symlinks, no nested directories)
#     - be executable (the wrappers exist precisely so Claude Code's auto-
#       PATH allowlists them; non-executable files would be useless and
#       suggest someone forgot `chmod +x`)
#     - have a name matching ^lean4-skills-[a-z][a-z0-9-]*$
#
# Check 10 enforces *shape*, not a hardcoded list of wrapper names. Adding
# or removing wrappers is a docs / test_contracts.sh concern, not a lint
# change. Absent bin/ is also fine — the shape rule only fires when bin/
# exists and contains the wrong things.
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 10: bin/ shape (curated lean4-skills-* wrappers only) --"
found=0
if [[ -L "$PLUGIN_ROOT/bin" ]]; then
  warn "$PLUGIN_ROOT/bin is a symlink — whole-directory bin/ symlinks bypass the guardrails stderr-suppression detector wholesale. Replace with a real directory containing curated lean4-skills-* wrappers."
  found=1
elif [[ -e "$PLUGIN_ROOT/bin" && ! -d "$PLUGIN_ROOT/bin" ]]; then
  warn "$PLUGIN_ROOT/bin exists but is not a directory — bin/ must be a directory of curated lean4-skills-* wrappers (or absent)."
  found=1
elif [[ -d "$PLUGIN_ROOT/bin" ]]; then
  # Walk bin/ entries and enforce per-entry shape.
  # Using find with -mindepth 1 -maxdepth 1 to catch direct entries
  # (regular files, symlinks, and subdirs all).
  while IFS= read -r entry; do
    base=$(basename "$entry")
    if [[ -L "$entry" ]]; then
      warn "$PLUGIN_ROOT/bin/$base: symlink in bin/ is not allowed; wrappers must be regular files."
      found=1
      continue
    fi
    if [[ ! -f "$entry" ]]; then
      warn "$PLUGIN_ROOT/bin/$base: non-file entry in bin/ (directory or device); bin/ must contain only regular files."
      found=1
      continue
    fi
    if [[ ! "$base" =~ ^lean4-skills-[a-z][a-z0-9-]*$ ]]; then
      warn "$PLUGIN_ROOT/bin/$base: name does not match ^lean4-skills-[a-z][a-z0-9-]*\$ — bin/ is reserved for model-facing wrappers with that prefix."
      found=1
      continue
    fi
    if [[ ! -x "$entry" ]]; then
      warn "$PLUGIN_ROOT/bin/$base: wrapper is not executable. Run 'chmod +x' on it."
      found=1
    fi
  done < <(find "$PLUGIN_ROOT/bin" -mindepth 1 -maxdepth 1 2>/dev/null | sort)
fi
[[ $found -eq 0 ]] && ok "bin/ shape OK (${#WRAPPER_FILES[@]} curated lean4-skills-* wrappers)"

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
