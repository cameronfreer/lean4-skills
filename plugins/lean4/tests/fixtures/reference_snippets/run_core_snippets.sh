#!/usr/bin/env bash
# Core-Lean (no Mathlib) reference-snippet checks. Run from a directory whose
# `lean-toolchain` pins the intended Lean (CI: tests/fixtures/lean_file_gate).
#   bash ../reference_snippets/run_core_snippets.sh
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"

for f in core_instance_snippets.lean diagnostic_snippets.lean; do
    echo "== $f (must elaborate)"
    lean "$here/$f"
done

echo "== diagnostic_omit_negative.lean (must FAIL at the docstring line with unexpected token 'omit')"
if out="$(lean "$here/diagnostic_omit_negative.lean" 2>&1)"; then
    echo "FAIL: diagnostic_omit_negative.lean elaborated, but it documents a parse error" >&2
    exit 1
fi
printf '%s\n' "$out" | head -c 300; echo
grep -qF "unexpected token 'omit'" <<<"$out" \
    || { echo "FAIL: message no longer contains unexpected token 'omit'" >&2; exit 1; }
grep -qE "diagnostic_omit_negative\.lean:7:" <<<"$out" \
    || { echo "FAIL: error not reported at the docstring line (7)" >&2; exit 1; }
echo "ok: all core snippet checks passed"
