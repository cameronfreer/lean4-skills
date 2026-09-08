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
printf '%.300s\n' "$out"
# File, line, severity, and message matched TOGETHER: an unrelated line-7
# diagnostic plus the omit error elsewhere must not pass.
if ! grep -qE \
    "diagnostic_omit_negative[.]lean:7:[0-9]+: error: unexpected token 'omit'" \
    <<<"$out"; then
    printf '%s\n' "$out" >&2
    echo "FAIL: expected unexpected token 'omit' at the docstring line (7)" >&2
    exit 1
fi
echo "ok: all core snippet checks passed"
