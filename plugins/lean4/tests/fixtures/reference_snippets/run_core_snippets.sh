#!/usr/bin/env bash
# Core-Lean (no Mathlib) reference-snippet checks. Run from a directory whose
# `lean-toolchain` pins the intended Lean (CI: tests/fixtures/lean_file_gate).
#   bash ../reference_snippets/run_core_snippets.sh
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"

for f in core_instance_snippets.lean diagnostic_snippets.lean \
         grind_snippets.lean grind_suggestions_snippets.lean \
         meta_snippets.lean verso_snippets.lean; do
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

# The steps below run from a scratch directory, which has no lean-toolchain of
# its own: resolve the caller's pinned `lean` once and use it by path.
lean_bin="$(command -v lean)"
if command -v elan >/dev/null 2>&1; then
    lean_bin="$(elan which lean)"
fi
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

echo "== linter_rule.lean + linter_use.lean (a linter runs only in modules that import it)"
cp "$here/linter_rule.lean" "$scratch/LinterRule.lean"
cp "$here/linter_use.lean" "$scratch/LinterUse.lean"
(
    cd "$scratch"
    "$lean_bin" -o LinterRule.olean LinterRule.lean
    LEAN_PATH="$scratch" "$lean_bin" -Dweak.linter.myRule=true LinterUse.lean
)

echo "== profiler_probe.lean (-Dtrace.profiler.output writes Firefox Profiler JSON, prints nothing)"
out="$("$lean_bin" -Dtrace.profiler=true -Dtrace.profiler.threshold=1 \
    "-Dtrace.profiler.output=$scratch/profile.json" "$here/profiler_probe.lean" 2>&1)"
if [[ -n "$out" ]]; then
    printf '%s\n' "$out" >&2
    echo "FAIL: trace.profiler.output given, but trace messages were still printed" >&2
    exit 1
fi
if ! grep -qF '"threads"' "$scratch/profile.json" 2>/dev/null; then
    echo "FAIL: trace.profiler.output given on the command line, but no Firefox Profiler JSON was written" >&2
    exit 1
fi

echo "== profiler_infile.lean (the same option set inside the file writes nothing)"
cp "$here/profiler_infile.lean" "$scratch/ProfilerInfile.lean"
out="$(cd "$scratch" && "$lean_bin" ProfilerInfile.lean 2>&1)"
if [[ -n "$out" ]]; then
    printf '%s\n' "$out" >&2
    echo "FAIL: in-file trace.profiler.output should suppress the trace messages" >&2
    exit 1
fi
if [[ -e "$scratch/profile-infile.json" ]]; then
    echo "FAIL: in-file trace.profiler.output now writes a file; update profiling-workflows.md" >&2
    exit 1
fi
echo "ok: all core snippet checks passed"
