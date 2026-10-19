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

# `bv_decide` as a `grind` command exists from Lean v4.34.0 on.
if [[ "$(lean --version)" =~ version\ ([0-9]+)\.([0-9]+)\. ]] &&
    (( BASH_REMATCH[1] > 4 || BASH_REMATCH[2] >= 34 )); then
    echo "== grind_bv_snippets.lean (must elaborate; Lean v4.34.0+)"
    lean "$here/grind_bv_snippets.lean"
else
    echo "== grind_bv_snippets.lean skipped: needs Lean v4.34.0+"
fi

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
if [[ ! -s "$scratch/profile.json" ]]; then
    echo "FAIL: trace.profiler.output given on the command line, but no Firefox Profiler JSON was written" >&2
    exit 1
fi
# Frame names in the exported profile, one per line (a name can span lines).
frames() {
    python3 -I -c 'import json, sys
d = json.load(open(sys.argv[1]))
print("\n".join(sorted({s for t in d["threads"] for s in t["stringArray"]})))' "$1"
}
# The probe's `decide +kernel` must appear as a real Kernel frame (the exporter
# adds a `runFrontend` root by itself); by default a frame is its class only.
names="$(frames "$scratch/profile.json")"
if ! grep -qxF 'Kernel' <<<"$names"; then
    echo "FAIL: the profile has no Kernel frame from profiler_probe.lean" >&2
    exit 1
fi
if grep -qF 'typechecking declarations' <<<"$names"; then
    echo "FAIL: without trace.profiler.output.pp, frames should carry only class and tag" >&2
    exit 1
fi

echo "== profiler_probe.lean (-Dtrace.profiler.output.pp=true keeps the full trace text)"
"$lean_bin" -Dtrace.profiler=true -Dtrace.profiler.threshold=1 \
    "-Dtrace.profiler.output=$scratch/profile-pp.json" -Dtrace.profiler.output.pp=true \
    "$here/profiler_probe.lean"
if ! grep -qF 'Kernel: typechecking declarations' <<<"$(frames "$scratch/profile-pp.json")"; then
    echo "FAIL: -Dtrace.profiler.output.pp=true should keep the full Kernel trace text" >&2
    exit 1
fi

echo "== profiler_probe.lean (output.pp set inside the file is not used by the exporter)"
{ echo 'set_option trace.profiler.output.pp true'; cat "$here/profiler_probe.lean"; } \
    > "$scratch/ProfilerPpInfile.lean"
"$lean_bin" -Dtrace.profiler=true -Dtrace.profiler.threshold=1 \
    "-Dtrace.profiler.output=$scratch/profile-pp-infile.json" "$scratch/ProfilerPpInfile.lean"
if grep -qF 'typechecking declarations' <<<"$(frames "$scratch/profile-pp-infile.json")"; then
    echo "FAIL: in-file trace.profiler.output.pp now reaches the exporter; update profiling-workflows.md" >&2
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
