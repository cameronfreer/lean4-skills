# Profiling Workflows

> **Scope:** Not part of the prove/autoprove default loop. Consulted when diagnosing slow Lean builds or proofs.

> **Version metadata:**
> - **Verified on:** Lean `v4.33.1` and `v4.35.0` (options and their descriptions read from `Lean/Util/Trace.lean`; in-file traces, command-line JSON export via `lean` and `lake env lean`, and `lake build +Module` run)
> - **Last validated:** 2026-10-19
> - **Confidence:** high for the option behaviour (JSON export and the in-file pitfall run in CI: `tests/fixtures/reference_snippets/run_core_snippets.sh`); `trace.profiler.serve` is from its option description, not run

## When to Use

- A file or lemma is slow to elaborate or compile
- A tactic is timing out or producing long traces
- You need hotspots before refactoring

## Composable Profiling Blocks

- `Scope`: set options near the slow section
- `Target`: build a single module with `lake build +My.Module`
- `Threshold`: raise/lower `trace.profiler.threshold`
- `Clock`: use `useHeartbeats` when wall-clock noise is high
- `Output`: write JSON from the command line to inspect in Firefox Profiler

## Quick Setup

In the file, for trace messages:

```lean
set_option trace.profiler true
set_option trace.profiler.threshold 200
-- optional:
-- set_option trace.profiler.useHeartbeats true
```

For Firefox Profiler JSON, pass the options on the command line:

```text
lean -Dtrace.profiler=true -Dtrace.profiler.output=/tmp/lean-profile.json My/Module.lean
lake env lean -Dtrace.profiler=true -Dtrace.profiler.output=/tmp/lean-profile.json My/Module.lean
```

Notes:
- **Threshold units.** `trace.profiler.threshold` is in milliseconds (default `10`), or in heartbeats when `trace.profiler.useHeartbeats` is true.
- **JSON output.** With `trace.profiler.output` set, Lean writes Firefox Profiler JSON (`meta`, `threads`, `libs`) and prints no trace messages.
- **Pitfall: set the output path on the command line.** `set_option trace.profiler.output "…"` *inside* the file suppresses the trace messages but writes no file (checked on `v4.33.1` and `v4.35.0`), so the profile is silently lost.
- **`trace.profiler.output.pp`.** If false (the default), exported trace nodes carry only the trace class and tag. To keep the full text, pass `-Dtrace.profiler.output.pp=true` on the command line too. The JSON exporter reads the command-line options, so an in-file `set_option trace.profiler.output.pp true` is not used.
- **`trace.profiler.serve`.** If true, it serves the data over HTTP and opens `https://profiler.firefox.com`, blocking until Ctrl+C.

## Workflow

1. Narrow scope: add profiling options near the slow section
2. Build a single target: `lake build +My.Module`
3. If noisy, increase `trace.profiler.threshold`
4. If wall-clock noise is high, enable `useHeartbeats`
5. For JSON, rerun the module with `lake env lean -Dtrace.profiler=true -Dtrace.profiler.output=…`, open it in Firefox Profiler and inspect hot traces
6. Iterate by shrinking scope or adding local reductions to isolate the hotspot

## What to Record

- The slowest trace entries and surrounding lemmas
- Whether the slowdown is elaboration, simp, or typeclass search
- Any change in performance after narrowing scope

## See Also

- [performance-optimization.md](performance-optimization.md) — optimization patterns (irreducible wrappers, simp budgets)
