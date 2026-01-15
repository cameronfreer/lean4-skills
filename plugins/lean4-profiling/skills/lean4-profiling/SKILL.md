---
name: lean4-profiling
description: Use when diagnosing slow Lean builds or proofs. Covers trace.profiler options, thresholding, and Firefox Profiler output.
---

# Lean 4 Profiling

## When to use

- A file or lemma is slow to elaborate or compile.
- A tactic is timing out or producing long traces.
- You need to identify hotspots before refactoring.

## Quick setup

```lean
set_option trace.profiler true
set_option trace.profiler.threshold 200
-- optional:
-- set_option trace.profiler.useHeartbeats true
-- set_option trace.profiler.output "/tmp/lean-profile.json"
-- set_option trace.profiler.output.pp true
```

Notes:
- Threshold is in milliseconds unless `useHeartbeats` is true.
- If `trace.profiler.output` is set, Lean writes Firefox Profiler JSON and suppresses stdout traces.

## Workflow

1. Narrow scope: add profiling options near the slow section.
2. Build a single target: `lake build +My.Module`.
3. If noisy, increase `trace.profiler.threshold`.
4. If wall-clock noise is high, enable `useHeartbeats`.
5. If using JSON output, open in Firefox Profiler and inspect hot traces.
6. Iterate by shrinking scope or adding local reductions to isolate the hotspot.

## What to record

- The slowest trace entries and surrounding lemmas.
- Whether the slowdown is elaboration, simp, or typeclass search.
- Any change in performance after narrowing scope.

