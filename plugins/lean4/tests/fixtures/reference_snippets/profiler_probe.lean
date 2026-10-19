-- Evidence for `references/profiling-workflows.md` (#181). `run_core_snippets.sh`
-- elaborates this file with `-Dtrace.profiler=true -Dtrace.profiler.output=…`
-- and checks that a Firefox Profiler JSON file is written and stdout is empty.
theorem profiled : (List.range 2000).foldl (· + ·) 0 = 1999000 := by decide +kernel
