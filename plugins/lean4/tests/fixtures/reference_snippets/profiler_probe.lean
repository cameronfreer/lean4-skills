-- Evidence for `references/profiling-workflows.md` (#181). `run_core_snippets.sh`
-- elaborates this file with `-Dtrace.profiler=true -Dtrace.profiler.output=…`
-- and checks that a Firefox Profiler JSON file is written, stdout is empty, and
-- the profile holds a real Kernel frame; then that `output.pp` keeps the full
-- trace text only when given with `-D`, not when set in the file.
theorem profiled : (List.range 2000).foldl (· + ·) 0 = 1999000 := by decide +kernel
