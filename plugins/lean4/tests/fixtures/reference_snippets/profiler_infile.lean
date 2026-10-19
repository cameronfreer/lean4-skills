-- Evidence for `references/profiling-workflows.md` (#181): setting the output
-- path in the file suppresses the trace messages but writes no file.
-- `run_core_snippets.sh` runs this from a scratch directory and checks that
-- `profile-infile.json` is absent and stdout is empty.
set_option trace.profiler true
set_option trace.profiler.threshold 1
set_option trace.profiler.output "profile-infile.json"

theorem profiled : (List.range 2000).foldl (· + ·) 0 = 1999000 := by decide +kernel
