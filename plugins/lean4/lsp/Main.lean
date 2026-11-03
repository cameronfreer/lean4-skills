import LspCli.Doctor
open Lean System LspCli

def run (r : Request) : IO Response := do
  if r.operation == .help then
    return {ok := true, operation := "help", status := "ok", data := toJson ("Commands: doctor, goal, diagnostics, hover, definition, references, code-actions, search, attempt, status, stop. Public positions are 1-based Unicode codepoints; ranges are end-exclusive." : String)}
  let root ← resolveProject r.project
  let file ← r.file.mapM (resolveFile root)
  if r.operation == .doctor then
    let result ← probeProject root r.timeoutMs
    let data := Json.mkObj [("buildVersion", toJson Lean.versionString), ("projectToolchainAvailable", toJson result.toolchainAvailable), ("projectServerAvailable", toJson result.serverAvailable)]
    if result.serverAvailable then return {ok := true, operation := r.operation.name, projectRoot := some root.toString, status := "ok", data := data}
    else if result.timedOut then return {ok := false, operation := r.operation.name, projectRoot := some root.toString, status := "timeout", data := data, error := some ⟨"timeout", "project server probe timed out", 4⟩}
    else return {ok := false, operation := r.operation.name, projectRoot := some root.toString, status := "unavailable", data := data, error := some ⟨"server_unavailable", "project toolchain or server unavailable", 3⟩}
  return {ok := false, operation := r.operation.name, projectRoot := some root.toString, file := file.map (·.toString), status := "unavailable", error := some ⟨"not_implemented", "session operations are temporarily unavailable", 3⟩}

def main (args : List String) : IO UInt32 := do
  let result : Response ← match parseArgs args with
    | .error e => pure ({ok := false, operation := args.headD "", status := "invalid_invocation", error := some e} : Response)
    | .ok req => try run req catch e => pure {ok := false, operation := req.operation.name, status := "invalid_invocation", error := some ⟨"invalid_project_or_file", e.toString, 2⟩}
  IO.println (toJson result).compress
  return result.exitCode
