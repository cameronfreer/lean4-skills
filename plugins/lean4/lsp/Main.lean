import LspCli.Protocol
open Lean System LspCli

def run (r : Request) : IO Response := do
  if r.operation == .help then
    return {ok := true, operation := "help", status := "ok", data := toJson ("Commands: doctor, goal, diagnostics, hover, definition, references, code-actions, search, attempt, status, stop. Public positions are 1-based Unicode codepoints; ranges are end-exclusive." : String)}
  let root ← resolveProject r.project
  let file ← r.file.mapM (resolveFile root)
  if r.operation == .doctor then
    let server ← try
      let out ← IO.Process.output {cmd := "lake", args := #["env", "lean", "--version"], cwd := some root}
      pure (out.exitCode == 0)
    catch _ => pure false
    let data := Json.mkObj [("buildVersion", toJson Lean.versionString), ("projectToolchainAvailable", toJson server), ("projectServerAvailable", Json.null)]
    if server then return {ok := true, operation := r.operation.name, projectRoot := some root.toString, status := "server_unchecked", data := data}
    else return {ok := false, operation := r.operation.name, projectRoot := some root.toString, status := "unavailable", data := data, error := some ⟨"server_unavailable", "project toolchain unavailable", 3⟩}
  return {ok := false, operation := r.operation.name, projectRoot := some root.toString, file := file.map (·.toString), status := "unavailable", error := some ⟨"not_implemented", "session operations are temporarily unavailable", 3⟩}

def main (args : List String) : IO UInt32 := do
  let result : Response ← match parseArgs args with
    | .error e => pure ({ok := false, operation := args.headD "", status := "invalid_invocation", error := some e} : Response)
    | .ok req => try run req catch e => pure {ok := false, operation := req.operation.name, status := "invalid_invocation", error := some ⟨"invalid_project_or_file", e.toString, 2⟩}
  IO.println (toJson result).compress
  return (result.error.map CliError.exitCode |>.getD 0).toUInt32
