import LspCli.Session
open Lean System Std
namespace LspCli.Trials

private def offset (text : String) (p : PublicPosition) : Nat := Id.run do
  let lines := text.splitOn "\n"
  let mut n := 0
  for line in lines.take (p.line - 1) do n := n + line.length + 1
  return n + p.column - 1

private def endPosition (start : PublicPosition) (snippet : String) : PublicPosition :=
  let lines := snippet.splitOn "\n"
  if lines.length == 1 then ⟨start.line, start.column + snippet.length⟩
  else ⟨start.line + lines.length - 1, lines.getLast!.length + 1⟩

private def invalidResponse (base : Response) (e : CliError) : Response :=
  {base with ok := false, status := "invalid_invocation", error := some e}

private def observe (s : Session) (r : Request) (deadline : Deadline) : IO Response := do
  let base : Response := {ok := true, operation := r.operation.name, projectRoot := some s.root.toString, status := "ok"}
  if r.operation != .attempt then return invalidResponse base (invalid "expected attempt operation")
  let some file := r.file | return invalidResponse base (invalid "missing file")
  let some range := r.range | return invalidResponse base (invalid "missing range")
  let some snippetsFile := r.snippetsFile | return invalidResponse base (invalid "missing snippets file")
  let snippetsPath := if snippetsFile.isAbsolute then snippetsFile else s.root / snippetsFile
  let candidates : Array String ← match (← try pure (some (← IO.FS.readFile snippetsPath)) catch _ => pure none) with
    | none => return invalidResponse base (invalid "cannot read snippets file")
    | some contents => match (Json.parse contents).bind fromJson? with
      | .error _ => return invalidResponse base (invalid "snippets file must contain an array of strings")
      | .ok xs => pure xs
  if candidates.isEmpty then return invalidResponse base (invalid "candidate array must not be empty")
  s.refresh deadline
  let path ← resolveFile s.root file
  let text ← IO.FS.readFile path
  let d ← s.openDocument path text
  let base := {base with file := some path.toString, documentVersion := some d.version, sourceIdentity := some d.identity}
  if let .error e := checkSourceIdentity r.expectSource (some d.identity) then return {base with ok := false, status := "stale_input", error := some e}
  if let .error e := validateRange (FileMap.ofString text) range then return invalidResponse base e
  let liveDiagnostics ← s.waitDocument d deadline
  if Session.staleImports liveDiagnostics then
    return {base with ok := false, status := "stale_dependency", data := ← s.publicJson d.uri (toJson liveDiagnostics), error := some ⟨"stale_dependency", "Imports changed. Run the project's dependency-aware lake build, then stop/restart this session.", 4⟩}
  let chars := text.toList
  let left := String.ofList (chars.take (offset text range.start))
  let right := String.ofList (chars.drop (offset text range.end))
  let scratch := s.root / s!".lean4-skills-trial-{s.nonce}.lean"
  let mut results := #[]
  let mut errors := false
  for candidate in candidates do
    let virtual ← s.openDocument scratch (left ++ candidate ++ right) true
    try
      let diagnostics ← s.waitDocument virtual deadline
      let goal ← s.plainGoal virtual (endPosition range.start candidate) deadline
      let diagnostics ← s.publicJson virtual.uri (toJson diagnostics)
      let goal ← s.publicJson virtual.uri goal
      errors := errors || (diagnostics.getArr?).toOption.any (·.any fun x => (x.getObjValAs? Nat "severity").toOption == some 1)
      results := results.push (Json.mkObj [("candidate", toJson candidate), ("status", toJson (Session.goalStatus goal)), ("goal", goal), ("diagnostics", diagnostics), ("sourceIdentity", toJson d.identity)])
    finally s.closeDocument virtual.uri
  let error := if errors then some (⟨"lean_diagnostics", "Lean reported errors in one or more candidates.", 1⟩ : CliError) else none
  return {base with ok := error.isNone, error, data := Json.mkObj [("candidates", toJson results)]}

def run (s : Session) (r : Request) : IO Response := s.runBounded r (observe s r)
end LspCli.Trials
