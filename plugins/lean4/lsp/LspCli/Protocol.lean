import Lean
open Lean System
namespace LspCli

inductive Operation where
  | doctor | goal | diagnostics | hover | definition | references | codeActions | search | attempt | status | stop | help
  deriving Repr, BEq, Inhabited, ToJson, FromJson

def Operation.name : Operation → String
  | .codeActions => "code-actions"
  | .doctor => "doctor" | .goal => "goal" | .diagnostics => "diagnostics"
  | .hover => "hover" | .definition => "definition" | .references => "references"
  | .search => "search" | .attempt => "attempt" | .status => "status" | .stop => "stop" | .help => "help"

def Operation.parse : String → Option Operation
  | "doctor" => some .doctor | "goal" => some .goal | "diagnostics" => some .diagnostics
  | "hover" => some .hover | "definition" => some .definition | "references" => some .references
  | "code-actions" => some .codeActions | "search" => some .search | "attempt" => some .attempt
  | "status" => some .status | "stop" => some .stop | "help" | "--help" | "-h" => some .help
  | _ => none

structure CliError where
  code : String
  message : String
  exitCode : Nat := 2
  deriving Repr, BEq, Inhabited, ToJson, FromJson

def invalid (message : String) : CliError := ⟨"invalid_invocation", message, 2⟩
structure PublicPosition where
  line : Nat
  column : Nat
  deriving Repr, BEq, Inhabited, ToJson, FromJson
structure PublicRange where
  start : PublicPosition
  «end» : PublicPosition
  deriving Repr, BEq, Inhabited, ToJson, FromJson
structure Request where
  operation : Operation
  project : Option FilePath := none
  file : Option FilePath := none
  query : Option String := none
  line : Option Nat := none
  column : Option Nat := none
  range : Option PublicRange := none
  snippetsFile : Option FilePath := none
  expectSource : Option String := none
  limit : Option Nat := none
  timeoutMs : Nat := 30000
  json : Bool := false
  deriving Repr, Inhabited, ToJson, FromJson
structure Response where
  schema : String := "lean4-lsp/v1"
  ok : Bool
  operation : String
  projectRoot : Option String := none
  file : Option String := none
  documentVersion : Option Nat := none
  sourceIdentity : Option String := none
  status : String
  data : Json := Json.null
  error : Option CliError := none
  deriving ToJson, FromJson

def positive (s : String) : Except CliError Nat := do
  match s.toNat? with
  | some n => if n > 0 then pure n else throw (invalid "expected a positive integer")
  | none => throw (invalid "expected a positive integer")

def parsePosition (s : String) : Except CliError PublicPosition := do
  match s.splitOn ":" with
  | [l, c] => return ⟨← positive l, ← positive c⟩
  | _ => throw (invalid "expected LINE:COLUMN")
def parseRange (s : String) : Except CliError PublicRange := do
  match s.splitOn "-" with
  | [a, b] =>
    let start ← parsePosition a
    let stop ← parsePosition b
    if start.line > stop.line || (start.line == stop.line && start.column > stop.column) then
      throw (invalid "range is reversed")
    return ⟨start, stop⟩
  | _ => throw (invalid "expected START-END range")

private def parseOptions : List String → Request → Except CliError Request
  | [], r => pure r
  | "--json" :: xs, r => if r.json then throw (invalid "duplicate --json") else parseOptions xs {r with json := true}
  | "--project" :: v :: xs, r => parseOptions xs {r with project := some ⟨v⟩}
  | "--line" :: v :: xs, r => do parseOptions xs {r with line := some (← positive v)}
  | "--column" :: v :: xs, r => do parseOptions xs {r with column := some (← positive v)}
  | "--range" :: v :: xs, r => do parseOptions xs {r with range := some (← parseRange v)}
  | "--snippets-file" :: v :: xs, r => parseOptions xs {r with snippetsFile := some ⟨v⟩}
  | "--expect-source" :: v :: xs, r => parseOptions xs {r with expectSource := some v}
  | "--limit" :: v :: xs, r => do parseOptions xs {r with limit := some (← positive v)}
  | "--timeout-ms" :: v :: xs, r => do parseOptions xs {r with timeoutMs := (← positive v)}
  | x :: xs, r =>
    if x.startsWith "-" then throw (invalid s!"unknown or incomplete option: {x}")
    else if r.operation == .search && r.query.isNone then parseOptions xs {r with query := some x}
    else if r.file.isNone then parseOptions xs {r with file := some ⟨x⟩}
    else throw (invalid "unexpected argument")

def parseArgs (args : List String) : Except CliError Request := do
  let (op, rest) ← match args with
    | [] => pure (Operation.help, [])
    | a :: xs => match Operation.parse a with
      | some o => pure (o, xs)
      | none => throw (invalid s!"unknown operation: {a}")
  let r ← parseOptions rest {operation := op}
  let needsFile := [Operation.goal, .diagnostics, .hover, .definition, .references, .codeActions, .attempt].contains op
  if needsFile != r.file.isSome then throw (invalid "invalid or missing file argument")
  if op == .search && r.query.isNone then throw (invalid "missing search query")
  if [Operation.goal, .hover, .definition, .references, .codeActions].contains op && r.line.isNone then throw (invalid "missing --line")
  if [Operation.hover, .definition, .references].contains op && r.column.isNone then throw (invalid "missing --column")
  if op == .attempt && (r.range.isNone || r.snippetsFile.isNone) then throw (invalid "attempt requires --range and --snippets-file")
  if r.line.isSome && ![Operation.goal, .hover, .definition, .references, .codeActions].contains op then throw (invalid "--line is not valid for this operation")
  if r.column.isSome && ![Operation.goal, .hover, .definition, .references, .codeActions].contains op then throw (invalid "--column is not valid for this operation")
  if r.range.isSome && op != .attempt then throw (invalid "--range is only valid for attempt")
  if r.snippetsFile.isSome && op != .attempt then throw (invalid "--snippets-file is only valid for attempt")
  if r.limit.isSome && op != .search then throw (invalid "--limit is only valid for search")
  if r.expectSource.isSome && !needsFile then throw (invalid "--expect-source requires a file")
  return r

def toLspPosition (map : FileMap) (p : PublicPosition) : Except CliError Lean.Lsp.Position := do
  if p.line == 0 || p.column == 0 then throw (invalid "positions are 1-based")
  let lines := map.source.splitOn "\n"
  let some line := lines[p.line - 1]? | throw (invalid "line out of range")
  if p.column - 1 > line.length then throw (invalid "column out of range")
  return map.leanPosToLspPos ⟨p.line, p.column - 1⟩

def validateRange (map : FileMap) (r : PublicRange) : Except CliError Lean.Lsp.Range := do
  let start ← toLspPosition map r.start
  let stop ← toLspPosition map r.end
  if r.start.line > r.end.line || (r.start.line == r.end.line && r.start.column > r.end.column) then throw (invalid "range is reversed")
  return ⟨start, stop⟩

private partial def findRoot (p : FilePath) : IO FilePath := do
  if (← (p / "lakefile.lean").pathExists) || (← (p / "lakefile.toml").pathExists) || (← (p / "lean-toolchain").pathExists) then return p
  match p.parent with
  | some parent => if parent == p then throw <| IO.userError "no Lake project found" else findRoot parent
  | none => throw <| IO.userError "no Lake project found"

def resolveProject (project : Option FilePath) : IO FilePath := do
  let p ← IO.FS.realPath (project.getD (← IO.currentDir))
  findRoot p

def resolveFile (root file : FilePath) : IO FilePath := do
  let path ← IO.FS.realPath (if file.isAbsolute then file else root / file)
  let rootPrefix := root.toString ++ "/"
  unless rootPrefix.isPrefixOf path.toString do throw <| IO.userError "file is outside project root"
  return path

def checkSourceIdentity (expected actual : Option String) : Except CliError Unit :=
  if expected.isSome && expected != actual then .error ⟨"stale_input", "source identity mismatch", 4⟩ else .ok ()
end LspCli
