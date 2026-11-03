import LspCli.Protocol
open Lean System
namespace LspCli.Positions

def fromLsp (text : String) (p : Lean.Lsp.Position) : Except String PublicPosition := do
  let some line := (text.splitOn "\n")[p.line]? | throw "server returned an out-of-range line"
  let column := line.utf16PosToCodepointPos p.character
  unless line.codepointPosToUtf16Pos column == p.character do throw "server returned an invalid UTF-16 boundary"
  if column > line.length then throw "server returned an out-of-range column"
  return ⟨p.line + 1, column + 1⟩

/-- Convert public output recursively, including workspace edit URI maps, without touching opaque data.
    The retained snapshot resolver must take priority over disk reads for open documents. -/
partial def convert (load : String → IO String) (uri : String) (value : Json) : IO Json := do
  match value with
  | .arr xs => return toJson (← xs.mapM (convert load uri))
  | .obj fields =>
    if (value.getObjVal? "start").isOk && (value.getObjVal? "end").isOk then
      let range : Lean.Lsp.Range ← IO.ofExcept (fromJson? value)
      let text ← load uri
      return toJson ({start := ← IO.ofExcept (fromLsp text range.start), «end» := ← IO.ofExcept (fromLsp text range.end)} : PublicRange)
    let localUri := (value.getObjValAs? String "uri").toOption.getD
      (((value.getObjVal? "textDocument").bind (·.getObjValAs? String "uri")).toOption.getD uri)
    let targetUri := (value.getObjValAs? String "targetUri").toOption.getD localUri
    let fields ← fields.toArray.mapM fun (key, child) => do
      if key == "data" then return (key, child)
      let childUri := if key == "targetRange" || key == "targetSelectionRange" then targetUri
        else if key.startsWith "file://" then key else localUri
      return (key, ← convert load childUri child)
    return Json.mkObj fields.toList
  | _ => return value
end LspCli.Positions
