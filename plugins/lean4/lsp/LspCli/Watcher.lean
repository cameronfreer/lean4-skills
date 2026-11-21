import LspCli.Transport
namespace LspCli
open System Std Lean
structure Stamp where
  modified : IO.FS.SystemTime
  size : UInt64
  deriving BEq
abbrev Snapshot := Std.HashMap String Stamp
namespace Watcher
private partial def walk (path : FilePath) (indicesOnly : Bool) (deadline : Deadline)
    (seen : IO.Ref (Std.HashSet String)) (files : IO.Ref Snapshot) : IO Unit := do
  discard <| remaining deadline
  let canonical ← IO.FS.realPath path
  if (← seen.get).contains canonical.toString then return
  seen.modify (·.insert canonical.toString)
  for entry in ← path.readDir do
    discard <| remaining deadline
    if entry.fileName == ".git" || entry.fileName == ".lake" then continue
    -- Entries may disappear after readDir, including dangling symlink targets.
    -- Other failures must abort the freshness barrier.
    let metadata ← try
      some <$> entry.path.metadata
    catch
      | .noFileOrDirectory .. => pure none
      | e => throw e
    let some metadata := metadata | continue
    if metadata.type == .dir then
      try walk entry.path indicesOnly deadline seen files
      catch
        | .noFileOrDirectory .. => pure ()
        | e => throw e
    else if entry.path.extension == some "ilean" ||
        (!indicesOnly && entry.path.extension == some "lean") then
      files.modify (·.insert entry.path.toString ⟨metadata.modified, metadata.byteSize⟩)

private def scanBuild (path : FilePath) (deadline : Deadline)
    (seen : IO.Ref (Std.HashSet String)) (files : IO.Ref Snapshot) : IO Unit := do
  discard <| remaining deadline
  try
    if (← path.metadata).type == .dir then
      walk path true deadline seen files
  catch
    | .noFileOrDirectory .. => pure ()
    | e => throw e

/-- Watch project .lean/.ilean files, excluding .git and .lake subtrees; additionally watch only
.ilean files in root/.lake/build and root/.lake/packages/*/.lake/build (with the same exclusions).
Dependency sources are excluded: dependencyBuildMode=never makes rebuilt indices the server's signal. -/
def scan (root : FilePath) (deadline : Deadline) : IO Snapshot := do
  let seen ← IO.mkRef {}
  let files ← IO.mkRef {}
  walk root false deadline seen files
  scanBuild (root / ".lake" / "build") deadline seen files
  discard <| remaining deadline
  let packages ← try
    (root / ".lake" / "packages").readDir
  catch
    | .noFileOrDirectory .. => pure #[]
    | e => throw e
  for entry in packages do
    discard <| remaining deadline
    try
      if (← entry.path.metadata).type == .dir then
        scanBuild (entry.path / ".lake" / "build") deadline seen files
    catch
      | .noFileOrDirectory .. => pure ()
      | e => throw e
  discard <| remaining deadline
  files.get

def changes (before after : Snapshot) : Array Lean.Lsp.FileEvent := Id.run do
  let mut events := #[]
  for (path, stamp) in after.toArray do
    let kind := match before[path]? with
      | none => some Lean.Lsp.FileChangeType.Created
      | some old => if old != stamp then some .Changed else none
    if let some type := kind then events := events.push {uri := System.Uri.pathToUri path, type}
  for (path, _) in before.toArray do
    unless after.contains path do events := events.push {uri := System.Uri.pathToUri path, type := .Deleted}
  return events
end Watcher
end LspCli
