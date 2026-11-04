import LspCli.Transport
namespace LspCli
open System Std Lean
structure Stamp where
  modified : IO.FS.SystemTime
  size : UInt64
  deriving BEq
abbrev Snapshot := Std.HashMap String Stamp
namespace Watcher
private partial def walk (root path : FilePath) (deadline : Deadline)
    (seen : IO.Ref (Std.HashSet String)) (files : IO.Ref Snapshot) : IO Unit := do
  discard <| remaining deadline
  let canonical ← IO.FS.realPath path
  if (← seen.get).contains canonical.toString then return
  seen.modify (·.insert canonical.toString)
  for entry in ← path.readDir do
    discard <| remaining deadline
    if entry.fileName == ".git" then continue
    -- Entries may disappear after readDir, including dangling symlink targets.
    -- Other failures must abort the freshness barrier.
    let metadata ← try
      some <$> entry.path.metadata
    catch
      | .noFileOrDirectory .. => pure none
      | e => throw e
    let some metadata := metadata | continue
    if metadata.type == .dir then
      try walk root entry.path deadline seen files
      catch
        | .noFileOrDirectory .. => pure ()
        | e => throw e
    else if entry.path.extension == some "lean" || entry.path.extension == some "ilean" then
      files.modify (·.insert entry.path.toString ⟨metadata.modified, metadata.byteSize⟩)

def scan (root : FilePath) (deadline : Deadline) : IO Snapshot := do
  let seen ← IO.mkRef {}
  let files ← IO.mkRef {}
  walk root root deadline seen files
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
