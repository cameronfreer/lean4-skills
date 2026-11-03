import LspCli.Protocol
open Lean System LspCli

def check (label : String) (b : Bool) : IO Unit :=
  unless b do throw <| IO.userError s!"FAIL: {label}"

def main (args : List String) : IO UInt32 := do
  check "unit flag" (args == ["--unit"])
  for argv in [["doctor", "--project", ".", "--json"], ["goal", "Foo.lean", "--line", "2", "--json"], ["diagnostics", "Foo.lean"], ["hover", "Foo.lean", "--line", "2", "--column", "3"], ["definition", "Foo.lean", "--line", "2", "--column", "3"], ["references", "Foo.lean", "--line", "2", "--column", "3"], ["code-actions", "Foo.lean", "--line", "2"], ["search", "add_zero", "--limit", "10"], ["attempt", "Foo.lean", "--range", "1:2-1:3", "--snippets-file", "x.json", "--expect-source", "abc", "--timeout-ms", "42"], ["status"], ["stop"]] do
    check s!"accepted {argv}" (parseArgs argv).isOk
  for argv in [["hover", "Foo.lean"], ["goal", "Foo.lean", "--line", "0"], ["attempt", "Foo.lean", "--range", "2:1-1:1", "--snippets-file", "x"], ["search"], ["bad"]] do
    check s!"rejected {argv}" (! (parseArgs argv).isOk)
  let response : Response := {ok := false, operation := "goal", status := "stale", error := some ⟨"stale_input", "mismatch", 4⟩}
  let decoded : Except String Response := fromJson? (toJson response)
  check "response JSON round trip" (decoded.toOption.map (·.status) == some "stale")
  check "position JSON round trip" ((fromJson? (toJson (⟨4, 7⟩ : PublicPosition)) : Except String PublicPosition).toOption == some ⟨4, 7⟩)
  check "unicode conversion" ((toLspPosition (FileMap.ofString "a😀b\n") ⟨1, 3⟩).toOption == some ⟨0, 3⟩)
  check "end of line allowed" ((toLspPosition (FileMap.ofString "a") ⟨1, 2⟩).isOk)
  check "out of bounds" (!(toLspPosition (FileMap.ofString "a") ⟨1, 3⟩).isOk)
  check "empty trailing line" ((toLspPosition (FileMap.ofString "a\n") ⟨2, 1⟩).toOption == some ⟨1, 0⟩)
  check "exclusive range preserved" ((validateRange (FileMap.ofString "a😀b") ⟨⟨1, 2⟩, ⟨1, 3⟩⟩).toOption == some ⟨⟨0, 1⟩, ⟨0, 3⟩⟩)
  check "source identity mismatch" (!(checkSourceIdentity (some "old") (some "new")).isOk)
  check "source identity match" ((checkSourceIdentity (some "same") (some "same")).isOk)
  let request : Request := {operation := .hover, file := some "x.lean", line := some 1, column := some 2}
  let roundTrip : Except String Request := fromJson? (toJson request)
  check "request JSON round trip" (roundTrip.toOption.bind (·.line) == some 1)
  let tmp ← IO.FS.createTempDir
  let noRoot ← try let _ ← resolveProject (some tmp); pure false catch _ => pure true
  check "missing Lake root" noRoot
  let spaced := tmp / "project with spaces"
  IO.FS.createDir spaced
  IO.FS.writeFile (spaced / "lakefile.toml") "name = 'test'"
  IO.FS.writeFile (spaced / "Test.lean") "example : True := trivial"
  let link := tmp / "project link"
  let ln ← IO.Process.output {cmd := "ln", args := #["-s", spaced.toString, link.toString]}
  check "symlink setup" (ln.exitCode == 0)
  let canonical ← resolveProject (some link)
  check "space and symlink canonicalized" (canonical == (← IO.FS.realPath spaced))
  let target ← resolveFile canonical "Test.lean"
  check "spaced path file" (target == (← IO.FS.realPath (spaced / "Test.lean")))
  let escaping := spaced / "escape"
  let ln ← IO.Process.output {cmd := "ln", args := #["-s", "/etc/passwd", escaping.toString]}
  check "escape setup" (ln.exitCode == 0)
  let escaped ← try let _ ← resolveFile canonical "escape"; pure false catch _ => pure true
  check "symlink escape rejected" escaped
  IO.FS.removeDirAll tmp
  let root ← resolveProject none
  check "project discovery" ((root / "lakefile.lean").toString.endsWith "lakefile.lean")
  let file ← resolveFile root "Main.lean"
  check "relative path" (file.toString.endsWith "/Main.lean")
  let outside ← try let _ ← resolveFile root "/etc/passwd"; pure false catch _ => pure true
  check "outside root rejected" outside
  let exe := root / ".lake/build/bin/lean4-skills-lsp"
  let out ← IO.Process.output {cmd := exe.toString, args := #["hover", "--json"]}
  check "invalid exit code" (out.exitCode == 2)
  check "one JSON record" ((Json.parse out.stdout.trimAscii.copy).isOk && (out.stdout.splitOn "\n").length == 2)
  let out ← IO.Process.output {cmd := exe.toString, args := #["status", "--project", root.toString, "--json"]}
  check "unavailable exit code" (out.exitCode == 3)
  let out ← IO.Process.output {cmd := exe.toString, args := #["--help", "--json"]}
  check "help exit code" (out.exitCode == 0)
  IO.println "unit tests passed"
  return 0
