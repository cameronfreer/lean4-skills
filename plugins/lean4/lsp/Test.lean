import LspCli.Doctor
import LspCli.TestIntegration
import LspCli.Test.Session
open Lean System LspCli

def check (label : String) (b : Bool) : IO Unit :=
  unless b do throw <| IO.userError s!"FAIL: {label}"

def main (args : List String) : IO UInt32 := do
  if args == ["--fake-server"] then return ← FakeServer.run
  if let ["--mathlib", root] := args then
    Integration.mathlib root
    return 0
  if args == ["--session"] then
    SessionTests.run
    return 0
  if args == ["env", "lean", "--version"] then return 0
  if args == ["serve", "--"] then
    if ← (System.FilePath.mk "hang").pathExists then IO.sleep 3000
    return 1
  if let ["--regression", focus, "--server-toolchain", toolchain] := args then
    Integration.regressions toolchain focus
    return 0
  if args.head? == some "--integration" then
    Integration.run (args[2]?.getD "leanprover/lean4:v4.35.0")
    return 0
  check "unit flag" (args == ["--unit"])
  for argv in [["doctor", "--project", ".", "--json"], ["goal", "Foo.lean", "--line", "2", "--json"], ["diagnostics", "Foo.lean"], ["hover", "Foo.lean", "--line", "2", "--column", "3"], ["definition", "Foo.lean", "--line", "2", "--column", "3"], ["references", "Foo.lean", "--line", "2", "--column", "3"], ["code-actions", "Foo.lean", "--line", "2"], ["search", "add_zero", "--limit", "10"], ["attempt", "Foo.lean", "--range", "1:2-1:3", "--snippets-file", "x.json", "--expect-source", "abc", "--timeout-ms", "42"], ["status"], ["stop"]] do
    check s!"accepted {argv}" (parseArgs argv).isOk
  for argv in [["hover", "Foo.lean"], ["goal", "Foo.lean", "--line", "0"], ["attempt", "Foo.lean", "--range", "2:1-1:1", "--snippets-file", "x"], ["search"], ["bad"]] do
    check s!"rejected {argv}" (! (parseArgs argv).isOk)
  let response : Response := {ok := false, operation := "goal", projectRoot := some "/project", file := some "/project/a.lean", documentVersion := some 8, sourceIdentity := some "nonce", status := "stale", error := some ⟨"stale_input", "mismatch", 4⟩}
  let decoded : Except String Response := fromJson? (toJson response)
  let some decoded := decoded.toOption | throw <| IO.userError "response JSON decode failed"
  check "response JSON round trip" (decoded.schema == "lean4-lsp/v1" && decoded.operation == "goal" && decoded.status == "stale" && decoded.projectRoot == some "/project" && decoded.file == some "/project/a.lean" && decoded.documentVersion == some 8 && decoded.sourceIdentity == some "nonce" && decoded.error.map CliError.exitCode == some 4 && decoded.error.map CliError.code == some "stale_input")
  check "position JSON round trip" ((fromJson? (toJson (⟨4, 7⟩ : PublicPosition)) : Except String PublicPosition).toOption == some ⟨4, 7⟩)
  check "unicode conversion" ((toLspPosition (FileMap.ofString "a😀b\n") ⟨1, 3⟩).toOption == some ⟨0, 3⟩)
  check "end of line allowed" ((toLspPosition (FileMap.ofString "a") ⟨1, 2⟩).isOk)
  check "out of bounds" (!(toLspPosition (FileMap.ofString "a") ⟨1, 3⟩).isOk)
  check "empty trailing line" ((toLspPosition (FileMap.ofString "a\n") ⟨2, 1⟩).toOption == some ⟨1, 0⟩)
  check "exclusive range preserved" ((validateRange (FileMap.ofString "a😀b") ⟨⟨1, 2⟩, ⟨1, 3⟩⟩).toOption == some ⟨⟨0, 1⟩, ⟨0, 3⟩⟩)
  let .error stale := checkSourceIdentity (some "old") (some "new") | throw <| IO.userError "mismatch accepted"
  check "source identity mismatch error" (stale.code == "stale_input" && stale.exitCode == 4)
  for n in [0, 1, 2, 3, 4] do
    let response : Response := {ok := n == 0, operation := "test", status := "test", error := if n == 0 then none else some ⟨"test", "test", n⟩}
    check s!"response exit {n}" (response.exitCode == n.toUInt32)
  check "source identity match" ((checkSourceIdentity (some "same") (some "same")).isOk)
  let request : Request := {operation := .attempt, file := some "x.lean", range := some ⟨⟨1, 2⟩, ⟨3, 4⟩⟩, expectSource := some "identity"}
  let roundTrip : Except String Request := fromJson? (toJson request)
  let some request := roundTrip.toOption | throw <| IO.userError "request JSON decode failed"
  check "request JSON round trip" (request.operation == .attempt && request.expectSource == some "identity" && request.range == some ⟨⟨1, 2⟩, ⟨3, 4⟩⟩)
  let tmp ← IO.FS.createTempDir
  let noRoot ← try let _ ← resolveProject (some tmp); pure false catch _ => pure true
  check "missing Lake root" noRoot
  let self ← IO.appPath
  let unavailable ← probeProject tmp 1000 self.toString
  check "toolchain available but server fails" (unavailable.toolchainAvailable && !unavailable.serverAvailable && !unavailable.timedOut)
  IO.FS.writeFile (tmp / "hang") ""
  let start ← IO.monoMsNow
  let timed ← probeProject tmp 100 self.toString
  check "server probe timeout bounded" (timed.toolchainAvailable && !timed.serverAvailable && timed.timedOut && (← IO.monoMsNow) - start < 1500)
  IO.FS.removeFile (tmp / "hang")
  let spaced := tmp / "project with spaces"
  IO.FS.createDir spaced
  IO.FS.writeFile (spaced / "lakefile.toml") "name = 'test'"
  IO.FS.writeFile (spaced / "Test.lean") "example : True := trivial"
  let link := tmp / "project link"
  let ln ← IO.Process.output {cmd := "ln", args := #["-s", spaced.toString, link.toString]}
  check "symlink setup" (ln.exitCode == 0)
  let canonical ← resolveProject (some link)
  check "space and symlink canonicalized" (canonical == (← IO.FS.realPath spaced))
  let fakeLake := tmp / "lake"
  let ln ← IO.Process.output {cmd := "ln", args := #["-s", self.toString, fakeLake.toString]}
  check "fake lake setup" (ln.exitCode == 0)
  let cwd ← IO.currentDir
  let exe := cwd / ".lake/build/bin/lean4-skills-lsp"
  let broken ← IO.Process.output {cmd := exe.toString, args := #["doctor", "--project", spaced.toString, "--json"], env := #[("PATH", some tmp.toString)]}
  let json ← IO.ofExcept (Json.parse broken.stdout.trimAscii.copy)
  let data ← IO.ofExcept (json.getObjVal? "data")
  check "doctor distinguishes failed server" (broken.exitCode == 3 && (data.getObjValAs? Bool "projectToolchainAvailable").toOption == some true && (data.getObjValAs? Bool "projectServerAvailable").toOption == some false)
  let target ← resolveFile canonical "Test.lean"
  check "spaced path file" (target == (← IO.FS.realPath (spaced / "Test.lean")))
  let escaping := spaced / "escape"
  let ln ← IO.Process.output {cmd := "ln", args := #["-s", "/etc/passwd", escaping.toString]}
  check "escape setup" (ln.exitCode == 0)
  let escaped ← try let _ ← resolveFile canonical "escape"; pure false catch _ => pure true
  check "symlink escape rejected" escaped
  let nested := spaced / "one" / "two"
  IO.FS.createDirAll nested
  check "nested project discovery" ((← resolveProject (some nested)) == canonical)
  IO.FS.removeDirAll tmp
  let root ← resolveProject none
  let file ← resolveFile root "Main.lean"
  check "relative path" (file.toString.endsWith "/Main.lean")
  let outside ← try let _ ← resolveFile root "/etc/passwd"; pure false catch _ => pure true
  check "outside root rejected" outside
  let exe := root / ".lake/build/bin/lean4-skills-lsp"
  let out ← IO.Process.output {cmd := exe.toString, args := #["hover", "--json"]}
  check "invalid exit code" (out.exitCode == 2)
  check "one JSON record" ((Json.parse out.stdout.trimAscii.copy).isOk && (out.stdout.splitOn "\n").length == 2)
  let out ← IO.Process.output {cmd := exe.toString, args := #["status", "--project", root.toString, "--json"]}
  check "inactive status exit code" (out.exitCode == 0)
  let doctor ← IO.Process.output {cmd := exe.toString, args := #["doctor", "--project", root.toString, "--json", "--timeout-ms", "10000"]}
  let doc ← IO.ofExcept (Json.parse doctor.stdout.trimAscii.copy)
  let available := (doc.getObjVal? "data").bind (·.getObjValAs? Bool "projectServerAvailable")
  check "doctor confirms real project server" (doctor.exitCode == 0 && available.toOption == some true)
  let out ← IO.Process.output {cmd := exe.toString, args := #["--help", "--json"]}
  check "help exit code" (out.exitCode == 0)
  IO.println "unit tests passed"
  return 0
