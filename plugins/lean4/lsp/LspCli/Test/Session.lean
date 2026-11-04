import LspCli.Session
import LspCli.Test.FakeServer
open Lean System LspCli
namespace SessionTests
private def check (label : String) (b : Bool) : IO Unit := do
  unless b do throw <| IO.userError s!"FAIL: {label}"
  IO.println s!"PASS: {label}"
private def deadline : IO Nat := return (← IO.monoMsNow) + 2000

def run : IO Unit := do
  let root ← IO.FS.createTempDir
  IO.FS.writeFile (root / "First.lean") "abc"
  let session ← Session.startWith root (← deadline) (← IO.appPath).toString #["--fake-server"]
  try
    let req := fun method params => do session.transport.request method params (← deadline)
    let one ← IO.asTask (req "test/reorder" Json.null) Task.Priority.dedicated
    IO.sleep 20
    let two ← req "test/reorder" Json.null
    check "out of order replies route to unique IDs" ((← IO.ofExcept one.get) == toJson "first" && two == toJson "second")
    let d ← session.openDocument (root / "First.lean") "abc"
    let diagnostics ← session.waitDocument d (← deadline)
    check "incremental diagnostics append" (diagnostics.size == 2)
    let aliased ← try discard <| session.openDocument d.path "changed" true; pure false catch _ => pure true
    check "virtual slot cannot alias live document" aliased
    let escaped ← try discard <| session.openDocument "/tmp/Outside.lean" "abc" true; pure false catch _ => pure true
    check "virtual document cannot escape project root" escaped
    let v ← session.openDocument (root / "Trial.lean") "abc" true
    discard <| session.waitDocument v (← deadline)
    let d ← session.openDocument d.path "abcd"
    let diagnostics ← session.waitDocument d (← deadline)
    check "version and URI isolation" (diagnostics.size == 2 && (diagnostics[0]!.getObjValAs? String "message").toOption == some "current" && d.version > 1)
    let v ← session.openDocument v.path "abcde" true
    check "identities differ across interleaved document edits" (d.identity != v.identity)
    session.closeDocument d.uri
    let reopened ← session.openDocument d.path d.text
    check "reopened URI never reuses wire version" (reopened.version > d.version && reopened.identity != d.identity)
    IO.FS.writeFile (root / "New.lean") "x"
    let expired ← try session.refresh (← IO.monoMsNow); pure false catch _ => pure true
    check "expired scan cannot commit freshness" (expired && !(← session.state.atomically get).snapshot.contains (root / "New.lean").toString)
    session.refresh (← deadline)
    IO.FS.writeFile (root / "New.lean") "xx"
    session.refresh (← deadline)
    IO.FS.removeFile (root / "New.lean")
    session.refresh (← deadline)
    IO.FS.writeFile (root / "New.ilean") "x"
    session.refresh (← deadline)
    IO.FS.writeFile (root / "New.ilean") "xx"
    session.refresh (← deadline)
    IO.FS.removeFile (root / "New.ilean")
    session.refresh (← deadline)
    let state ← req "test/state" Json.null
    let modes ← IO.ofExcept (state.getObjValAs? (Array Json) "buildModes")
    check "live and virtual documents never implicitly build dependencies" (!modes.isEmpty && modes.all (· == toJson "never"))
    let events ← IO.ofExcept (state.getObjValAs? (Array Json) "events")
    check "registration and create/change/delete forwarded" ((state.getObjValAs? Bool "registered").toOption == some true && events.map (fun e => (e.getObjValAs? Nat "type").toOption.getD 0) == #[1,2,3,1,2,3])
    let began ← IO.monoMsNow
    let timed ← try discard <| session.transport.request "test/late" Json.null (began + 30); pure false catch _ => pure true
    check "cancel deadline bounded" (timed && (← IO.monoMsNow) - began < 500)
    let state ← req "test/state" Json.null
    check "late reply cannot satisfy next request" ((state.getObjVal? "events").isOk)
    check "partial frames preserved" ((← req "test/partial" Json.null) == toJson "λ😀")
    discard <| req "test/stderr" Json.null
    IO.sleep 20
    let tail := (← session.transport.state.atomically get).stderrTail
    check "stderr drained and bounded" (!tail.isEmpty && tail.length ≤ 16384)
    let started ← IO.monoMsNow
    let search ← session.inspect {operation := .search, query := some "absent", timeoutMs := 30}
    check "blocked index deadline includes cleanup" (search.exitCode == 4 && (← IO.monoMsNow) - started < 300)
    check "incomplete search is explicit" ((search.data.getObjValAs? Bool "complete").toOption == some false)
    check "blocked watchdog session retired" (← session.state.atomically get <&> (·.retired))
  finally
    session.close
  let eofSession ← Session.startWith root (← deadline) (← IO.appPath).toString #["--fake-server"]
  try
    let failed ← try discard <| eofSession.transport.request "test/eof" Json.null (← deadline); pure false catch _ => pure true
    check "EOF resolves pending callers" failed
  finally
    eofSession.close
  let elaborating ← Session.startWith root (← deadline) (← IO.appPath).toString #["--fake-server"]
  try
    IO.FS.writeFile (root / "Slow.lean") "abc"
    let result ← elaborating.inspect {operation := .goal, file := some "Slow.lean", line := some 1, column := some 1, timeoutMs := 30}
    check "goal timeout distinguishes still elaborating" (result.exitCode == 4 && result.status == "still_elaborating")
  finally
    elaborating.close
    IO.FS.removeDirAll root
  IO.println "session tests passed"
end SessionTests
