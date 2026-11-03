import LspCli.Protocol
import Lean.Data.Lsp.Communication
open Lean Lean.JsonRpc
namespace FakeServer

def run : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let mut queued : Option RequestID := none
  let mut events : Array Json := #[]
  let mut registered := false
  let mut buildModes : Array Json := #[]
  repeat
    match ← input.readLspMessage with
    | .request id method params =>
      let p := params.map toJson |>.getD Json.null
      if method == "initialize" then
        output.writeLspMessage (.response id (Json.mkObj [("capabilities", Json.mkObj [])]))
      else if method == "shutdown" then output.writeLspMessage (.response id Json.null)
      else if method == "test/reorder" then
        if let some old := queued then
          output.writeLspMessage (.response id (toJson "second"))
          output.writeLspMessage (.response old (toJson "first"))
          queued := none
        else queued := some id
      else if method == "test/late" then queued := some id
      else if method == "test/state" then
        if let some old := queued then output.writeLspMessage (.response old (toJson "late")); queued := none
        output.writeLspMessage (.response id (Json.mkObj [("registered", toJson registered), ("events", toJson events), ("buildModes", toJson buildModes)]))
      else if method == "$/lean/waitForILeans" then IO.sleep 2000
      else if method == "test/stderr" then
        (← IO.getStderr).putStr (String.ofList (List.replicate 65536 'x'))
        output.writeLspMessage (.response id Json.null)
      else if method == "test/partial" then
        let bytes := (toJson (JsonRpc.Message.response id (toJson "λ😀"))).compress.toUTF8
        output.putStr s!"Content-Length: {bytes.size}\r\n\r\n"
        output.flush
        output.write (bytes.extract 0 3)
        output.flush
        IO.sleep 10
        output.write (bytes.extract 3 bytes.size)
        output.flush
      else if method == "test/eof" then return 0
      else if method == "textDocument/waitForDiagnostics" then
        if ((p.getObjValAs? String "uri").toOption.getD "").endsWith "/Slow.lean" then IO.sleep 2000
        output.writeLspMessage (.response id (Json.mkObj []))
      else if method == "$/lean/plainGoal" then output.writeLspMessage (.response id Json.null)
      else output.writeLspMessage (.response id p)
    | .notification method params =>
      let p := params.map toJson |>.getD Json.null
      if method == "initialized" then
        output.writeLspRequest (⟨"watch", "client/registerCapability", Json.mkObj [("registrations", toJson #[Json.mkObj [("id", toJson "w"), ("method", toJson "workspace/didChangeWatchedFiles"), ("registerOptions", Json.mkObj [("watchers", toJson #[Json.mkObj [("globPattern", toJson "**/*.lean")], Json.mkObj [("globPattern", toJson "**/*.ilean")]])])]])]⟩ : JsonRpc.Request Json)
      else if method == "textDocument/didOpen" || method == "textDocument/didChange" then
        if method == "textDocument/didOpen" then
          buildModes := buildModes.push ((p.getObjVal? "dependencyBuildMode").toOption.getD Json.null)
        let td ← IO.ofExcept (p.getObjVal? "textDocument")
        let uri ← IO.ofExcept (td.getObjValAs? String "uri")
        let version ← IO.ofExcept (td.getObjValAs? Nat "version")
        let publish := fun (v : Nat) (incremental : Bool) (message : String) => output.writeLspNotification (⟨"textDocument/publishDiagnostics", Json.mkObj [("uri", toJson uri), ("version", toJson v), ("isIncremental", toJson incremental), ("diagnostics", toJson #[Json.mkObj [("range", toJson (⟨⟨0,0⟩,⟨0,1⟩⟩ : Lean.Lsp.Range)), ("severity", toJson (2 : Nat)), ("message", toJson message)]])]⟩ : Notification Json)
        publish version false "current"
        publish version true "increment"
        if version > 1 then publish (version - 1) false "old"
      else if method == "workspace/didChangeWatchedFiles" then
        events := events ++ (← IO.ofExcept (p.getObjValAs? (Array Json) "changes"))
      else if method == "exit" then return 0
    | .response id _ => if id == .str "watch" then registered := true
    | .responseError .. => pure ()
  return 0
end FakeServer
