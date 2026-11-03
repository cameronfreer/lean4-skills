import LspCli.Transport
import Std.Async.TCP
open Std Std.Async Lean
namespace LspCli.Socket

def acceptWithin (s : TCP.Socket.Server) (ms : Nat) : Async (Option TCP.Socket.Client) := do
  let timer ← Selector.sleep (.ofInt ms)
  Selectable.one #[.case s.acceptSelector (fun c => pure (some c)), .case timer (fun _ => pure none)]

def recvWithin (c : TCP.Socket.Client) (n : UInt64) (ms : Nat) : Async (Option (Option ByteArray)) := do
  let timer ← Selector.sleep (.ofInt ms)
  Selectable.one #[.case (c.recvSelector n) (fun b => pure (some b)), .case timer (fun _ => pure none)]

private partial def readExact (c : TCP.Socket.Client) (n deadline : Nat) (acc : ByteArray := ByteArray.empty) : Async ByteArray := do
  if acc.size == n then return acc
  let ms ← remaining deadline
  match ← recvWithin c (n - acc.size).toUInt64 ms with
  | none => throw (IO.userError "timeout: frame deadline")
  | some none => throw (IO.userError "protocol: truncated frame")
  | some (some b) =>
    if b.isEmpty then throw (IO.userError "protocol: empty receive")
    readExact c n deadline (acc ++ b)

def sendJson (c : TCP.Socket.Client) (j : Json) : Async Unit := do
  let body := j.compress.toUTF8
  if body.size > 1048576 then throw (IO.userError "protocol: frame too large")
  let n := body.size
  c.sendAll #[ByteArray.mk #[(n / 16777216).toUInt8, (n / 65536).toUInt8, (n / 256).toUInt8, n.toUInt8], body]

def readJson (c : TCP.Socket.Client) (deadline : Deadline) : Async Json := do
  let header ← readExact c 4 deadline
  let n := header.foldl (fun n b => n * 256 + b.toNat) 0
  if n > 1048576 then throw (IO.userError "protocol: frame too large")
  let body ← readExact c n deadline
  let some text := String.fromUTF8? body | throw (IO.userError "protocol: invalid UTF-8")
  IO.ofExcept (Json.parse text)

/-- UV connect/send have no selector cancellation. A caller abandons this single-use connection
    on expiry; it is never reused after a partial frame. The client process can then exit. -/
def bounded (action : Async Json) (deadline : Deadline) : IO Json := do
  let ch ← CloseableChannel.new
  discard <| IO.asTask (do
    let result ← try pure (.ok (← action.block)) catch e => pure (.error e)
    discard <| ch.send result) Task.Priority.dedicated
  try awaitReply ch deadline finally ch.close
end LspCli.Socket
