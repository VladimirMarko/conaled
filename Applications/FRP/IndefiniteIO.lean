import Applications.FRP.Indefinite

/-! A synchronous byte-stream adapter. Every admitted byte is consumed before one
output is written and flushed. Stream implementations, host allocation and IO
completion are trusted; the circuit theorems do not prove physical heap bounds. -/
namespace FRPSpec.Indefinite

/-- ASCII 0 and 1 only. An invalid byte or IO error stops the session by throwing;
previous outputs are not rolled back. EOF ends the supplied finite session.
There is no lifetime step counter and no collection of earlier inputs/outputs. -/
def serve (p : Program .base .base s) (input output : IO.FS.Stream) : IO Unit := do
  let mut state := p.initial
  repeat
    let bytes ← input.read 1
    if bytes.size == 0 then break
    let byte := bytes[0]!
    if byte != 48 && byte != 49 then
      throw (.userError "expected ASCII 0 or 1")
    let next := p.machine.step (byte == 49,state)
    output.write (ByteArray.mk #[if next.1 then 49 else 48])
    output.flush
    state := next.2

end FRPSpec.Indefinite
