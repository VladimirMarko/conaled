import Applications.FRP.RegionalMigrationResources

/-! One-byte public control adapter. Successful business write/flush is exposed
before installing the new local state. Any IO exception aborts without recovery;
a partial external write remains ambiguous, not an atomic modeled tick. -/
namespace FRPSpec.Regional.Reconfiguration
open Selection

def both (c : Cut) : Sites := ⟨c,c⟩
def roomy : Requirements := ⟨10000,1,true,true⟩
def fixtureA : Input × Input := (.inl true,.inl false)
def fixtureB : Input × Input := (.inr (false,true),.inr (true,false))
def fixtureC : Input × Input := (.inl false,.inl true)

def statusText : Status → String
  | .ticked => "ticked" | .prepared => "prepared" | .committed => "committed"
  | .cancelled => "cancelled" | .throttled => "throttled" | .frozen => "frozen"
  | .stale => "stale" | .capacity => "capacity" | .allocation => "allocation"
  | .validation => "validation" | .unsupported => "unsupported" | .idle => "idle"
  | .noCandidate => "no-candidate"
def bit (b : Bool) : String := if b then "1" else "0"
def pairText (p : Bool × Bool) := bit p.1 ++ bit p.2

def command (s : Session) (byte : UInt8) : Option Outcome :=
  match byte.toNat with
  | 97 => some (tick s fixtureA)
  | 98 => some (tick s fixtureB)
  | 99 => some (tick s fixtureC)
  | 115 => some (prepare s s.active.sites (both .split) roomy true true)
  | 103 => some (prepare s s.active.sites (both .fused) roomy true true)
  | 104 => some (prepare s s.active.sites (both .checked) roomy true true)
  | 109 => some (commit s)
  | 120 => some (cancel s)
  | 122 => some (prepare s s.active.sites (both .split) ⟨(both .split).plan.storage,1,true,true⟩ true true)
  | 102 => some (prepare s s.active.sites (both .split) roomy false true)
  | 118 => some (prepare s s.active.sites (both .split) roomy true false)
  | 106 => some (prepare s (both .checked) (both .split) roomy true true)
  | 112 => some (propose s roomy "public-quiescent" none [both .split,both .checked])
  | 117 => some (refuse s .unsupported)
  | _ => none

def serve (input output : IO.FS.Stream) : IO Unit := do
  let mut session := initial (both .fused)
  repeat
    let bytes ← input.read 1
    if bytes.size == 0 then break
    let b := bytes[0]!
    if b == 10 then continue
    if b == 113 then
      output.putStr ("Q:" ++ pairText (observation session.active) ++ ":" ++
        session.active.sites.name ++ ":" ++ bit session.prepared.isSome ++ ":" ++
        bit session.permitted ++ "\n")
      output.flush
      continue
    let some next := command session b | throw (.userError "invalid regional migration byte")
    if let some value := next.output then
      output.putStr ("B:" ++ pairText value ++ "\n")
      output.flush
    session := next.session
    output.putStr ("C:" ++ statusText next.status ++ "\n")
    output.flush

end FRPSpec.Regional.Reconfiguration
