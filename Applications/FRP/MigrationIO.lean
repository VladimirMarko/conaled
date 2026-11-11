import Applications.FRP.Migration

/-! Bounded byte-command adapter. Local write/flush acceptance is the publication
boundary. Exceptions terminate the session without replay or recovery. -/
namespace FRPSpec.Migration

def parse (byte : UInt8) : Option Command :=
  match byte.toNat with
  | 48 => some (.accept false) | 49 => some (.accept true)
  | 101 => some (.evaluate none) | 112 => some (.sink true) | 119 => some (.sink false)
  | 116 => some .tickCommit | 100 => some (.request .delay) | 114 => some (.request .redundant)
  | 109 => some (.prepare 128 true true) | 98 => some (.prepare 0 true true)
  | 102 => some (.prepare 128 false true) | 118 => some (.prepare 128 true false)
  | 99 => some .cancel | 111 => some .ownershipCommit | 113 => some .query
  | 117 => some (.evaluate (some .delay)) | 106 => some (.evaluate (some .redundant))
  | 122 => some .unsupported | _ => none

def statusText : Status → String
  | .accepted => "accepted" | .evaluated => "evaluated" | .published => "published"
  | .tickCommitted => "tick-committed" | .requested => "requested" | .prepared => "prepared"
  | .migrated => "migrated" | .cancelled => "cancelled" | .query => "query"
  | .busy => "busy" | .refused => "refused" | .wrongOwner => "wrong-owner"
  | .sameBackend => "same-backend" | .unsupported => "unsupported"
  | .resourceFailure => "resource-failure" | .allocationFailure => "allocation-failure"
  | .validationFailure => "validation-failure" | .idle => "idle"

def kindText : Kind → String | .delay => "d" | .redundant => "r"
def bitText (b : Bool) : String := if b then "1" else "0"
def phaseText {b : Backend} : Flight b → String
  | .idle => "idle" | .accepted _ => "accepted"
  | .pending _ _ => "pending" | .published _ _ => "published"

def queryText (s : Session) : String :=
  "C:q:" ++ kindText s.active.kind ++ ":" ++ bitText s.active.logical ++ ":" ++
  phaseText s.flight ++ ":" ++ (s.last.map bitText).getD "-" ++ ":" ++
  (s.request.map kindText).getD "-" ++ ":" ++ (if s.prepared.isSome then "1" else "0") ++ "\n"

/-- One byte is the entire command frame, including malformed input. No line or
lifetime history is accumulated. Sink refusal is a control command, not OS write interruption. -/
def serve (kind : Kind) (input output : IO.FS.Stream) : IO Unit := do
  let mut session := initial kind
  repeat
    let bytes ← input.read 1
    if bytes.size == 0 then break
    let byte := bytes[0]!
    if byte == 10 then continue
    let some command := parse byte | throw (.userError "invalid migration command byte")
    let next := step session command
    if let some value := next.business then
      output.putStr ("B:" ++ bitText value ++ "\n")
      output.flush
    -- Expose successful pure publication only after the business write and flush.
    session := next.session
    output.putStr (if next.status == .query then queryText session
      else "C:" ++ statusText next.status ++ "\n")
    output.flush

end FRPSpec.Migration
