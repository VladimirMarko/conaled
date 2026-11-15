import Applications.FRP.PendingMigration

/-! One-byte framing for the controlled in-process peer experiment. Business
frames report actual peer effects. A failed stdout write terminates the process;
it is not evidence about an independently recoverable external peer. -/
namespace FRPSpec.PendingMigration

def parse (b : UInt8) : Option Command := match b.toNat with
  | 48 => some (.accept false) | 49 => some (.accept true)
  | 101 => some .evaluate | 112 => some .publish
  | 121 => some (.retry false) | 122 => some (.retry true)
  | 107 => some .queryPeer | 100 => some (.dispatch true) | 120 => some (.dispatch false)
  | 116 => some .tickCommit | 99 => some .close | 108 => some .release
  | 78 => some (.cancelWork true) | 110 => some (.cancelWork false) | 114 => some (.prepare .redundant)
  | 97 => some (.prepare .delay) | 111 => some .ownershipCommit
  | 102 => some (.prepare .redundant 256 false true)
  | 118 => some (.prepare .redundant 256 true false)
  | 98 => some (.prepare .redundant 0) | 115 => some .cancelMigration
  | 113 => some .inspect | _ => none

def statusText : Status → String
  | .accepted => "accepted" | .evaluated => "evaluated" | .enqueued => "enqueued"
  | .dispatched => "dispatched" | .confirmed => "confirmed" | .committed => "committed"
  | .prevented => "prevented" | .tooLate => "too-late" | .closed => "closed"
  | .released => "released" | .prepared => "prepared" | .migrated => "migrated"
  | .cancelled => "cancelled" | .busy => "busy" | .full => "full"
  | .conflict => "conflict" | .refused => "refused" | .inspect => "inspect"
  | .allocationFailure => "allocation-failure" | .validationFailure => "validation-failure"
  | .resourceFailure => "resource-failure"

def queryText (s : Session) : String :=
  "C:q:" ++ Migration.kindText s.active.kind ++ ":" ++ Migration.bitText s.active.logical ++
    ":" ++ toString s.order.length ++ ":" ++ toString s.queue.messages.length ++ "\n"

/-- No runtime trace or growing command buffer. The peer remains owned by this
runner through backend transfers; the session learns only delivered replies. -/
def serve (k : Migration.Kind) (input output : IO.FS.Stream) : IO Unit := do
  let mut session := initial k
  repeat
    let bytes ← input.read 1
    if bytes.size == 0 then break
    let b := bytes[0]!
    if b == 10 then continue
    let some command := parse b | throw (.userError "invalid pending migration command byte")
    let next := step session command
    session := next.session
    if let some value := next.business then
      output.putStr ("B:" ++ Migration.bitText value ++ "\n")
    output.putStr (if next.status == .inspect then queryText session
      else "C:" ++ statusText next.status ++ "\n")
    output.flush

end FRPSpec.PendingMigration
