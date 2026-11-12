import Applications.FRP.RegionalPendingPolicy
import Applications.FRP.PendingMigrationIO

/-! Public byte adapter for the bounded shared-dependency experiment. The peer
is owned by this process. A failed stdout write is fail-stop; write/flush is
neither atomic publication nor a crash recovery protocol. -/
namespace FRPSpec.Regional.Pending

def parse (s : Session) (b : UInt8) : Option Command := match b.toNat with
  | 48 => some (.accept false) | 49 => some (.accept true)
  | 101 => some .producer | 68 => some .deliverD | 78 => some .deliverN
  | 106 => some .join | 119 => some .whole
  | 114 => some (.prepare s.active.cut .split .redundant {} true true false)
  | 103 => some (.prepare s.active.cut .fused .delay {} true true false)
  | 104 => some (.prepare s.active.cut .checked .redundant {} true true false)
  | 111 => some .commit | 115 => some .cancel
  | 102 => some (.prepare s.active.cut .checked .redundant {} false true false)
  | 118 => some (.prepare s.active.cut .checked .redundant {} true false false)
  | 98 => some (.prepare s.active.cut .checked .redundant ⟨0,2,true,true⟩ true true false)
  | 87 => some (.prepare s.active.cut .fused .delay {} true true true)
  | 88 => some (.external (.cancelWork true))
  | _ => (PendingMigration.parse b).map Command.external

def statusText : Status → String
  | .protocol s => PendingMigration.statusText s
  | .produced => "produced" | .deliveredD => "delivered-D" | .deliveredN => "delivered-N"
  | .joined => "joined" | .completed => "completed" | .drained => "drained"
  | .prepared => "prepared" | .migrated => "migrated" | .cancelled => "cancelled"
  | .frozen => "frozen" | .throttled => "throttled" | .stale => "stale"
  | .capacity => "capacity" | .allocation => "allocation" | .validation => "validation"
  | .unsupported => "unsupported" | .busy => "busy"

def cutText : Cut → String | .split => "split" | .fused => "fused" | .checked => "checked"

def queryText (s : Session) : String :=
  "Q:" ++ cutText s.active.cut ++ ":" ++ Migration.kindText s.active.protocol.active.kind ++ ":" ++
  Migration.bitText s.active.protocol.active.logical ++ ":" ++ toString s.active.protocol.order.length ++ ":" ++
  toString s.active.protocol.queue.messages.length ++ ":" ++ toString s.active.deliveries.rank ++ ":" ++
  Migration.bitText s.prepared.isSome ++ "\n"

def serve (input output : IO.FS.Stream) : IO Unit := do
  let mut session := initial
  repeat
    let bytes ← input.read 1
    if bytes.size == 0 then break
    let b := bytes[0]!
    if b == 10 then continue
    if b == 113 then
      output.putStr (queryText session)
      output.flush
      continue
    let next ← if b == 80 then pure (propose session {} "public-pending") else do
      let some command := parse session b | throw (.userError "invalid regional pending command byte")
      pure (step session command)
    session := next.session
    if let some value := next.business then
      output.putStr ("B:" ++ Migration.bitText value ++ "\n")
    output.putStr ("C:" ++ statusText next.status ++ "\n")
    output.flush

end FRPSpec.Regional.Pending
