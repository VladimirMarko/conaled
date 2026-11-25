import Examples.BoundedFoldReactive

open FRPSpec.BoundedFold Progress.Feedback

def bitText (b : Bool) : String := if b then "1" else "0"
def bitsText (xs : List Bool) := String.join (xs.map bitText)
def boolWords : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (boolWords n).flatMap (fun xs => [false::xs,true::xs])
def batches : List (Batch 3) :=
  ((List.range 4).flatMap boolWords).filterMap (ingest 3)
def batchSequences : Nat → List (List (Batch 3))
  | 0 => [[]]
  | n+1 => batches.flatMap (fun x => (batchSequences n).map (x :: ·))
def statusText : Status → String
  | .accepted => "accepted"
  | .rejected => "rejected"
  | .unsupported => "unsupported"
def answerText : Option (List Bool × Bool) → String
  | none => "none"
  | some (ys,s) => s!"{bitsText ys}:{bitText s}"

def main : IO Unit := do
  let f := run (machine 3).mealy false fixtures
  IO.println s!"fixture|{bitsText f.1}|{bitText f.2}"
  for seed in [false,true] do
    for n in List.range 4 do
      for xs in batchSequences n do
        let r := run (machine 3).mealy seed xs
        let first := run (machine 3).mealy seed (xs.take 1)
        let rest := run (machine 3).mealy first.2 (xs.drop 1)
        let continued := bitsText (first.1 ++ rest.1) ++ ":" ++ bitText rest.2
        let rr := run (Regional.machine 3).mealy (seed,true) xs
        let inputs := if xs.isEmpty then "-" else String.intercalate "," (xs.map (fun x => bitsText x.val))
        IO.println s!"run|{bitText seed}|{inputs}|{bitsText r.1}|{bitText r.2}|{continued}|{bitsText rr.1}"
  let ok := assess 3 true (.bounded (storage 3))
  let no := assess 3 true (.bounded (storage 3-1))
  let unknown := assess 3 false (.bounded (storage 3))
  IO.println s!"admission|{statusText ok.status}|{statusText no.status}|{statusText unknown.status}|{answerText (ok.run fixtures)}|{answerText (no.run fixtures)}"
  for c in List.range 4 do
    for n in List.range 5 do
      for xs in boolWords n do
        let result := match ingest c xs with
          | none => "reject"
          | some b => bitsText b.val
        IO.println s!"ingest|{c}|{bitsText xs}|{result}"
  let trace := (liveTrace 1 false [true]).map (· + 3) ++ Regional.consumerTrace
  IO.println s!"space|{storage 1}|{Regional.storage 1}|{trace.foldl max 0}"
