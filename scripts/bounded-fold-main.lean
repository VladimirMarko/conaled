import Examples.BoundedFoldReactive

open FRPSpec.BoundedFold Progress.Feedback

def bit (b : Bool) : String := if b then "1" else "0"
def bits (xs : List Bool) := String.join (xs.map bit)
def boolWords : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (boolWords n).flatMap (fun xs => [false::xs,true::xs])
def batches : List (Batch 3) :=
  ((List.range 4).flatMap boolWords).filterMap (ingest 3)
def words : Nat → List (List (Batch 3))
  | 0 => [[]]
  | n+1 => batches.flatMap (fun x => (words n).map (x :: ·))
def status : Status → String
  | .accepted => "accepted"
  | .rejected => "rejected"
  | .unsupported => "unsupported"
def answer : Option (List Bool × Bool) → String
  | none => "none"
  | some (ys,s) => s!"{bits ys}:{bit s}"

def main : IO Unit := do
  let f := run (machine 3).mealy false fixtures
  IO.println s!"fixture|{bits f.1}|{bit f.2}"
  for seed in [false,true] do
    for n in List.range 4 do
      for xs in words n do
        let r := run (machine 3).mealy seed xs
        let first := run (machine 3).mealy seed (xs.take 1)
        let rest := run (machine 3).mealy first.2 (xs.drop 1)
        let continued := bits (first.1 ++ rest.1) ++ ":" ++ bit rest.2
        let rr := run (Regional.machine 3).mealy (seed,true) xs
        let inputs := if xs.isEmpty then "-" else String.intercalate "," (xs.map (fun x => bits x.val))
        IO.println s!"run|{bit seed}|{inputs}|{bits r.1}|{bit r.2}|{continued}|{bits rr.1}"
  let ok := assess 3 true (.bounded (storage 3))
  let no := assess 3 true (.bounded (storage 3-1))
  let unknown := assess 3 false (.bounded (storage 3))
  IO.println s!"admission|{status ok.status}|{status no.status}|{status unknown.status}|{answer (ok.run fixtures)}|{answer (no.run fixtures)}"
  for c in List.range 4 do
    for n in List.range 5 do
      for xs in boolWords n do
        let result := match ingest c xs with
          | none => "reject"
          | some b => bits b.val
        IO.println s!"ingest|{c}|{bits xs}|{result}"
  let trace := (liveTrace 1 false [true]).map (· + 3) ++ Regional.consumerTrace
  IO.println s!"space|{storage 1}|{Regional.storage 1}|{trace.foldl max 0}"
