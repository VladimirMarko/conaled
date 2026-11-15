import Examples.StaticFunctionReactive

open FRPSpec.StaticFunctionReactive StaticFunction Progress.Feedback

def bit (b : Bool) : String := if b then "1" else "0"
def pairText (p : Pair) : String := bit p.1 ++ bit p.2
def pairOf (n : Nat) : Pair := (n / 2 == 1,n % 2 == 1)
def words : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (List.range 4).flatMap (fun i => (words n).map (i :: ·))
def status : Status → String
  | .accepted => "accepted"
  | .rejectedCapacity => "capacity"
  | .unsupported => "unsupported"

def requireRun (selection : Admission capacity) (current : Option Pair) (inputs : List Pair) :
    IO (List Pair × Pair) :=
  match selection.execute current inputs with
  | some result => pure result
  | none => throw (IO.userError "expected selected executor")

def main : IO Unit := do
  let configs : List (String × List StaticBody) :=
    [("neg",[negationBody]),("identity",[identityBody]),("mask",[maskBody true]),
     ("nested",[negationBody,negationBody]),("empty",[])]
  for (name,bodies) in configs do
    let compiled := program bodies (false,true)
    let selection := assess (.static bodies (false,true)) (2 + compiled.body.arena)
    let seeded ← requireRun selection none [(false,false)]
    IO.println s!"seeded|{name}|{String.intercalate "," (seeded.1.map pairText)}|{pairText seeded.2}"
    for initial in (List.range 4).map pairOf do
      for n in List.range 5 do
        for word in words n do
          let xs := word.map pairOf
          let r ← requireRun selection (some initial) xs
          let firstRun ← requireRun selection (some initial) (xs.take 2)
          let suffix ← requireRun selection (some firstRun.2) (xs.drop 2)
          if (firstRun.1 ++ suffix.1,suffix.2) != r then throw (IO.userError "restart mismatch")
          IO.println s!"run|{name}|{pairText initial}|{String.join (word.map toString)}|{String.intercalate "," (r.1.map pairText)}|{pairText r.2}"
    IO.println s!"cost|{name}|{(measured (stagedBody bodies)).2}|{nodes (measured (stagedBody bodies)).1}|{compiled.body.work}|{compiled.body.arena}"
  for n in List.range 8 do
    let r := measured (duplication (P := Applications.Circuits.Gate) n)
    IO.println s!"duplication|{n}|{r.2}|{nodes r.1}"
  let regional := regionalMachine [negationBody] (false,true)
  for x in [false,true] do
    for y in [false,true] do
      let r := regional.step (.inr (x,y),(true,false))
      IO.println s!"regional|{bit x}{bit y}|{pairText r.1}|{pairText r.2}"
  let p := program [negationBody] (false,true)
  let capacity := 2 + p.body.arena
  IO.println s!"admission|{status (assess (.static [negationBody] (false,true)) capacity).status}|{status (assess (.static [negationBody] (false,true)) 0).status}|{status (assess (.dynamicFunction Bool.not) capacity).status}|{status (assess (.escapingEnvironment true Bool.xor) capacity).status}|{status (assess .opaqueNative capacity).status}"
  for selection in [assess (.static [negationBody] (false,true)) 0,
      assess (.dynamicFunction Bool.not) 0, assess (.escapingEnvironment true Bool.xor) 0,
      assess .opaqueNative 0] do
    let answer := selection.execute (some (true,false)) [(false,false),(true,true)]
    if answer.isSome then throw (IO.userError "negative admission executed")
    IO.println s!"nonexecution|{status selection.status}|none"
