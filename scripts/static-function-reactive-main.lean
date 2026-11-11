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

def main : IO Unit := do
  let configs : List (String × List StaticBody) :=
    [("neg",[negationBody]),("identity",[identityBody]),("mask",[maskBody true]),
     ("nested",[negationBody,negationBody]),("empty",[])]
  for (name,bodies) in configs do
    let compiled := program bodies (false,true)
    for initial in (List.range 4).map pairOf do
      for n in List.range 5 do
        for word in words n do
          let xs := word.map pairOf
          let r := run compiled.machine.mealy initial xs
          let firstRun := run compiled.machine.mealy initial (xs.take 2)
          let suffix := run compiled.machine.mealy firstRun.2 (xs.drop 2)
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
