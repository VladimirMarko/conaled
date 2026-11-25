import Examples.RegionalPlans

open FRPSpec.Regional Progress.Feedback

def bitText (b : Bool) : String := if b then "1" else "0"
def inputFromCode : Nat → Input
  | 0 => .inl false
  | 1 => .inl true
  | 2 => .inr (false,false)
  | 3 => .inr (false,true)
  | 4 => .inr (true,false)
  | _ => .inr (true,true)
def inputCodeSequences : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (List.range 6).flatMap (fun i => (inputCodeSequences n).map (i :: ·))
def statusText : Status → String
  | .accepted => "accepted"
  | .rejected => "rejected"
  | .unsupported => "unsupported"

def main : IO Unit := do
  for c in [Cut.fused,Cut.split,Cut.checked] do
    for seed in [false,true] do
      for n in List.range 5 do
        for word in inputCodeSequences n do
          let r := run (compile c).machine.mealy (resumeState c seed) (word.map inputFromCode)
          IO.println s!"run|{repr c}|{bitText seed}|{String.join (word.map toString)}|{String.join (r.1.map bitText)}|{bitText (logical c r.2)}"
    let s := resumeState c true
    let queried := command c s .query
    let afterQuery := command c queried.2 (.tick (.inl false))
    let queryValue := match queried.1 with | .inr b => bitText b | .inl _ => "wrong-tag"
    let tickValue := match afterQuery.1 with | .inl b => bitText b | .inr _ => "wrong-tag"
    IO.println s!"query|{queryValue}|{tickValue}|{bitText (logical c afterQuery.2)}"
    let sharedResult := (shared c).machine.step (.inr (true,false),(⟨⟩,(resumeState c false,⟨⟩)))
    IO.println s!"shared|{bitText sharedResult.1.1}{bitText sharedResult.1.2}"
    let r := run (parallel c).machine.mealy ((compile c).machine.initial,⟨⟩) sideFixtures
    IO.println s!"parallel|{String.intercalate "," (r.1.map (fun p => bitText p.1 ++ bitText p.2))}|{bitText (logical c r.2.1)}"
  for x in [false,true] do
    for y in [false,true] do
      let answer := match checkBoundary (x,y) with
        | none => "reject"
        | some b => bitText b
      IO.println s!"boundary|{bitText x}{bitText y}|{answer}"
  IO.println s!"admission|{statusText (assessAdmission .native .semantic).status}|{statusText (assessAdmission .native (.bounded 1000)).status}|{statusText (assessAdmission .circuitOnly .semantic).status}|{statusText (assessAdmission .missingAdapter .semantic).status}"
