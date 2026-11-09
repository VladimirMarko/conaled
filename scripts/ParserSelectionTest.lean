import Examples.ParserSelection

open LanguageWitnesses ParserWorkload ParserSelection ParserWorkloadExamples
open ParserSelectionExamples Resources.Prepared

def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

def observe : Option (Decision Payload) → Option (List Bool)
  | some (.yes x) => some x.1
  | _ => none

def main : IO Unit := do
  check "exhaustive profiles retain setup, validation and arenas"
    (observations source ==
      [(0,259,33,202), (1221,7,821,822), (46,114,60,124), (728,7,449,450)])
  let cases := [("repeated",roomy,source,repeated,some Policy.combined),
    ("short",roomy,source,short,some Policy.normalized),
    ("simple",roomy,Spine.base [true,false],repeated,some Policy.retained),
    ("heavy",roomy,heavy,repeated,some Policy.combined),
    ("storage",{roomy with capacity := 200, peak := 200},source,repeated,some Policy.normalized),
    ("deadline",{roomy with deadline := 7},source,short,some Policy.combined),
    ("impossible",{roomy with deadline := 2},source,repeated,none),
    ("empty",roomy,source,[],some Policy.ordinary)]
  for (name,req,p,qs,expected) in cases do
    let selected := offline req p qs
    check name (selected == expected)
    match selected with
    | none => check "no feasible policy" (catalog.all fun c => !decide (Feasible req (profile 2 3 3 unitTariff c) p))
    | some c =>
      check "selected feasible" (decide (Feasible req (profile 2 3 3 unitTariff c) p))
      let r := execute c p 2 qs
      let witness := if name == "heavy" then List.replicate 100 true else [true,false]
      check "selected payloads" (r.answers.map observe == qs.map (fun _ => some witness))
      check "full tariff" (batchCost unitTariff r == r.work)
      check "actual batch peak bounded" (r.peak ≤ (profile 2 3 3 unitTariff c).peak p)
  check "typed offline envelope" (chooseOffline 2 3 3 unitTariff roomy
    (offlineInput source (List.replicate 20 ParserSelectionExamples.q)) == some .combined)
  check "unknown future count objective" (online roomy source 20 == some .combined)
  check "zero future count" (online roomy source 0 == some .ordinary)
  check "heavy maps still charged" ((execute .combined heavy 2 repeated).count .map == 5729)
  check "heavy setup retained" ((profile 2 3 3 unitTariff .combined).retained heavy == 11621)
  for c in catalog do
    let prepared := (rawOps 2 3 3 unitTariff c).prepare source
    let badDepth := (rawOps 2 3 3 unitTariff c).answer prepared.1
      ⟨(3,[]), by decide⟩
    let badWord := (rawOps 2 3 3 unitTariff c).answer prepared.1
      ⟨(1,[true,true,true]), by decide⟩
    check "rejected depth answer/cost" (observe badDepth.1 == none && badDepth.2 == 3)
    check "rejected word answer/cost" (observe badWord.1 == none && badWord.2 == 6)
  IO.println "Parser selection runtime checks passed"
