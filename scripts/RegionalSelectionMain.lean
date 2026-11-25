import Examples.RegionalSelection
open FRPSpec.Regional FRPSpec.Regional.Selection Progress.Feedback Optimization.Choice
instance : BEq Sites := ⟨fun a b => decide (a = b)⟩

def bitText (b : Bool) : String := if b then "1" else "0"
def pairText (p : Bool × Bool) := bitText p.1 ++ bitText p.2
def inputFromCode : Nat → Input
  | 0 => .inl false | 1 => .inl true | 2 => .inr (false,false)
  | 3 => .inr (false,true) | 4 => .inr (true,false) | _ => .inr (true,true)
def reportCheck (name : String) (b : Bool) : IO Unit := IO.println s!"check|{name}|{b}"
def chosen (e : Option Epoch) : Option Sites := (installation roomy "fixture" e).1.map Session.sites

def main : IO Unit := do
  for c in catalog do
    for a in [false,true] do
      for b in [false,true] do
        for i in List.range 6 do
          for j in List.range 6 do
            let word := [(i,j),(j,i),(4,3)]
            let xs := word.map fun p => (inputFromCode p.1,inputFromCode p.2)
            let start : Session := ⟨c,c.resume (a,b)⟩
            let firstRun := start.advance (xs.take 1)
            let suffix := firstRun.2.advance (xs.drop 1)
            IO.println s!"run|{c.name}|{pairText (a,b)}|{String.intercalate "," (word.map fun p => s!"{p.1}{p.2}")}|{String.intercalate "," ((firstRun.1 ++ suffix.1).map pairText)}|{pairText (suffix.2.sites.observe suffix.2.state)}"
  let epoch := synthetic roomy "fixture" checkedSites
  let updated := synthetic roomy "fixture" splitSites
  reportCheck "epoch-change" (chosen (some epoch) == some checkedSites && chosen (some updated) == some splitSites)
  let old := Session.start checkedSites
  let first := old.advance (inputs.take 1)
  let retained := first.2.advance (inputs.drop 1)
  reportCheck "old-session" (retained.1 == [(false,true),(true,false)] && retained.2.sites == checkedSites)
  let fixed := chosen none
  reportCheck "stale-protocol" (chosen (some {epoch with context := {epoch.context with protocol := "stale"}}) == fixed)
  reportCheck "stale-budget" (chosen (some (synthetic {capacity := 9999} "fixture" checkedSites)) == fixed)
  reportCheck "stale-catalog" (chosen (some (synthetic roomy "fixture" checkedSites [checkedSites])) == fixed)
  reportCheck "wrong-implementation" (chosen (some {epoch with context := {epoch.context with implementation := "wrong"}}) == fixed)
  reportCheck "incomplete" (chosen (some {epoch with samples := epoch.samples.drop 1}) == fixed)
  reportCheck "empty" (select roomy "fixture" none [] == none)
  reportCheck "valid-fallback" ((installationFallback roomy "fixture" none [] fusedSites).1.map Session.sites == some fusedSites)
  reportCheck "bad-fallback" ((installationFallback {capacity := 0} "fixture" none [] fusedSites).1.map Session.sites == none)
  reportCheck "joint-budget" (decide ((compile Cut.fused).storage < fusedSites.plan.storage))
  reportCheck "unsupported" (!(assess (.direct : Plan Input Bool) 10000).acceptedFlag)
  reportCheck "invalid-port" (select {roomy with protocol := 2} "fixture" none == none)
  let stale := {epoch with context := {epoch.context with protocol := "stale"}}
  reportCheck "validation-path-cost" (bill (installation roomy "fixture" (some stale)).2 <
    bill (installation roomy "fixture" (some epoch)).2)
  reportCheck "fallback-cost" (bill (installation roomy "fixture" none []).2 <
    bill (installationFallback roomy "fixture" none [] fusedSites).2)
  let ctx := admittedContext catalog (eligible roomy) Sites.name (context roomy "fixture")
  let duplicate := {epoch with samples := epoch.samples.headD ⟨"missing",0,0,false,ctx⟩ :: epoch.samples.headD ⟨"missing",0,0,false,ctx⟩ :: epoch.samples.drop 2}
  reportCheck "duplicate-epoch" (!duplicate.complete ctx 1 && chosen (some duplicate) == fixed)
  reportCheck "mismatched-sample" (chosen (some {epoch with samples := epoch.samples.map fun s =>
    {s with context := {s.context with target := "other"}}}) == fixed)
  for c in catalog do
    IO.println s!"cost|{c.name}|{c.plan.work}|{c.plan.storage}"
  for e in [none,some epoch,some updated] do
    let before ← IO.monoNanosNow
    let installed := installation roomy "fixture" e
    let after ← IO.monoNanosNow
    match installed.1 with
    | none => throw (IO.userError "unexpected empty installation")
    | some s =>
      let began ← IO.monoNanosNow
      let result := s.advance inputs
      let finished ← IO.monoNanosNow
      IO.println s!"comparison|{s.sites.name}|{bill installed.2}|{after-before}|{finished-began}|{String.intercalate "," (result.1.map pairText)}"
  let fixedStart ← IO.monoNanosNow
  let fixedSession := Session.start fusedSites
  let fixedReady ← IO.monoNanosNow
  let fixedResult := fixedSession.advance inputs
  let fixedDone ← IO.monoNanosNow
  IO.println s!"fixed|{fusedSites.name}|{fixedReady-fixedStart}|{fixedDone-fixedReady}|{String.intercalate "," (fixedResult.1.map pairText)}"
  let directStart ← IO.monoNanosNow
  let directResult := run oracle.mealy (false,false) inputs
  let directDone ← IO.monoNanosNow
  IO.println s!"direct|{directDone-directStart}|{String.intercalate "," (directResult.1.map pairText)}"
  for c in catalog do
    let mut s := Session.start c
    let mut work := 0
    for x in inputs do
      let result := s.tick x
      work := work + bill result.2.2
      s := result.2.1
    IO.println s!"execution-bill|{c.name}|{work}"
