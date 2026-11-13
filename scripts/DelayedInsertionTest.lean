import Applications.Resources.DelayedInsertion

open Resources.DelayedInsertion

private def check [BEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")

/-- The first public seam: building recipes and counting their outer spine. -/
def main : IO Unit := do
  let built := ordinary (1 : Nat) [2, 3]
  check "ordinary outer cells" (outerCells built.2) 6
  let counted := countOuter built
  check "outer count" counted.1 3
  check "count preserves builder events" counted.2 (built.2 ++ [.outerObserve 4])
  check "build and count do not force callbacks" (callbackBills counted.2) []
  let forced := forceAll (fun ys : List Nat => (ys, 7)) built.1
  check "ordered insertion values" forced.1 [[1,2,3],[2,1,3],[2,3,1]]
  check "every callback charged" (callbackBills forced.2) [7,7,7]
  let acc := accumulating (fun ys : List Nat => (ys, 7)) 1 [2,3]
  check "accumulating outer cells" (outerCells acc.2) 3
  check "accumulating values" (readout acc.1) [[1,2,3],[2,1,3],[2,3,1]]
  check "accumulating build has no callbacks" (callbackBills acc.2) []
  let table := prepare (ordinary (1 : Nat) [1])
  let f := fun ys : List Nat => (ys, 9)
  let init := setup table.1
  check "setup cells" init.2 [.setupCells 2]
  let first := retained table.1 f ⟨0, by decide⟩ init.1
  let again := retained table.1 f ⟨0, by decide⟩ first.1.2.1
  check "retained repeat hit" again.1.2.2 (1,0,1,0)
  check "retained repeat no callback" (callbackBills again.2) []
  let workload : List (Fin table.1.size) := [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩]
  let retainedResult := retainedRun table.1 f workload init.1
  check "retained workload ordered values" retainedResult.1.1 [[1,1],[1,1],[1,1]]
  check "all native counters" retainedResult.1.2.2 (1,2,4,3)
  check "retained callback bills" (callbackBills retainedResult.2) [9,9]
  check "retained state first entry"
    (Applications.Memoization.Slots.read retainedResult.1.2.1 ⟨0, by decide⟩).1
    (some ([1,1], [.selection 1,.payloadCons,.callback 9]))
  check "retained state second entry"
    (Applications.Memoization.Slots.read retainedResult.1.2.1 ⟨1, by decide⟩).1
    (some ([1,1], [.selection 2,.payloadCons,.payloadCons,.callback 9]))
  check "delayed callback bills" (callbackBills (delayedRun table.1 f workload).2) [9,9,9]
  check "complete observation" (complete 1 [2,3] (fun ys : List Nat => (ys,7))).1
    [[1,2,3],[2,1,3],[2,3,1]]
  let visits := fun (es : Trace) => (es.filterMap fun e => match e with
    | .selection n => some n | _ => none).sum
  check "delayed selection visits" (visits (delayedRun table.1 f workload).2) 4
  check "retained miss-only selection visits" (visits retainedResult.2) 3
  check "delayed full body work" (bodyWork (delayedRun table.1 f workload).2) 31
  check "retained full body work" (bodyWork retainedResult.2) 21
  check "empty count" (countOuter (ordinary (1 : Nat) [])).1 1
  check "singleton count" (countOuter (ordinary (1 : Nat) [2])).1 2
  check "empty forcing cons" (payloadCells (forceAll f (ordinary 1 []).1).2) 1
  check "full ordinary payload cells" (payloadCells forced.2) 6
  check "full accumulating payload cells" (payloadCells (forceThunks acc.1).2) 6
  check "empty ordinary output" (forceAll f (ordinary 1 []).1).1 [[1]]
  check "empty ordinary construction" (outerCells (ordinary (1 : Nat) []).2) 1
  check "empty accumulating construction" (outerCells (accumulating f 1 []).2) 1
  check "singleton ordinary construction" (outerCells (ordinary (1 : Nat) [2]).2) 3
  check "singleton accumulating construction" (outerCells (accumulating f 1 [2]).2) 2
  check "singleton outputs" (forceAll f (ordinary 1 [2]).1).1 [[1,2],[2,1]]
  check "singleton body cons" (payloadCells (forceAll f (ordinary 1 [2]).1).2) 3
  let observeBills := fun (es : Trace) => es.filterMap fun e => match e with
    | .innerObserve n => some n | _ => none
  check "empty outer observer terminal" (observeBills (observe ([], []) : Resources.Measured (List (List Nat)) Trace).2) [1]
  check "empty inner observer terminal" (observeBills (observe ([[]], []) : Resources.Measured (List (List Nat)) Trace).2) [4]
  check "empty insertion observer" (observeBills (complete 1 [] f).2) [5]
  check "singleton insertion observer" (observeBills (complete 1 [2] f).2) [11]
  check "three insertion observer" (observeBills (complete 1 [2,3] f).2) [19]
  check "empty callback payloads observer" (observeBills (complete 1 [2,3]
    (fun _ : List Nat => (([] : List Nat), 8))).2) [10]
  let nonuniform := fun ys : List Nat => (ys, ys.headD 0)
  check "nonuniform callback order" (callbackBills (forceAll nonuniform built.1).2) [1,2,2]
  check "selected demand only" (callbackBills (delayed (prepare built).1 nonuniform ⟨1,by decide⟩).2) [2]
  check "nonuniform accumulated callback order" (callbackBills (forceThunks
    (accumulating nonuniform 1 [2,3]).1).2) [1,2,2]
  let rebuilt := [retained table.1 f ⟨0,by decide⟩ init.1,
    retained table.1 f ⟨0,by decide⟩ init.1, retained table.1 f ⟨1,by decide⟩ init.1]
  check "rebuilding loses hits" (rebuilt.map fun r => r.1.2.2).sum (0,3,4,4)
  check "rebuilding repeats callbacks" (rebuilt.flatMap fun r => callbackBills r.2) [9,9,9]
  let cachedAgain := retainedRun table.1 f workload retainedResult.1.2.1
  check "cached workload all hits" cachedAgain.1.2.2 (3,0,4,0)
  check "cached workload callback free" (callbackBills cachedAgain.2) []
  check "cached lists still observed" (observeBills (observe (cachedAgain.1.1,cachedAgain.2)).2) [16]
  let functions := forceAll (fun ys : List (Nat → Nat) => (ys,2))
    (ordinary (fun n => n+1) [fun n => n*2]).1
  check "function-valued labels" (functions.1.map (fun ys => ys.map (fun g => g 5))) [[6,10],[10,6]]
  check "arbitrary tail" (readout (accumulating (fun ys : List Nat => (ys ++ [8,9],3)) 1 [2]).1)
    [[1,2,8,9],[2,1,8,9]]
  check "actual accumulating full observation" (completeAccumulating 1 [2,3] f).1
    [[1,2,3],[2,1,3],[2,3,1]]
  check "retained full observation" (completeRetained 1 [2,3] f).1.1
    [[1,2,3],[2,1,3],[2,3,1]]
  let accTable := (prepare (accumulatingRecipes (1 : Nat) [1])).1
  let accRequests : List (Fin accTable.size) := [⟨0,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩]
  let accCached := retainedRun accTable f accRequests (setup accTable).1
  check "accumulating retained native counters" accCached.1.2.2 (1,2,4,3)
  check "accumulating retained body work" (bodyWork accCached.2) 21
  check "accumulating retained ordered values" accCached.1.1 [[1,1],[1,1],[1,1]]
  check "repeated delayed thunk work doubles"
    (bodyWork (delayedRun table.1 f [⟨0,by decide⟩,⟨0,by decide⟩]).2) 20
  let nilCallback := fun (_ : List Nat) => (([] : List Nat),8)
  let nilFirst := retained table.1 nilCallback ⟨0,by decide⟩ (setup table.1).1
  let nilHits := retainedRun table.1 nilCallback [⟨0,by decide⟩,⟨0,by decide⟩] nilFirst.1.2.1
  check "cached empty payloads all hit" nilHits.1.2.2 (2,0,2,0)
  check "cached empty payloads still observed" (observeBills (observe (nilHits.1.1,nilHits.2)).2) [7]
  let g := fun ys : List Nat => (ys,10)
  let f0 := (delayed table.1 f ⟨0,by decide⟩).2
  let f1 := (delayed table.1 f ⟨1,by decide⟩).2
  let g0 := (delayed table.1 g ⟨0,by decide⟩).2
  let g1 := (delayed table.1 g ⟨1,by decide⟩).2
  check "two-phase callback order" (callbackBills (f0 ++ f1 ++ g0 ++ g1)) [9,9,10,10]
  check "interleaved callback order" (callbackBills (f0 ++ g0 ++ f1 ++ g1)) [9,10,9,10]
  check "schedule scalar equality" (bodyWork (f0 ++ f1 ++ g0 ++ g1),bodyWork (f0 ++ g0 ++ f1 ++ g1)) (44,44)
  IO.println "delayed insertion: construction, forcing, cache state/counters and observer cases passed"
