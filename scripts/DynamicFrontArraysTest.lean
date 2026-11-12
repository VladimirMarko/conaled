import Examples.DynamicFrontArrays
open Resources.DynamicFrontArrays Examples.DynamicFrontArrays
private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)
def main : IO Unit := do
  check "literal full state and event blocks" (decide (grouped add [1,2,3,4] empty =
    (⟨#[some 4,some 3,some 2,some 1],0⟩,literalBlocks)))
  check "eager full state and event blocks" (decide (grouped Eager.add [1,2,3,4] empty =
    (⟨#[none,none,none,none,some 4,some 3,some 2,some 1],4⟩,eagerBlocks)))
  let cases := [(add,[1,2,3],6,6,2,4,1),(Eager.add,[1,2,3],4,6,2,4,1),
    (add,[1,2,3,4],7,6,2,4,0),(Eager.add,[1,2,3,4],8,14,3,8,4)]
  for (step,xs,w,a,g,c,f) in cases do
    let r := execute step xs empty
    check "frozen tariff projections" (work r.2 == w && allocation r.2 == a && Eager.growths r.2 == g)
    check "frozen capacity and free" (r.1.slots.size == c && r.1.free == f)
    check "independent logical reverse" (value r.1 == xs.reverse)
    check "event grouping preserves ordered trace" ((grouped step xs empty).2.flatten == r.2)
  check "literal three complete observation" (decide (grouped add [1,2,3] empty =
    (⟨#[none,some 3,some 2,some 1],1⟩,literalBlocks.take 3)))
  check "eager three complete observation" (decide (grouped Eager.add [1,2,3] empty =
    (⟨#[none,some 3,some 2,some 1],1⟩,eagerBlocks.take 3)))
  check "literal schedule" (bills add work [1,2,3,4,5,6,7,8,9] empty == [1,2,3,1,5,1,1,1,9])
  check "index-sensitive price" (indexZeroPrice (adds [1,2,3,4] empty).2 == 3 &&
    indexZeroPrice (Eager.adds [1,2,3,4] empty).2 == 0)
  check "overwritten window" (decide (copyInto [none,some 7] 1 #[some 90,some 8,some 9,some 91] =
    (#[some 90,none,some 7,some 91],[.copy 1 none,.copy 2 (some 7)])))
  check "non-power literal state" (decide ((adds [7,7,8] ⟨#[none,none,none],3⟩).1 =
    ⟨#[some 8,some 7,some 7],0⟩))
  check "non-power eager state" (decide ((Eager.adds [7,7,8] ⟨#[none,none,none],3⟩).1 =
    ⟨#[none,none,none,some 8,some 7,some 7],3⟩))
  check "initial credit retained" (potential fullSingleton == 1 &&
    work (adds [7] fullSingleton).2 + potential (adds [7] fullSingleton).1 == 4)
  check "eager schedule" (bills Eager.add work [1,2,3,4,5,6,7,8,9] empty == [1,2,1,4,1,1,1,8,1])
  check "copy arbitrary surroundings" (decide (copyInto [none,some 7] 1 #[some 90,none,none,some 91] =
    (#[some 90,none,some 7,some 91],[.copy 1 none,.copy 2 (some 7)])))
  check "out-of-bounds copy still emits attempts" (decide (copyInto [some 7,some 8] 0 #[some 90] =
    (#[some 7],[.copy 0 (some 7),.copy 1 (some 8)])))
  check "empty copy" (decide (copyInto ([] : List (Option Nat)) 8 #[some 9] = (#[some 9],[])))
  for step in [add,Eager.add] do
    check "zero allocation recorded" (decide (step 7 ⟨#[],0⟩ = (⟨#[],0⟩,[.allocate 0,.write 0 7])))
    check "malformed cursor remains total" (decide (step 7 ⟨#[some 9],4⟩ = (⟨#[some 9],3⟩,[.write 3 7])))
    check "empty command list" (decide (execute step [] fullSingleton = (fullSingleton,[])))
    let r := execute step [7,7,8] ⟨#[none,none,none],3⟩
    check "non-power capacity and repeated values" (value r.1 == [8,7,7])
  check "full singleton eager lacks spare" (decide (Eager.add 7 fullSingleton =
    (⟨#[some 7,some 9],0⟩,[.allocate 2,.copy 1 (some 9),.write 0 7])))
  IO.println "dynamic front arrays: complete states, ordered blocks, tariffs, boundary and repeated-command checks passed"
