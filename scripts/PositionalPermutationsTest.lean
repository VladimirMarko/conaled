import Examples.PositionalPermutations
open Resources.PositionalPermutations
private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)
def main : IO Unit := do
  check "empty construction" (decide (generate ([] : List Nat) = ([[]], 1)))
  check "three-state positional construction" (decide
    (generate [1,2,3] = ([[1,2,3],[1,3,2],[2,1,3],[2,3,1],[3,1,2],[3,2,1]],274)))
  check "complete observer includes all inner terminals" (decide
    (observeSpines [[],[1,2],[]] = ([[],[1,2],[]],12)))
  check "singleton and two-element prices" (decide
    (generate [1] = ([[1]],18) ∧ generate [1,2] = ([[1,2],[2,1]],69)))
  check "duplicates retain all six branches" (decide
    (generate [1,1,2] = (Examples.PositionalPermutations.duplicates,274)))
  check "construction and complete observation differ" (decide
    ((observed ([] : List Nat)).2 = 5 ∧ (observed [1]).2 = 23 ∧
      (observed [1,2]).2 = 80 ∧ (observed [1,2,3]).2 = 311))
  check "empty outer observer has only its terminal charge" (decide
    (observeSpines ([] : List (List Nat)) = ([],1)))
  check "function labels are observed pointwise" (decide
    ((generate Examples.PositionalPermutations.functions).1.map
      (List.map (fun f => f false)) = [[false,true],[true,false]]))
  check "varying callback prices include duplicate occurrences" (decide
    (mapRun (fun n : Nat => (n+1,n*n)) [1,1,3] = ([2,2,4],18)))
  check "insufficient fuel changes the full result" (decide
    (generateFuel 0 [1] != generate [1]))
  for xs in [[],[1],[1,2],[1,1,2],[1,2,3],[1,2,3,4]] do
    let p := generate xs
    for extra in List.range 4 do
      check "adequate and excess fuel retain complete measured pair"
        (decide (generateFuel (xs.length + extra) xs = p))
  check "four-element construction and observation" (decide
    ((generate [1,2,3,4]).2 = 1270 ∧ (observed [1,2,3,4]).2 = 1439))
  IO.println "positional permutation checks passed: 11 fixed fixtures and 24 full-pair fuel comparisons"
