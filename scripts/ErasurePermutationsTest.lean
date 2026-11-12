import Examples.ErasurePermutations
open Resources.ErasurePermutations
private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)
def main : IO Unit := do
  check "empty removal" (decide (removeRun 1 [] = ([],1)))
  check "head hit stops before suffix" (decide (removeRun 1 [1,2,1] = ([2,1],2)))
  check "first equal hit" (decide (removeRun 1 [2,1,1] = ([2,1],5)))
  check "late hit" (decide (removeRun 1 [2,3,1] = ([2,3],8)))
  check "absent target" (decide (removeRun 9 [2,1,1] = ([2,1,1],10)))
  let fixtures : List (List Nat × Nat × Nat) :=
    [([],1,5),([1],16,21),([1,2],62,73),([1,1],59,70),([1,2,3],249,286),
     ([1,1,2],243,280),([1,2,1],240,277),([1,1,1],231,268),([1,2,3,4],1165,1334)]
  for (xs,construction,complete) in fixtures do
    let r := generate xs
    check "literal construction price" (r.2 == construction)
    check "literal complete-observation price" ((observed xs).2 == complete)
    check "native ordered erasure values" (decide (r.1 = Sequences.Permutations.byErasure xs))
    for extra in List.range 4 do
      check "adequate/excess fuel complete pair" (decide (generateFuel (xs.length+extra) xs = r))
  check "separated duplicate exact order" (decide
    ((generate [1,2,1]).1 = [[1,2,1],[1,1,2],[2,1,1],[2,1,1],[1,2,1],[1,1,2]]))
  check "insufficient fuel differs" (decide (generateFuel 0 [1] ≠ generate [1]))
  check "positional order differs" (decide
    ((generate [1,2,1]).1 ≠ (Resources.PositionalPermutations.generate [1,2,1]).1))
  IO.println "erasure checks passed: 5 removal cases, 9 generation/observation fixtures, 36 fuel pairs, 3 separation checks"
