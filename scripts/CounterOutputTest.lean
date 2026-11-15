import Examples.CounterOutput
open Resources Resources.BinaryCounter Resources.CounterOutput
open Examples.CounterOutput

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

def main : IO Unit := do
  let p := printCounter 5 []
  check "five states require seven writes and 23 emitted tokens"
    (decide (p.transitionWork = 7 ∧ p.symbols = 23))
  check "exact literal token order and line boundaries" (decide (p.lines = fiveLines))
  check "decoded representations" (decide (p.lines.map decodeDigits = fiveStates))
  check "per-line symbol bills" (decide (p.lines.map List.length = [3,4,5,5,6]))
  check "actual four-transition bills" (decide (CounterGeometry.bills 4 [] = [1,2,1,3]))
  check "different tariff is 24, not token count"
    (decide (comparisonRun.2 .outputWrite = 13 ∧
      comparisonRun.2 .outputWrite + (2*fiveStates.length+1) = 24 ∧
      p.symbols + (2*fiveStates.length+1) = 34))
  check "single zero state has no transition"
    (decide ((printCounter 1 []).transitionWork = 0 ∧ (printCounter 1 []).symbols = 3))
  check "noncanonical zero retains its digit"
    (decide ((printCounter 1 [false]).lines = [[.left,.digit false,.right,.lineEnd]] ∧
      (printCounter 1 [false]).symbols = 4))
  check "carry extension"
    (decide (prefixRun 3 [true,true] =
      ([[true,true],[false,false,true],[true,false,true]],4)))
  check "duplicate insertion occurrences and varying bills"
    (decide (insertionObserved.1 = [([1,1,2],3),([1,1,2],3),([1,2,1],5)] ∧
      insertionObserved.2 .outputWrite = 11))
  -- Numeric specification uses addition, independently of bit-write recursion.
  for seed in [[], [false], [true], [true,true], [false,true,false]] do
    for n in List.range 17 do
      let result := printCounter n seed
      check "seeded numeric prefix" (decide
        ((result.lines.map decodeDigits).map value = (List.range n).map (value seed + ·)))
      if n = 0 then
        check "empty prefix performs no work" (decide
          (result.lines = [] ∧ result.transitionWork = 0 ∧ result.symbols = 0))
  IO.println "counter output runtime checks passed: 10 fixed fixtures and 85 seeded prefixes"
