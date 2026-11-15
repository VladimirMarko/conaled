import Examples.WeakMachine

open SquareKit.WeakHigherOrder SquareKit.WeakMachine Examples.WeakMachine

def check (label : String) (actual expected : Option Nat) : IO Unit :=
  unless actual == expected do throw (IO.userError s!"{label}: got {actual}, expected {expected}")

def main : IO Unit := do
  check "literal at zero fuel" (numeral (execute 0 zero)) (some 0)
  check "returning timeout" (numeral (execute 0 redex)) none
  check "one beta" (numeral (execute 1 redex)) (some 0)
  check "higher-order caller" (numeral (execute 2 (client identity))) (some 0)
  check "function-first budget" (numeral (execute 2 functionFirst)) none
  check "function-first completion" (numeral (execute 3 functionFirst)) (some 0)
  unless isTerminal (execute 0 loopingFunction) do throw (IO.userError "lambda body evaluated early")
  check "capture avoiding redex" (numeral (execute 3 (client (subst closeSeven openRedex)))) (some 7)
  check "capture avoiding direct" (numeral (execute 2 (client (subst closeSeven openIdentity)))) (some 7)
  for n in List.range 20 do
    check "omega timeout" (numeral (execute n (.omega))) none
    check "discard loop timeout" (numeral (execute n discardLoop)) none
    check "invoked loop timeout" (numeral (execute n (client loopingFunction))) none
  IO.println "weak machine: finite runner checks passed; divergence is established by separate infinite-path proofs"
