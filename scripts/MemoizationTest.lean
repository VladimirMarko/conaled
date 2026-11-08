import Examples.Memoization

open Applications.Memoization

def check (label : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"memoization check failed: {label}")

def main : IO Unit := do
  for n in List.range 13 do
    let initial := Slots.setup (V := Nat) (n+1)
    let r := Fibonacci.eval n (Nat.le_refl n) initial.1
    let again := Fibonacci.eval n (Nat.le_refl n) r.1.2
    check s!"value {n}" (r.1.1 == (Client.ordinary n).1)
    check s!"setup {n}" (initial.2 == n+1)
    check s!"retained hit {n}" (again.1.1 == r.1.1 && again.2 == (1,0,n+1,0))
    if n ≥ 2 then
      check s!"cold misses {n}" (r.2.2.1 == n+1)
      check s!"cold hits {n}" (r.2.1 == n-2)
      check s!"read visits {n}" (r.2.2.2.1 == n*(n+1))
      check s!"written nodes {n}" (r.2.2.2.2 == (n+1)*(n+2)/2)
    else
      check s!"base miss {n}" (r.2 == (0,1,n+1,n+1))
  let r := Fibonacci.cold 10
  check "saved bodies" (r.2.2.1 == 11 && (Client.ordinary 10).2 == 177)
  check "rebuild loses reuse" (r.2.2.1 + (Fibonacci.cold 10).2.2.1 == 22)
  check "shared workload" ((Resources.run (Fibonacci.step (N := 10)) [10,10]
    (Slots.storage 11).empty).2.2.1 == 11)
  let t := (Words.representation 3).tabulate (fun k => Client.wordMeaning (Words.word k))
  check "ordered word" (Words.observe t [true,false,true] == some ([true,false,true],5))
  check "empty" (Words.observe t [] == some ([],0))
  check "overlength" (Words.observe t [false,false,false,false] == none)
  check "restricted" (Words.observe (Words.restrict (by decide : 1 ≤ 3) t) [true] == some ([true],1))
  check "restricted rejection" (Words.observe (Words.restrict (by decide : 1 ≤ 3) t) [true,false] == none)
  check "domain equivalence" (Examples.Memoization.four.lookup ((1,2),(3,4)) 2 == 3)
  check "stale instance" (((Slots.storage 1).call 0 (fun s => ((8,s),0))
    Examples.Memoization.stale).1.1 == 7)
  IO.println s!"memoization: checks passed for 0..12; cold10 value={r.1.1}, (hits,misses,reads,writes)={r.2}; ordinary bodies={(Client.ordinary 10).2}"
