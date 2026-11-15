import Examples.GuardedStreamExecution

open Applications.GuardedStreams
open SquareKit.GuardedStreamCompiler
open SquareKit.GuardedStreamCompiler.Examples

private def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

def main : IO Unit := do
  for n in List.range 20 do
    let expected := (List.range n).map (fun i => i * (i + 1) / 2)
    check s!"fresh triangular prefix {n}" ((recompute n).1 == expected)
  let mut s := empty
  for n in [0, 1, 4, 4, 2, 8, 0, 3, 10] do
    let previous := s
    let r := retain n s
    check s!"retained prefix {n}"
      (r.1.1 == (List.range n).map (fun i => i * (i + 1) / 2))
    check s!"retained maximum {n}" (r.1.2.triangular.length == max previous.triangular.length n)
    if n ≤ previous.triangular.length then
      check s!"repeat/smaller leaves cache {n}" (r.1.2 == previous)
    s := r.1.2
  check "repeated demand saves all three observations"
    (decide ((retainedWorkload [4, 4]).2.1 < (recomputedWorkload [4, 4]).2.1 ∧
      (retainedWorkload [4, 4]).2.2.1 < (recomputedWorkload [4, 4]).2.2.1 ∧
      (retainedWorkload [4, 4]).2.2.2 < (recomputedWorkload [4, 4]).2.2.2))
  check "zero workload pays retained header" ((retainedWorkload [0]).2 == (0, 0, 1))
  check "zero recomputation avoids allocation" ((recomputedWorkload [0]).2 == (0, 0, 0))
  check "single request ties" ((retainedWorkload [1]).2 == (recomputedWorkload [1]).2)
  check "indexed primitive reads coordinate parameter"
    (Progress.unfold ((inputs (fun _ => (1 : Nat)) (fun _ => 0)).step outerBody 0) [] 6 ==
      [1, 2, 3, 4, 5, 6])
  check "parameter input drives triangular stream"
    (Progress.unfold ((inputs (fun n => n + 1) (fun _ => (0 : Nat))).step parameterBody 0) [] 6 ==
      [0, 1, 3, 6, 10, 15])
  check "unguarded recurrence rejected" (!(guarded (Body.recur : Program)))
  IO.println "Guarded stream execution: prefixes, repeated/out-of-order demands, indexed inputs, guard and resource controls passed."
