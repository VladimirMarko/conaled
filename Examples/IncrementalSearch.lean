import Applications.Search.Incremental.Core

/-! Independent rational path calculations exercised through the retained loop. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.IncrementalSearch
open Search.Incremental

/-- The two-edge route costs 1/2+1/3=5/6, less than the direct cost2. -/
def triangle : Graph 3 := fun u v =>
  if u = 0 ∧ v = 1 then (1/2 : ℚ)
  else if u = 1 ∧ v = 2 then (1/3 : ℚ)
  else if u = 0 ∧ v = 2 then 2 else ⊤

def observed (out : Outcome 3) : Option Cost :=
  match out with
  | .stopped s => some (s.g 2)
  | .exhausted _ => none

example : observed (run triangle 0 2 (fun _ => 0) 6 (initial 0)) = some (5/6 : ℚ) := by decide +kernel

end Examples.IncrementalSearch
