import Applications.Incremental.LocalRows
import Mathlib.Data.Rat.Defs

/-! A second client uses weighted sums rather than min-plus shortest paths. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.IncrementalRows
open Incremental.LocalRows Dijkstra.Store

def rows : Fin 2 → List (Fin 3) := fun v => if v = 0 then [0,2] else [1]
def coefficient (v : Fin 2) (i : Fin 3) : ℚ :=
  if v = 0 then if i = 0 then 2 else 3 else -1

def pairedInputs : Store 3 (Fin 3 × ℚ) := #v[(0,1),(1,4),(2,2)]
def changes : List (Fin 3 × (Fin 3 × ℚ)) := [(0,(0,5)),(0,(0,7))]
def combine (v : Fin 2) (iq : Fin 3 × ℚ) (acc : ℚ) : ℚ := coefficient v iq.1 * iq.2 + acc
def cache : Fin 2 → ℚ := evaluate combine (fun _ => 0) rows (lookup pairedInputs)
def updated : Fin 2 → ℚ := recompute combine (fun _ => 0) rows pairedInputs cache changes

theorem updated_exact (v : Fin 2) :
    updated v = evaluate combine (fun _ => 0) rows (lookup (updateStore pairedInputs changes)) v :=
  recompute_correct combine (fun _ => 0) rows pairedInputs cache (fun _ => rfl) changes v

example : cache 0 = 8 := by decide +kernel
example : updated 0 = 20 := by rw [updated_exact]; decide +kernel

/-- Repeated writes to column0 leave the independent row1 cached. -/
theorem untouched_row : updated 1 = cache 1 :=
  recompute_untouched combine (fun _ => 0) rows pairedInputs cache changes 1 (by decide +kernel)

example : updated 1 = -4 := by rw [untouched_row]; decide +kernel

end Examples.IncrementalRows
