import Applications.Resources.CounterGeometry
import Examples.CounterGeometryContract

/-! Ordinary measured callers and finite counter-geometry boundaries. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CounterGeometry
open Resources Resources.BinaryCounter Resources.CounterGeometry

example : totalCost 0 [] = 0 ∧ totalCost 1 [] = 1 := by decide
example : totalCost 4 [] = 7 := by have h := power_two_exact 2; norm_num at h; omega
example : totalCost 5 [] = 8 := by rw [exact_of_lt 5 3 (by decide)]; decide
example : floorSum 4 2 = 6 ∧ floorSum 4 2 ≠ totalCost 4 [] := by decide
example : totalCost 4 [] = floorSum 4 2 + totalCost 1 [] := remainder 4 2
example : floorSum 4 3 = 7 ∧ floorSum 4 5 = 7 := by decide
example : (∑ j ∈ Finset.range 3, 4/2^(j+1)) = 3 ∧
    (∑ j ∈ Finset.range 3, 4/2^(j+1)) ≠ totalCost 4 [] := by decide
example : totalCost (2^0) [] + 1 = 2^(0+1) := power_two_exact 0

/-- A complete-pair client retains the actual final state along with exact writes. -/
example : advanceWithCost 4 [] = ([false,false,true],7) := by
  rw [advance_exact 4 3 (by decide)]
  rfl
example : (bits 5).map value = [0,1,2,3,4] ∧ bitsTransitionCost 5 = 7 := by
  constructor
  · exact bits_values 5
  · rw [observed_states_exact 5 3 (by decide)]; rfl
example : bitsTransitionCost 0 = 0 ∧ bitsTransitionCost 1 = 0 := by decide

example : bills 3 [] = [1,2,1] ∧ bills 4 [] = [1,2,1,3] := by decide
example : 2*(bills 3 []).count 1 ≠ 3 := by decide
example (n : Nat) (bs : Bits) : (bills n bs).sum = totalCost n bs := bills_sum n bs
example (n m : Nat) (bs : Bits) :
    bills (n+m) bs = bills n bs ++ bills m (advance n bs) := bills_append n m bs
example : (bills 4 [false,false])[1]? = some (incWithCost (advance 1 [false,false])).2 :=
  bills_entry 4 1 [false,false]
example (n : Nat) : totalCost n [] = totalCost n [false] := empty_zero_padding n
example : (trace 0 []).1 ≠ (trace 0 [false]).1 := by decide
example : incWithCost [true,true,true] = ([false,false,false,true],4) := extending_carry 3
example : ¬ (incWithCost [true,true,true]).2 ≤ 2 := by decide
example (n : Nat) : totalCost (2*n) [false,false,false] = 2*n+totalCost n [false,false] :=
  even_from_zero_bit n [false,false]
example (n : Nat) : totalCost (2*n+1) [false,false,false] = 2*n+1+totalCost n [false,false] :=
  odd_from_zero_bit n [false,false]
example : Asymptotics.IsTheta Filter.atTop
    (fun n : Nat => (totalCost n [] : ℝ)) (fun n : Nat => (n : ℝ)) := theta
end Examples.CounterGeometry
