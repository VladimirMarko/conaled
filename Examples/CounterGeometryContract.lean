import Applications.Resources.BinaryCounter
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit false
set_option warningAsError true
namespace Resources.CounterGeometryContract
open BinaryCounter
example : incWithCost [] = ([true],1) ∧ incWithCost [true] = ([false,true],2) ∧
    incWithCost [false,true] = ([true,true],1) ∧ incWithCost [true,true] = ([false,false,true],3) := by decide
example : (∑ j ∈ Finset.range 2, 4 / 2^j) = 6 ∧
    (∑ j ∈ Finset.range 3, 4 / 2^j) = 7 ∧
    (∑ j ∈ Finset.range 5, 4 / 2^j) = 7 := by decide
example : ([1,2,1,3] : List Nat).sum = 7 ∧ ([1,2,1] : List Nat).sum = 4 ∧
    2*([1,2,1] : List Nat).count 1 ≠ 3 := by decide
example : advance 0 [] ≠ advance 0 [false] := by decide
example : incWithCost [true,true,true] = ([false,false,false,true],4) := by decide
example : ¬ Canonical [false,false] := by simp [Canonical]
example : (bits 5).map value = [0,1,2,3,4] := bits_values 5
end Resources.CounterGeometryContract
