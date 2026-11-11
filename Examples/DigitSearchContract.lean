import Applications.Resources.ListFusion
import SquareKit.FiniteSums
import Mathlib.Data.List.Pi
set_option autoImplicit false
set_option warningAsError true
namespace Resources.DigitSearchContract
abbrev Digit := Fin 10
def large (d : Digit) : Bool := decide (5 ≤ d.val)
def digits : List Digit := List.finRange 10
-- Independently enumerated length-two product, head-major as required.
def pairs : List (List Digit) := digits.flatMap (fun a => digits.map (fun b => [a,b]))
example : ([0,4,8,9] : List Digit).findIdx? large = some 2 := by decide
example : ([0,4,3] : List Digit).findIdx? large = none := by decide
example : ([8,8] : List Digit).findIdx? large = some 0 := by decide
example : pairs.take 2 = [[0,0],[0,1]] := by decide
example : (pairs.drop 9).take 2 = [[0,9],[1,0]] := by decide
example : (pairs.filter (fun xs => xs.findIdx? large == some 0)).length = 50 ∧
    (pairs.filter (fun xs => xs.findIdx? large == some 1)).length = 25 ∧
    (pairs.filter (fun xs => xs.findIdx? large == none)).length = 25 := by decide
example : (50*1+25*2+25*2 : Nat)=150 := by decide
example : (150/100 : ℚ)=3/2 ∧ (10/10 : ℚ)=1 ∧ (0/1 : ℚ)=0 := by norm_num
example : ([digits,digits].sections).take 2 = [[0,0],[1,0]] := by decide
end Resources.DigitSearchContract
