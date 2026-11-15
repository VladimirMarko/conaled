import Examples.FoldedPruneContract
set_option autoImplicit false
set_option warningAsError true
namespace Resources.PricedPruneContract

-- Independent ordered transition prices: length work plus dispatch count.
example : (2+1 : Nat)=3 ∧ 3+1=4 ∧ 12+3=15 ∧ 3+1=4 ∧ 4+1=5 := by decide
example : (3+4+15+4+5 : Nat)=31 ∧ 33+2*5=43 ∧ 9+3=12 ∧ 31+7=38 := by decide
example : (24+2*7 : Nat)=38 ∧ 38+7=45 ∧ 21+3=24 ∧ 24+7=31 := by decide
example : (14+4 : Nat)=18 ∧ 18+5=23 ∧ 6+4=10 ∧ 2+1=3 := by decide
example : (5+12 : Nat)=6+11 ∧ 5+12≠11 := by decide

-- The coefficient obstruction concerns a finite all-g/all-n bound only.
example (C : Nat) : C < 3+2*(C+1) := by omega
example (g : Nat) (hg : 0<g) : ¬ g ≤ (0:Nat) := by omega
end Resources.PricedPruneContract
