import Applications.Resources.BinaryCounter
import Applications.Resources.Growth
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-! Finite floor geometry from actual increment branches, with ordered native bills. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.CounterGeometry
open BinaryCounter

theorem even_from_zero_bit (n : Nat) (bs : Bits) :
    totalCost (2*n) (false::bs) = 2*n+totalCost n bs := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,totalCost_succ,totalCost_succ]
    simp only [flipCost,inc,ih,totalCost_succ]
    omega

theorem odd_from_zero_bit (n : Nat) (bs : Bits) :
    totalCost (2*n+1) (false::bs) = 2*n+1+totalCost n bs := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)+1=(2*n+1)+1+1 by omega,totalCost_succ,totalCost_succ]
    simp only [flipCost,inc,ih,totalCost_succ]
    omega

theorem empty_zero_padding (n : Nat) : totalCost n [] = totalCost n [false] := by
  cases n with
  | zero => rfl
  | succ n => simp only [totalCost_succ,flipCost,inc]

theorem zero_even (n : Nat) : totalCost (2*n) [] = 2*n+totalCost n [] := by
  rw [empty_zero_padding (2*n)]; exact even_from_zero_bit n []
theorem zero_odd (n : Nat) : totalCost (2*n+1) [] = 2*n+1+totalCost n [] := by
  rw [empty_zero_padding (2*n+1)]; exact odd_from_zero_bit n []

theorem halving (n : Nat) : totalCost n [] = n+totalCost (n/2) [] := by
  have hm : n%2<2 := Nat.mod_lt n (by decide)
  have hd := Nat.mod_add_div n 2
  by_cases hz : n%2=0
  · have he : n=2*(n/2) := by omega
    calc
      totalCost n [] = totalCost (2*(n/2)) [] := congrArg (fun k => totalCost k []) he
      _ = 2*(n/2)+totalCost (n/2) [] := zero_even _
      _ = n+totalCost (n/2) [] := by omega
  · have he : n=2*(n/2)+1 := by omega
    calc
      totalCost n [] = totalCost (2*(n/2)+1) [] := congrArg (fun k => totalCost k []) he
      _ = 2*(n/2)+1+totalCost (n/2) [] := zero_odd _
      _ = n+totalCost (n/2) [] := by omega

/-- Independent finite natural floor sum, retaining exponent zero. -/
def floorSum (n k : Nat) : Nat := ∑ j ∈ Finset.range k, n/2^j

theorem floorSum_succ (n k : Nat) : floorSum n (k+1) = floorSum n k+n/2^k :=
  Finset.sum_range_succ _ _

theorem remainder (n k : Nat) :
    totalCost n [] = floorSum n k + totalCost (n/2^k) [] := by
  induction k with
  | zero => simp [floorSum]
  | succ k ih =>
    rw [ih,halving (n/2^k),floorSum_succ]
    rw [Nat.div_div_eq_div_mul,← Nat.pow_succ]
    simp only [Nat.succ_eq_add_one] at *
    omega

theorem exact_cutoff (n k : Nat) (h : n/2^k=0) : totalCost n [] = floorSum n k := by
  simpa [h,totalCost_zero] using remainder n k

theorem exact_of_lt (n k : Nat) (h : n<2^k) : totalCost n [] = floorSum n k :=
  exact_cutoff n k (Nat.div_eq_of_lt h)

theorem floorSum_halving (n k : Nat) : floorSum n (k+1) = n+floorSum (n/2) k := by
  induction k with
  | zero => simp [floorSum]
  | succ k ih =>
    rw [floorSum_succ n (k+1),ih,floorSum_succ]
    rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm (2^k) 2]
    omega

theorem floorSum_bound (n k : Nat) : floorSum n k ≤ 2*n := by
  induction k generalizing n with
  | zero => simp [floorSum]
  | succ k ih => rw [floorSum_halving]; have h := ih (n/2); omega

/-- Independent geometric derivation; does not invoke potential-based bounds. -/
theorem geometric_bound (n : Nat) : totalCost n [] ≤ 2*n := by
  rw [exact_of_lt n n (Nat.lt_two_pow_self)]
  exact floorSum_bound n n

theorem lower (n : Nat) : n ≤ totalCost n [] := by rw [halving]; omega

theorem theta : Asymptotics.IsTheta Filter.atTop
    (fun n : Nat => (totalCost n [] : ℝ)) (fun n : Nat => (n:ℝ)) := by
  constructor
  · exact isBigO_of_nat_bound _ _ 2 0 (fun n _ => geometric_bound n)
  · exact isBigO_of_nat_bound _ _ 1 0 (fun n _ => by simpa using lower n)

theorem power_two_exact (k : Nat) : totalCost (2^k) []+1=2^(k+1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ,Nat.mul_comm (2^k) 2,zero_even]
    simp only [Nat.pow_succ] at ih ⊢
    omega

theorem extending_carry (k : Nat) :
    incWithCost (List.replicate k true) = (List.replicate k false ++ [true],k+1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,incWithCost,ih]; omega

theorem advance_exact (n k : Nat) (h : n<2^k) :
    advanceWithCost n [] = (advance n [],floorSum n k) := by
  rw [advanceWithCost_eq,exact_of_lt n k h]

theorem observed_states_exact (n k : Nat) (h : n-1<2^k) :
    bitsTransitionCost n = floorSum (n-1) k := exact_of_lt (n-1) k h

/-- Record each actual transition's aggregate write count in order. -/
def recordStep (_ : Unit) (bs : Bits) : Measured Bits (Additive (FreeMonoid Nat)) :=
  let r := incWithCost bs
  (r.1,Additive.ofMul (FreeMonoid.of r.2))

def trace (n : Nat) (bs : Bits) : Measured Bits (Additive (FreeMonoid Nat)) :=
  Resources.run recordStep (List.replicate n ()) bs

def bills (n : Nat) (bs : Bits) : List Nat := (trace n bs).2.toMul.toList

def sumBills : Additive (FreeMonoid Nat) →+ Nat where
  toFun xs := xs.toMul.toList.sum
  map_zero' := rfl
  map_add' _xs _ys := List.sum_append

theorem trace_reweight (n : Nat) (bs : Bits) :
    reweight sumBills (trace n bs) = advanceWithCost n bs := by
  rw [trace,reweight_run]
  rfl

theorem trace_state (n : Nat) (bs : Bits) : (trace n bs).1 = advance n bs := by
  have h := congrArg Prod.fst (trace_reweight n bs)
  simpa [reweight,advanceWithCost_eq] using h

theorem bills_sum (n : Nat) (bs : Bits) : (bills n bs).sum = totalCost n bs := by
  have h := congrArg Prod.snd (trace_reweight n bs)
  change (bills n bs).sum = (advanceWithCost n bs).2 at h
  simpa only [advanceWithCost_eq] using h

theorem bills_succ (n : Nat) (bs : Bits) : bills (n+1) bs = flipCost bs :: bills n (inc bs) := by
  simp [bills,trace,List.replicate_succ,Resources.run,bind,recordStep,incWithCost_eq]

theorem bills_prefix (n : Nat) (bs : Bits) : bills n bs = (iteratePrefix inc n bs).map flipCost := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => rw [bills_succ,ih]; rfl

theorem bills_length (n : Nat) (bs : Bits) : (bills n bs).length=n := by
  rw [bills_prefix,List.length_map]; exact length_iteratePrefix inc n bs

theorem bills_entry (n j : Nat) (bs : Bits) : (bills n bs)[j]? =
    if j<n then some (incWithCost (advance j bs)).2 else none := by
  rw [bills_prefix,List.getElem?_map,getElem?_iteratePrefix_inc]
  split <;> simp [incWithCost_eq]

theorem trace_append (n m : Nat) (bs : Bits) :
    trace (n+m) bs = bind (trace n bs) (trace m) := by
  simp only [trace,List.replicate_add,Resources.run_append]
  rfl

theorem bills_append (n m : Nat) (bs : Bits) :
    bills (n+m) bs = bills n bs ++ bills m (advance n bs) := by
  simp [bills,trace_append,bind,trace_state]

end Resources.CounterGeometry
