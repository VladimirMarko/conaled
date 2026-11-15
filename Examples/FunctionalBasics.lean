import Applications.Arithmetic.EuclidInduction
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormNum

/-! Checked use of the standard Lean foundations corresponding to FDSA chapter 1.
No parallel Bool, list, set, option, numeric or multiset library is introduced.
Coverage and statement review: `docs/research/fdsa-reconstruction-map.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FunctionalBasics
universe u
variable {α : Type u}

theorem append_associative (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := List.append_assoc xs ys zs

theorem append_equations (x : α) (xs ys : List α) :
    ([] : List α) ++ ys = ys ∧ (x :: xs) ++ ys = x :: (xs ++ ys) := by
  constructor <;> rfl

/-- A nontrivial application of the chapter's branch-sensitive induction rule. -/
theorem gcd_common_divisor (m n d : Nat) (hm : d ∣ m) (hn : d ∣ n) :
    d ∣ Nat.gcd m n := by
  apply (Arithmetic.Euclid.induction
    (P := fun a b => d ∣ a → d ∣ b → d ∣ Nat.gcd a b) ?_ m n) hm hn
  intro a b ih ha hb
  by_cases hb0 : b = 0
  · simpa [Arithmetic.Euclid.gcd_equation, hb0] using ha
  · rw [Arithmetic.Euclid.gcd_equation, ite_eq_right hb0]
    exact ih hb0 hb ((Nat.dvd_mod_iff hb).mpr ha)

theorem gcd_divisor_example : 4 ∣ Nat.gcd 12 8 :=
  gcd_common_divisor 12 8 4 (by decide) (by decide)

theorem gcd_zero_boundary : Nat.gcd 0 0 = 0 := by
  rw [Arithmetic.Euclid.gcd_equation]
  rfl

theorem update_at_key (f : Nat → α) (a : Nat) (b : α) :
    Function.update f a b a = b := by simp

theorem update_away (f : Nat → α) (a x : Nat) (b : α) (h : x ≠ a) :
    Function.update f a b x = f x := by simp [h]

/-- Natural inclusion preserves addition, while subtraction needs its domain. -/
theorem real_cast_add (m n : Nat) : ((m + n : Nat) : Real) = m + n := by simp

theorem real_cast_sub (m n : Nat) (h : n ≤ m) :
    ((m - n : Nat) : Real) = (m : Real) - n := by
  exact Nat.cast_sub h

theorem truncated_subtraction_matters :
    (((0 - 1 : Nat) : Real) = 0) ∧ ((0 : Real) - 1 = -1) := by
  norm_num

theorem integer_to_nat_boundary : Int.toNat (-1) = 0 ∧ Int.toNat 3 = 3 := by
  decide

/-- Multiplicity, not only membership, survives the list-to-multiset conversion. -/
theorem multiset_observations :
    (([2, 2, 3] : List Nat) : Multiset Nat).card = 3 ∧
    (([2, 2, 3] : List Nat) : Multiset Nat).count 2 = 2 ∧
    (([2, 2, 3] : List Nat) : Multiset Nat).sum = 7 := by
  decide

theorem multiset_map_filter :
    ((([2, 2, 3] : List Nat) : Multiset Nat).map (fun x => x + 1)) =
      (([3, 3, 4] : List Nat) : Multiset Nat) ∧
    ((([2, 2, 3] : List Nat) : Multiset Nat).filter (fun x => x = 2)) =
      (([2, 2] : List Nat) : Multiset Nat) := by
  decide

theorem multiset_append (xs ys : List α) :
    ((xs ++ ys : List α) : Multiset α) = (xs : Multiset α) + (ys : Multiset α) :=
  (Multiset.coe_add xs ys).symm

theorem multiset_membership (x : α) (xs : List α) :
    x ∈ (xs : Multiset α) ↔ x ∈ xs := Iff.rfl

theorem option_pair_and_unit (x : α) :
    (some x).map (fun y => (y, ())) = some (x, ()) := rfl

theorem set_comprehension (x : Nat) :
    x ∈ {n : Nat | n < 3} ↔ x < 3 := Iff.rfl

end Examples.FunctionalBasics
