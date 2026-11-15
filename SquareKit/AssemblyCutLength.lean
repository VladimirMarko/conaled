import SquareKit.AssemblyCuts

/-! The finite/full length determined by a descending family of observations. -/
namespace Realizability.Assembly

/-- Observations of a finite or infinite cut. -/
def cutTest (n : Option Nat) (k : Nat) : Prop := n.elim True (fun n => k < n)

noncomputable def cutLength (P : Nat → Prop) : Option Nat := by
  classical
  exact if h : ∃ n, ¬ P n then some (Nat.find h) else none

theorem cutLength_test (P : Nat → Prop) (hd : ∀ k, P (k + 1) → P k) (k : Nat) :
    cutTest (cutLength P) k ↔ P k := by
  classical
  have hmono : ∀ m n, m ≤ n → P n → P m := by
    intro m n h
    induction h with
    | refl => exact id
    | step h ih => exact fun hn => ih (hd _ hn)
  unfold cutLength
  split_ifs with h
  · change k < Nat.find h ↔ P k
    constructor
    · intro hk
      exact not_not.mp (Nat.find_min h hk)
    · intro hk
      by_contra hn
      exact Nat.find_spec h (hmono _ _ (Nat.le_of_not_gt hn) hk)
  · change True ↔ P k
    simp only [true_iff]
    by_contra hk
    exact h ⟨k, hk⟩

theorem cutTest_ext {x y : Option Nat} (h : ∀ k, cutTest x k ↔ cutTest y k) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some n => exact False.elim (Nat.lt_irrefl n ((h n).mp trivial))
  | some m =>
    cases y with
    | none => exact False.elim (Nat.lt_irrefl m ((h m).mpr trivial))
    | some n =>
      congr 1
      apply Nat.le_antisymm
      · by_contra hn
        exact Nat.lt_irrefl n ((h n).mp (Nat.lt_of_not_ge hn))
      · by_contra hm
        exact Nat.lt_irrefl m ((h m).mpr (Nat.lt_of_not_ge hm))

end Realizability.Assembly
