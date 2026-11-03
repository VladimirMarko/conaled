import Applications.Subsequences.Frontier
import Mathlib.Data.List.Pairwise

/-! Longest increasing witnesses, with global optimality transported from the frontier. -/
set_option autoImplicit false
set_option warningAsError true
namespace Subsequences
universe u
variable {α : Type u}
open Segments (LengthOrdered)

/-- Strictly ordered lengths justify the source's final last selection. -/
theorem lengthOrdered_last (ps : List (List α)) (hs : LengthOrdered ps) (hn : ps ≠ []) :
    ps.getLastD [] ∈ ps ∧ ∀ p ∈ ps, p.length ≤ (ps.getLastD []).length := by
  have hg : ps.getLastD [] = ps.getLast hn := by cases ps with
    | nil => contradiction
    | cons p ps => rfl
  rw [hg]
  refine ⟨List.getLast_mem hn, ?_⟩
  intro p hp
  exact (hs.imp (fun h => Nat.le_of_lt h)).rel_getLast_of_rel_getLast_getLast hp (Nat.le_refl _)

/-- Global optimality is over ALL independently increasing input sublists. -/
theorem lus_optimal (xs : List Int) : LusOptimal xs (lus xs) := by
  let cost : List Int → OrderDual Nat := fun p => OrderDual.toDual p.length
  have hl := lengthOrdered_last (lusStates xs) (lusStates_lengthOrdered xs) (lusStates_ne_nil xs)
  have localOpt : lus xs ∈ Optimization.minimizers {p | p ∈ lusStates xs} cost :=
    ⟨hl.1, fun _ hp => hl.2 _ hp⟩
  have globalOpt := Optimization.Thinning.minimizer_of_represents
    (lusStates_refinement xs) cost (fun _ _ _ _ h => upDominates_length _ _ h) localOpt
  have hf := (mem_upStates xs _).mp globalOpt.1
  exact ⟨hf.1, hf.2, fun candidate hc hi =>
    globalOpt.2 ((mem_upStates xs candidate).mpr ⟨hc, hi⟩)⟩

theorem lus_mem_lus0 (xs : List Int) : lus xs ∈ lus0 xs :=
  (mem_lus0 xs (lus xs)).mpr (lus_optimal xs)

/-- This is equality of optimum LENGTH, not equality of all tied witnesses. -/
theorem lus_length_eq_optimum (xs candidate : List Int) (h : LusOptimal xs candidate) :
    (lus xs).length = candidate.length :=
  lusOptimal_length_eq xs (lus xs) candidate (lus_optimal xs) h

theorem lus_length_le (xs : List Int) : (lus xs).length ≤ xs.length :=
  lusOptimal_length_le xs (lus xs) (lus_optimal xs)

theorem lus_of_increasing (xs : List Int) (hi : Increasing xs) : lus xs = xs :=
  (lusOptimal_of_increasing xs (lus xs) hi).mp (lus_optimal xs)

/-- Retained candidate entries only: no runtime, allocation, or bit-cost claim. -/
theorem lusStates_count_le (xs : List Int) : (lusStates xs).length ≤ (lus xs).length + 1 := by
  have hn : ((lusStates xs).map List.length).Nodup := by
    apply List.pairwise_map.mpr
    exact (lusStates_ordered xs).imp (fun h => Nat.ne_of_lt h.1)
  have hl := lengthOrdered_last (lusStates xs) (lusStates_lengthOrdered xs) (lusStates_ne_nil xs)
  have hb : (lusStates xs).map List.length ⊆ List.range ((lus xs).length + 1) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have hbound : p.length ≤ (lus xs).length := hl.2 p hp
    exact List.mem_range.mpr (Nat.lt_succ_of_le hbound)
  simpa only [List.length_map, List.length_range] using hn.length_le_of_subset hb

theorem lusStates_count_le_input (xs : List Int) : (lusStates xs).length ≤ xs.length + 1 :=
  Nat.le_trans (lusStates_count_le xs) (Nat.add_le_add_right (lus_length_le xs) 1)

@[simp] theorem lus_nil : lus [] = [] := rfl

end Subsequences
