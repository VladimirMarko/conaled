import Mathlib.Data.List.Sort

/-! Independent observations for stable key sorting. Records need no order. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting
open List

universe u v w
variable {α : Type u} {β : Type v} {κ : Type w}

abbrev KeySorted [LE κ] (key : α → κ) (xs : List α) : Prop :=
  xs.Pairwise (fun a b => key a ≤ key b)

/-- Equal-key observations retain the original records and their order. -/
def Stable [DecidableEq κ] (key : α → κ) (xs ys : List α) : Prop :=
  ∀ k, ys.filter (fun x => decide (key x = k)) = xs.filter (fun x => decide (key x = k))

/-- A mathematical contract, independent of any sorting implementation. -/
structure StableSort [LE κ] [DecidableEq κ] (key : α → κ) (xs ys : List α) : Prop where
  sorted : KeySorted key ys
  perm : ys.Perm xs
  stable : Stable key xs ys

/-- Preservation of each equal-key sublist plus permutation suffices for stability. -/
theorem stable_of_sublist [DecidableEq κ] (key : α → κ) {xs ys : List α}
    (hp : ys.Perm xs)
    (hsub : ∀ k, xs.filter (fun x => decide (key x = k)) <+ ys) : Stable key xs ys := by
  intro k
  let p := fun x => decide (key x = k)
  have hs := (hsub k).filter p
  have hi : (xs.filter p).filter p = xs.filter p := by simp
  rw [hi] at hs
  exact (hs.eq_of_length (hp.filter p).length_eq.symm).symm

private theorem sorted_eq_of_perm_stable [LE κ] [Std.IsPartialOrder κ] [DecidableEq κ]
    (key : α → κ) {ys zs : List α} (hy : KeySorted key ys) (hz : KeySorted key zs)
    (hp : ys.Perm zs) (hs : Stable key zs ys) : ys = zs := by
  induction ys generalizing zs with
  | nil => exact List.Perm.nil_eq hp
  | cons a ys ih =>
    cases zs with
    | nil => have := hp.length_eq; simp at this
    | cons b zs =>
      have hab : key a ≤ key b := by
        have hm := hp.mem_iff.mpr List.mem_cons_self
        rcases List.mem_cons.mp hm with h | h
        · subst b; exact Std.le_refl _
        · exact (List.pairwise_cons.mp hy).1 _ h
      have hba : key b ≤ key a := by
        have hm := hp.mem_iff.mp List.mem_cons_self
        rcases List.mem_cons.mp hm with h | h
        · subst a; exact Std.le_refl _
        · exact (List.pairwise_cons.mp hz).1 _ h
      have hk : key b = key a := Std.le_antisymm hba hab
      have hf := hs (key a)
      simp only [List.filter_cons, hk, decide_true, ↓reduceIte] at hf
      have he : a = b := (List.cons.inj hf).1
      subst b
      apply congrArg (a :: ·)
      apply ih (List.pairwise_cons.mp hy).2 (List.pairwise_cons.mp hz).2 (List.Perm.cons_inv hp)
      intro k
      have hf := hs k
      by_cases hk : key a = k
      · simpa [List.filter_cons, hk] using hf
      · simpa [List.filter_cons, hk] using hf

/-- Antisymmetry is required on keys, never on records. -/
theorem StableSort.unique [LE κ] [Std.IsPartialOrder κ] [DecidableEq κ]
    {key : α → κ} {xs ys zs : List α} (hy : StableSort key xs ys)
    (hz : StableSort key xs zs) : ys = zs :=
  sorted_eq_of_perm_stable key hy.sorted hz.sorted (hy.perm.trans hz.perm.symm)
    (fun k => (hy.stable k).trans (hz.stable k).symm)

/-- Key-preserving maps may identify payloads; injectivity is unnecessary. -/
theorem StableSort.map [LE κ] [DecidableEq κ] {key : α → κ} {key' : β → κ}
    {xs ys : List α} (h : StableSort key xs ys) (f : α → β)
    (hf : ∀ x, key' (f x) = key x) : StableSort key' (xs.map f) (ys.map f) where
  sorted := by simpa only [KeySorted, List.pairwise_map, hf] using h.sorted
  perm := h.perm.map f
  stable := by
    intro k
    simp only [List.filter_map, Function.comp_def, hf]
    exact congrArg (List.map f) (h.stable k)

end Applications.Sorting
