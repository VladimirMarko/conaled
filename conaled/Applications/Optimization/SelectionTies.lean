import Applications.Optimization.SelectionSpec
import Applications.Optimization.Thinning

/-! Exact tie contracts for the existing total selector and its reversed traversal. -/
set_option autoImplicit false
set_option warningAsError true

namespace Optimization
open Thinning
universe u v
variable {α : Type u} {K : Type v} [LinearOrder K]

theorem argmin_firstMinimum (cost : α → K) (xs : List α) (a : α)
    (h : argmin cost xs = some a) : FirstMinimum cost xs a := by
  induction xs generalizing a with
  | nil => simp [argmin] at h
  | cons x xs ih =>
    cases he : argmin cost xs with
    | none =>
      have hn := (argmin_eq_none_iff cost xs).mp he
      subst xs
      simp only [argmin, Option.some.injEq] at h
      subst a
      exact ⟨[], [], rfl, by simp, by simp⟩
    | some y =>
      have ht := ih y he
      have hm := argmin_correct cost xs y he
      by_cases hx : cost x ≤ cost y
      · simp only [argmin, he, ite_eq_left hx, Option.some.injEq] at h
        subst a
        exact ⟨[], xs, rfl, by simp, fun z hz => le_trans hx (hm.2 hz)⟩
      · simp only [argmin, he, ite_eq_right hx, Option.some.injEq] at h
        subst a
        obtain ⟨before, after, hs, hb, ha⟩ := ht
        refine ⟨x :: before, after, congrArg (x :: ·) hs, ?_, ha⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact lt_of_not_ge hx
        · exact hb z hz

theorem argmin_eq_some_of_firstMinimum (cost : α → K) (xs : List α) (a : α)
    (h : FirstMinimum cost xs a) : argmin cost xs = some a := by
  obtain ⟨before, after, rfl, hb, ha⟩ := h
  induction before with
  | nil => exact argmin_first cost a after ha
  | cons x before ih =>
    have ht := ih (fun y hy => hb y (List.mem_cons_of_mem x hy))
    have hx : ¬ cost x ≤ cost a := not_le.mpr (hb x List.mem_cons_self)
    simp [argmin, ht, hx]

theorem argmin_eq_some_iff_firstMinimum (cost : α → K) (xs : List α) (a : α) :
    argmin cost xs = some a ↔ FirstMinimum cost xs a :=
  ⟨argmin_firstMinimum cost xs a, argmin_eq_some_of_firstMinimum cost xs a⟩

theorem lastMinimum_iff_first_reverse (cost : α → K) (xs : List α) (a : α) :
    LastMinimum cost xs a ↔ FirstMinimum cost xs.reverse a := by
  constructor
  · rintro ⟨before, after, rfl, hb, ha⟩
    refine ⟨after.reverse, before.reverse, ?_, ?_, ?_⟩
    · simp [List.reverse_append, List.reverse_cons, List.append_assoc]
    · intro y hy; exact ha y (List.mem_reverse.mp hy)
    · intro y hy; exact hb y (List.mem_reverse.mp hy)
  · rintro ⟨before, after, he, hb, ha⟩
    refine ⟨after.reverse, before.reverse, ?_, ?_, ?_⟩
    · have hr := congrArg List.reverse he
      simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using hr
    · intro y hy; exact ha y (List.mem_reverse.mp hy)
    · intro y hy; exact hb y (List.mem_reverse.mp hy)

/-- Last ties reuse the same selector, traversing candidates in reverse. -/
abbrev argminLast (cost : α → K) (xs : List α) : Option α := argmin cost xs.reverse

theorem argminLast_eq_some_iff (cost : α → K) (xs : List α) (a : α) :
    argminLast cost xs = some a ↔ LastMinimum cost xs a := by
  rw [argminLast, argmin_eq_some_iff_firstMinimum, lastMinimum_iff_first_reverse]

theorem argminLast_correct (cost : α → K) (xs : List α) (a : α)
    (h : argminLast cost xs = some a) : a ∈ minimizers {x | x ∈ xs} cost := by
  simpa using argmin_correct cost xs.reverse a h

/-- The reversed traversal realizes the source strict right-fold recurrence exactly. -/
theorem argminLast_cons (cost : α → K) (x : α) (xs : List α) :
    argminLast cost (x :: xs) =
      match argminLast cost xs with
      | none => some x
      | some y => some (if cost x < cost y then x else y) := by
  cases he : argminLast cost xs with
  | none =>
    have hn : xs = [] := by simpa using (argmin_eq_none_iff cost xs.reverse).mp he
    subst xs
    rfl
  | some y =>
    have hm := argminLast_correct cost xs y he
    change argminLast cost (x :: xs) = some (if cost x < cost y then x else y)
    by_cases hx : cost x < cost y
    · rw [ite_eq_left hx]
      apply (argminLast_eq_some_iff cost (x :: xs) x).mpr
      exact ⟨[], xs, rfl, by simp, fun z hz => lt_of_lt_of_le hx (hm.2 hz)⟩
    · rw [ite_eq_right hx]
      obtain ⟨before, after, hs, hb, ha⟩ := (argminLast_eq_some_iff cost xs y).mp he
      apply (argminLast_eq_some_iff cost (x :: xs) y).mpr
      refine ⟨x :: before, after, congrArg (x :: ·) hs, ?_, ha⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact le_of_not_gt hx
      · exact hb z hz

end Optimization
