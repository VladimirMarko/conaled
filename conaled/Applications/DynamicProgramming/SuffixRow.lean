import Mathlib.Data.List.Infix

/-! Standard suffix tabulations: only the evaluator depends on the application. -/
set_option autoImplicit false
set_option warningAsError true

namespace DynamicProgramming
universe u v
variable {α : Type u} {β : Type v}

theorem suffixRow_length (evaluate : List α → β) (xs : List α) :
    (xs.tails.map evaluate).length = xs.length + 1 := by simp

theorem suffixRow_ne_nil (evaluate : List α → β) (xs : List α) :
    xs.tails.map evaluate ≠ [] := by
  have := suffixRow_length evaluate xs
  intro h
  rw [h] at this
  simp at this

theorem suffixRow_head (evaluate : List α → β) (xs : List α) (fallback : β) :
    (xs.tails.map evaluate).headD fallback = evaluate xs := by
  cases xs <;> simp

theorem suffixRow_last (evaluate : List α → β) (xs : List α) (fallback : β) :
    (xs.tails.map evaluate).getLastD fallback = evaluate [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.tails_cons, List.map_cons]
    have hn := suffixRow_ne_nil evaluate xs
    cases he : xs.tails.map evaluate with
    | nil => exact False.elim (hn he)
    | cons a rest =>
      change (a :: rest).getLastD fallback = evaluate []
      simpa only [he] using ih

theorem suffixRow_entry (evaluate : List α → β) (xs : List α) (i : Nat)
    (h : i ≤ xs.length) : (xs.tails.map evaluate)[i]? = some (evaluate (xs.drop i)) := by
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨by simpa using Nat.lt_succ_of_le h, ?_⟩
  simp

end DynamicProgramming
