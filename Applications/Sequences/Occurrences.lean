import Mathlib.Data.List.Basic

/-!
# Ordered positional choices

Each input position supplies its selected value and the list with that position
removed. Equal values remain separate occurrences. Permutation generation and
the forest algorithms share this operation without requiring element equality.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.Occurrences

universe u
variable {α : Type u}

/-- Each input position contributes a choice and its remaining list. -/
def picks : List α → List (α × List α)
  | [] => []
  | x :: xs => (x, xs) :: (picks xs).map (fun p => (p.1, x :: p.2))

/-- The selected occurrence is specified by its preceding and following lists. -/
theorem mem_picks_iff (xs : List α) (x : α) (ys : List α) :
    (x, ys) ∈ picks xs ↔ ∃ front back, xs = front ++ x :: back ∧ ys = front ++ back := by
  induction xs generalizing ys with
  | nil => simp [picks]
  | cons z zs ih =>
      constructor
      · intro h
        rcases List.mem_cons.mp h with h | h
        · cases h
          exact ⟨[], zs, rfl, rfl⟩
        · rcases List.mem_map.mp h with ⟨⟨y, ws⟩, hw, heq⟩
          cases heq
          rcases (ih ws).mp hw with ⟨front, back, hzs, hws⟩
          exact ⟨z :: front, back, by simp [hzs], by simp [hws]⟩
      · rintro ⟨front, back, hxs, hys⟩
        cases front with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hxs hys
            rcases hxs with ⟨rfl, rfl⟩
            subst ys
            exact List.mem_cons_self
        | cons a front =>
            simp only [List.cons_append, List.cons.injEq] at hxs
            rcases hxs with ⟨rfl, hzs⟩
            rw [hys]
            exact List.mem_cons_of_mem _ (List.mem_map.mpr
              ⟨(x, front ++ back), (ih _).mpr ⟨front, back, hzs, rfl⟩, rfl⟩)

/-- Projecting selected values retains the original order and multiplicity. -/
theorem picks_fst (xs : List α) : (picks xs).map Prod.fst = xs := by
  induction xs <;> simp_all [picks, List.map_map, Function.comp_def]

end Sequences.Occurrences
