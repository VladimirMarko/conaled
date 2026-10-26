import Std

namespace DynamicProgramming
variable {β : Type}

/-- Finite implementation of source array replacement `//`. The association
values have already been specified; the accumulator only receives writes. -/
def arrayAssign (old : Array β) (updates : List (Nat × β)) : Array β :=
  updates.foldl (fun a p => a.setIfInBounds p.1 p.2) old

/-- Independent simultaneous replacement relation on valid, distinct indices. -/
def ArrayBatch (old result : Array β) (updates : List (Nat × β)) : Prop :=
  result.size = old.size ∧
    (∀ j v, (j, v) ∈ updates → result[j]? = some v) ∧
    (∀ j, (∀ p ∈ updates, p.1 ≠ j) → result[j]? = old[j]?)

theorem arrayAssign_size (old : Array β) (updates : List (Nat × β)) :
    (arrayAssign old updates).size = old.size := by
  induction updates generalizing old with
  | nil => rfl
  | cons p updates ih =>
    change (arrayAssign (old.setIfInBounds p.1 p.2) updates).size = _
    rw [ih, Array.size_setIfInBounds]

theorem arrayAssign_unmentioned (old : Array β) (updates : List (Nat × β))
    (j : Nat) (h : ∀ p ∈ updates, p.1 ≠ j) :
    (arrayAssign old updates)[j]? = old[j]? := by
  induction updates generalizing old with
  | nil => rfl
  | cons p updates ih =>
    change (arrayAssign (old.setIfInBounds p.1 p.2) updates)[j]? = _
    rw [ih _ (fun q hq => h q (List.mem_cons_of_mem p hq))]
    exact Array.getElem?_setIfInBounds_ne (h p (by simp))

theorem arrayAssign_entry (old : Array β) (updates : List (Nat × β))
    (hn : (updates.map Prod.fst).Nodup) (j : Nat) (v : β)
    (hm : (j, v) ∈ updates) (hj : j < old.size) :
    (arrayAssign old updates)[j]? = some v := by
  induction updates generalizing old with
  | nil => simp at hm
  | cons p updates ih =>
    have ht := (List.nodup_cons.mp (by simpa only [List.map_cons] using hn)).2
    have hh := (List.nodup_cons.mp (by simpa only [List.map_cons] using hn)).1
    change (arrayAssign (old.setIfInBounds p.1 p.2) updates)[j]? = _
    rcases List.mem_cons.mp hm with he | hm
    · subst p
      rw [arrayAssign_unmentioned _ updates j (by
        intro q hq he
        apply hh
        exact List.mem_map.mpr ⟨q, hq, he⟩)]
      exact Array.getElem?_setIfInBounds_self_of_lt hj
    · exact ih _ ht hm (by simpa only [Array.size_setIfInBounds] using hj)

theorem arrayAssign_batch (old : Array β) (updates : List (Nat × β))
    (hn : (updates.map Prod.fst).Nodup) (hb : ∀ p ∈ updates, p.1 < old.size) :
    ArrayBatch old (arrayAssign old updates) updates := by
  refine ⟨arrayAssign_size old updates, ?_, ?_⟩
  · intro j v hm
    exact arrayAssign_entry old updates hn j v hm (hb (j, v) hm)
  · exact fun j hj => arrayAssign_unmentioned old updates j hj


end DynamicProgramming
