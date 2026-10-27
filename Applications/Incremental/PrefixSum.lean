import Applications.Incremental.VectorSum
import Mathlib.Data.Finset.Card

/-! Materialized prefixes observations expose a different cost: changing the
first input by a nonzero amount changes every output cell. -/
namespace Incremental.VectorSum
open scoped BigOperators
variable {G : Type} [AddCommGroup G] {n : Nat}

def prefixes (v : Values G n) (i : Fin n) : G :=
  ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), v j

theorem prefix_assign_first (v : Values G (n + 1)) (d : G) (i : Fin (n + 1)) :
    prefixes (assign v (0, v 0 + d)) i = prefixes v i + d := by
  classical
  have hm : (0 : Fin (n + 1)) ∈ Finset.univ.filter (fun j => j ≤ i) := by simp
  simp only [prefixes, assign, Finset.sum_update_of_mem hm]
  rw [← Finset.sum_erase_add _ _ hm]
  simp only [Finset.sdiff_singleton_eq_erase]
  abel

theorem prefix_assign_first_ne (v : Values G (n + 1)) (d : G) (hd : d ≠ 0)
    (i : Fin (n + 1)) : prefixes (assign v (0, v 0 + d)) i ≠ prefixes v i := by
  rw [prefix_assign_first]
  exact fun h => hd (add_left_cancel (h.trans (add_zero _).symm))

omit [AddCommGroup G] in
theorem applyPatch_untouched (v : Values G n) (p : Patch G n) (i : Fin n)
    (h : i ∉ p.map Prod.fst) : applyPatch v p i = v i := by
  induction p generalizing v with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    change applyPatch (assign v a) p i = v i
    rw [ih _ h.2]
    exact Function.update_of_ne h.1 _ _

/-- Any in-place materialization by scalar writes needs at least n+1 writes.
The input change is just one assignment. This excludes compressed/lazy output
representations, whose observation contract is different. -/
theorem prefix_write_lower_bound (v : Values G (n + 1)) (d : G) (hd : d ≠ 0)
    (writes : Patch G (n + 1))
    (correct : applyPatch (prefixes v) writes = prefixes (assign v (0, v 0 + d))) :
    n + 1 ≤ writes.length := by
  classical
  have mem (i : Fin (n + 1)) : i ∈ writes.map Prod.fst := by
    by_contra h
    have he := applyPatch_untouched (prefixes v) writes i h
    rw [correct] at he
    exact prefix_assign_first_ne v d hd i he
  have cover : (Finset.univ : Finset (Fin (n + 1))) ⊆ (writes.map Prod.fst).toFinset := by
    intro i _
    exact List.mem_toFinset.mpr (mem i)
  have hc := Finset.card_le_card cover
  have hl := List.toFinset_card_le (writes.map Prod.fst)
  simpa using le_trans hc hl

end Incremental.VectorSum
