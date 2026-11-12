import Applications.Search.Incremental.Semantics
import Applications.Incremental.LocalRows

/-! The rhs dependency argument is a specialization of the shared row-fold law. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
variable {n : Nat}

theorem predecessorMinimum_fold (w : Graph n) (g : Labels n) (v : Fin n) :
    predecessorMinimum w g v =
      _root_.Incremental.LocalRows.fold min ⊤ (List.finRange n) (fun u => g u + w u v) := by
  have he : (List.finRange n).toFinset = Finset.univ := by ext u; simp
  rw [predecessorMinimum, ← he]
  exact _root_.Incremental.LocalRows.inf_eq_fold _ _

theorem rhsValue_congr_inputs (w w' : Graph n) (start : Fin n) (g g' : Labels n) (v : Fin n)
    (he : ∀ u, g u + w u v = g' u + w' u v) :
    rhsValue w start g v = rhsValue w' start g' v := by
  unfold rhsValue
  split
  · rfl
  · rw [predecessorMinimum_fold, predecessorMinimum_fold]
    exact _root_.Incremental.LocalRows.fold_congr min ⊤ _ _ _ (fun u _ => he u)

end Search.Incremental
