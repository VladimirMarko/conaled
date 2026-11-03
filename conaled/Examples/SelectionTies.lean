import Applications.Optimization.SelectionTies

/-! Independent positional certificates exercise first/last and order-dual selection. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.SelectionTies
open Optimization Optimization.Thinning

theorem first_text : argmin String.length ["aa", "b", "c", "ddd"] = some "b" := by
  apply (argmin_eq_some_iff_firstMinimum _ _ _).mpr
  exact ⟨["aa"], ["c", "ddd"], rfl, by decide, by decide⟩

theorem last_text : argminLast String.length ["aa", "b", "c", "ddd"] = some "c" := by
  apply (argminLast_eq_some_iff _ _ _).mpr
  exact ⟨["aa", "b"], ["ddd"], rfl, by decide, by decide⟩

theorem strict_tie_step : argminLast String.length ["a", "b"] = some "b" := by
  rw [argminLast_cons]
  rfl

theorem first_maximum :
    argmin (fun p : String × Int => OrderDual.toDual p.2)
      [("a", 2), ("b", 2), ("c", 1)] = some ("a", 2) := by
  apply (argmin_eq_some_iff_firstMinimum _ _ _).mpr
  exact ⟨[], [("b", 2), ("c", 1)], rfl, by simp, by decide⟩

end Examples.SelectionTies
