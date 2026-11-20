import Applications.Resources.SearchTree

/-!
# Nonempty visits of the executed lookup

The existing lookup returns its actual optional payload and two observations:
nonempty node visits and binary strict-comparison calls. Reweighting by the
first projection retains the payload and selects the visit tariff. It neither
reexecutes search nor charges an unchosen subtree. No ordering invariant on the
raw input tree is needed for these recurrence laws.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SearchTree
universe u v
variable {κ : Type u} {ν : Type v} [LinearOrder κ]

/-- The actual lookup result, charged once for every reached nonempty node. -/
def lookupVisitsRun (query : κ) (tree : BinaryTree (κ × ν)) :
    Measured (Option ν) Nat :=
  reweight Prod.fst (lookupRun query tree)

theorem lookupVisitsRun_value (query : κ) (tree : BinaryTree (κ × ν)) :
    (lookupVisitsRun query tree).1 = Search.OrderedMap.lookup query tree :=
  lookupRun_value query tree

/-- Reweighting discards only the comparator-work observation. -/
theorem lookupVisitsRun_work (query : κ) (tree : BinaryTree (κ × ν)) :
    (lookupVisitsRun query tree).2 = (lookupRun query tree).2.1 := rfl

@[simp] theorem lookupVisitsRun_nil (query : κ) :
    lookupVisitsRun (ν := ν) query .nil = (none, 0) := rfl

/-- The returned value and cost follow only the selected child. Equality of
keys terminates at the current node; reaching nil has cost zero. -/
theorem lookupVisitsRun_node (query : κ) (binding : κ × ν)
    (left right : BinaryTree (κ × ν)) :
    lookupVisitsRun query (.node binding left right) =
      if query < binding.1 then
        ((lookupVisitsRun query left).1, (lookupVisitsRun query left).2 + 1)
      else if binding.1 < query then
        ((lookupVisitsRun query right).1, (lookupVisitsRun query right).2 + 1)
      else (some binding.2, 1) := by
  by_cases hleft : query < binding.1
  · simp only [lookupVisitsRun, lookupRun_node, ite_eq_left hleft, reweight]
  · by_cases hright : binding.1 < query
    · simp only [lookupVisitsRun, lookupRun_node, ite_eq_right hleft, ite_eq_left hright, reweight]
    · simp only [lookupVisitsRun, lookupRun_node, ite_eq_right hleft, ite_eq_right hright, reweight]

theorem lookupVisitsRun_work_le_height (query : κ) (tree : BinaryTree (κ × ν)) :
    (lookupVisitsRun query tree).2 ≤ tree.height :=
  lookupRun_visits_le_height query tree

/-- A successful lookup has no terminal nil inspection. This bridge does not
identify inspections and visits for missing keys. -/
theorem lookupInspections_eq_visits_of_success (query : κ) (tree : BinaryTree (κ × ν))
    (value : ν) (success : (lookupVisitsRun query tree).1 = some value) :
    lookupInspections query tree = (lookupVisitsRun query tree).2 := by
  have actual : (lookupRun query tree).1 = some value := success
  simp only [lookupInspections, actual, Option.isNone_some]
  rfl

end Resources.SearchTree
