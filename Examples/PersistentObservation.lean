import Applications.Resources.Persistent.Observation
import Examples.PersistentDebits

/-!
# A legal fork connected to measured debit execution

The origin allocates and discharges one debit. Two children realize it. With
one unit of unshared work at each of the three nodes, the global interpreter
charges four, and the source accounting laws supply exactly that budget.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.PersistentObservation

open Resources Resources.Persistent
open Examples.PersistentDebits
open scoped BigOperators

private def unshared (_ : Fork.Node) : Nat := 1
private def realized (operation : Fork.Node) : Finset Nat :=
  (Fork.realizations operation).toFinset

/-- The bound uses the same fork's proved local laws and exact node enumeration. -/
theorem fork_measured_bound :
    (run (realizeStep unshared realized) Fork.operations ∅).2 ≤ 4 := by
  have bound := realize_run_bound_of_enumeration unshared Fork.discharges Fork.realizations
    Fork.scope Fork.operations Fork.operations_nodup Fork.operations_toFinset
    Fork.closed Fork.law.paid
  have charges : (∑ v ∈ Fork.scope, (unshared v + (Fork.discharges v).card)) = 4 := by
    decide
  simpa only [charges] using bound

/-- The public interpreter identity independently fixes the concrete total. -/
theorem fork_measured_cost :
    (run (realizeStep unshared realized) Fork.operations ∅).2 = 4 := by
  rw [realize_run_cost]
  decide

/-- The two logical futures still share one global realized-support state. -/
theorem fork_composition :
    bind (run (realizeStep unshared realized) [Fork.Node.origin, .left] ∅)
      (run (realizeStep unshared realized) [Fork.Node.right]) = ({7}, 4) := by
  rw [← run_append (realizeStep unshared realized)
    [Fork.Node.origin, .left] [Fork.Node.right] ∅]
  apply Prod.ext
  · rw [realize_run_state]
    decide
  · exact fork_measured_cost

/-- Repeating an occurrence label loses unshared work if its list is silently
replaced by the same finite node set. The bound requires its actual enumeration. -/
theorem duplicate_enumeration_boundary :
    (run (realizeStep unshared realized) (Fork.operations ++ [.left]) ∅).2 = 5 ∧
      (∑ v ∈ Fork.scope, (unshared v + (Fork.discharges v).card)) = 4 ∧
      ¬ (Fork.operations ++ [.left]).Nodup := by
  constructor
  · rw [realize_run_cost]
    decide
  · constructor <;> decide

end Examples.PersistentObservation
