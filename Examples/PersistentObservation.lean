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
  simpa only [realized, charges] using bound

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
    (run (realizeStep unshared realized) (Fork.operations ++ [Fork.Node.left]) ∅).2 = 5 ∧
      (∑ v ∈ Fork.scope, (unshared v + (Fork.discharges v).card)) = 4 ∧
      (Fork.operations ++ [Fork.Node.left]).toFinset = Fork.scope ∧
      ¬ (Fork.operations ++ [Fork.Node.left]).Nodup := by
  constructor
  · rw [realize_run_cost]
    decide
  · exact ⟨by decide, by decide, by decide⟩

private def cycleUnshared (_ : Cycle.Node) : Nat := 0
private def cycleRealized (operation : Cycle.Node) : Finset Nat :=
  (Cycle.realizations operation).toFinset

/-- The payment outside this open scope remains in the measured bound. -/
theorem open_cycle_measured_bound :
    (run (realizeStep cycleUnshared cycleRealized) [Cycle.Node.first] ∅).2 ≤
      Cycle.boundary.card +
        ∑ v ∈ Cycle.openScope, (cycleUnshared v + (Cycle.discharges v).card) :=
  realize_run_bound_with_boundary cycleUnshared Cycle.discharges Cycle.realizations
    Cycle.openScope [Cycle.Node.first] (by decide) (by decide)
    Cycle.boundary Cycle.paid_with_boundary

/-- The same boundary theorem permits independently chosen initial support. -/
theorem open_cycle_bound_with_seen (seen : Finset Nat) :
    (run (realizeStep cycleUnshared cycleRealized) [Cycle.Node.first] seen).2 ≤ 1 := by
  have bound := realize_run_bound_with_boundary_and_seen cycleUnshared
    Cycle.discharges Cycle.realizations Cycle.openScope [Cycle.Node.first]
    (by decide) (by decide) Cycle.boundary seen Cycle.paid_with_boundary
  have credit : Cycle.boundary.card = 1 := by decide
  have internal : (∑ v ∈ Cycle.openScope,
      (cycleUnshared v + (Cycle.discharges v).card)) = 0 := by decide
  simpa only [cycleRealized, credit, internal, Nat.add_zero] using bound

/-- The cost is one, internal payment zero, and external credit one. -/
theorem open_cycle_cost_and_credit :
    (run (realizeStep cycleUnshared cycleRealized) [Cycle.Node.first] ∅).2 = 1 ∧
      (∑ v ∈ Cycle.openScope, (cycleUnshared v + (Cycle.discharges v).card)) = 0 ∧
      Cycle.boundary.card = 1 ∧ ¬ HistoryClosed Cycle.openScope := by
  constructor
  · rw [realize_run_cost]
    decide
  · exact ⟨by decide, by decide, Cycle.open_not_closed⟩

/-- Payment alone leaves the work charge intact; realized support removes it. -/
theorem payment_credit_is_not_realized_support :
    (run (realizeStep cycleUnshared cycleRealized) [Cycle.Node.first] ∅).2 = 1 ∧
      (run (realizeStep cycleUnshared cycleRealized)
        [Cycle.Node.first] Cycle.boundary).2 = 0 := by
  refine ⟨open_cycle_cost_and_credit.1, ?_⟩
  have balance := realize_run_identity cycleUnshared cycleRealized
    [Cycle.Node.first] Cycle.boundary
  have initial : Cycle.boundary.card = 1 := by decide
  have charges : ([Cycle.Node.first].map cycleUnshared).sum = 0 := by decide
  have final : (Cycle.boundary ∪
      realizationSupport cycleRealized [Cycle.Node.first]).card = 1 := by decide
  rw [initial, charges, final] at balance
  omega

end Examples.PersistentObservation
