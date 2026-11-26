import Applications.Search.IntervalTree.Balanced
import Applications.Search.RectangleSweep.Correctness

/-!
# Rectangle intersection using a balanced interval tree

The existing sweep sorts its events once and distinguishes input occurrences
by complete keys. Its active set now uses the concrete height/maximum tree.
This is functional correctness; measured sweep costs remain a separate obligation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RectangleSweep
universe u v
variable {α : Type u} {β : Type v}
variable [LinearOrder α] [OrderBot α] [LinearOrder β]

/-- The existing event algorithm with tolerance-one balanced active intervals. -/
def balancedSweep (rs : List (Rectangle α β)) : Bool :=
  sweep (IntervalTree.Balanced.deleteOps keyInterval)
    (IntervalTree.Balanced.search keyInterval) rs

/-- Closed boundary contact and duplicate values retain occurrence semantics. -/
theorem balancedSweep_eq_true_iff_hasIntersection (rs : List (Rectangle α β)) :
    balancedSweep rs = true ↔ Rectangle.HasIntersection rs :=
  sweep_eq_true_iff_hasIntersection
    (IntervalTree.Balanced.intervalSet_laws keyInterval keyInterval_low_le_of_lt) rs

end Search.RectangleSweep
