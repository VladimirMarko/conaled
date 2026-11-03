import Applications.Resources.Persistent.Debits
import Applications.Resources.Persistent.Realization

/-!
# Logical debit laws bound the same measured realization run

An exact duplicate-free enumeration connects the chronological operation list
to a finite accounted node set. Source payment laws and history closure then
bound the abstract debit interpreter's work. Concrete evaluator compatibility
remains a separate obligation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Persistent

universe u v w
variable {V : Type u} {D : Type v}
variable [DecidableEq V] [DecidableEq D]
open scoped BigOperators

/-- The list observation forgets operation multiplicity only for shared support. -/
theorem realizationSupport_eq_supportUnion (realized : V → Multiset D)
    (operations : List V) :
    realizationSupport (fun v => (realized v).toFinset) operations =
      supportUnion operations.toFinset realized := by
  induction operations with
  | nil => simp [realizationSupport, supportUnion]
  | cons operation rest ih =>
      simp [realizationSupport, supportUnion, ih]

variable [Quiver.{w} V]

/-- Local history payment yields an aggregate bound for this exact enumeration. -/
theorem realize_run_bound_of_enumeration (unshared : V → Nat)
    (discharged realized : V → Multiset D) (scope : Finset V)
    (operations : List V) (nodup : operations.Nodup)
    (enumerates : operations.toFinset = scope)
    (closed : HistoryClosed scope) (paid : Paid discharged realized) :
    (run (realizeStep unshared (fun v => (realized v).toFinset)) operations ∅).2 ≤
      ∑ v ∈ scope, (unshared v + (discharged v).card) := by
  calc
    _ = (∑ v ∈ scope, unshared v) + (supportUnion scope realized).card := by
      rw [realize_run_cost, realizationSupport_eq_supportUnion,
        ← List.sum_toFinset unshared nodup, enumerates]
    _ ≤ (∑ v ∈ scope, unshared v) + dischargeCost scope discharged :=
      Nat.add_le_add_left (realized_card_le closed paid) _
    _ = ∑ v ∈ scope, (unshared v + (discharged v).card) := by
      simp only [dischargeCost, Finset.sum_add_distrib]

/-- An initial realized cache can only reduce the same explicitly counted work. -/
theorem realize_run_bound_with_seen (unshared : V → Nat)
    (discharged realized : V → Multiset D) (scope : Finset V)
    (operations : List V) (nodup : operations.Nodup)
    (enumerates : operations.toFinset = scope)
    (closed : HistoryClosed scope) (paid : Paid discharged realized) (seen : Finset D) :
    (run (realizeStep unshared (fun v => (realized v).toFinset)) operations seen).2 ≤
      ∑ v ∈ scope, (unshared v + (discharged v).card) :=
  (realize_run_cost_le_fresh unshared (fun v => (realized v).toFinset) operations seen).trans
    (realize_run_bound_of_enumeration unshared discharged realized scope operations
      nodup enumerates closed paid)

end Resources.Persistent
