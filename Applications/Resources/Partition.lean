import Applications.Sequences.Partition
import Applications.Resources.CallCount

/-! The companion source's one-pass three-way partition execution.
The tail is processed once, and its actual returned buckets are extended at
the head. Every recursive entry, including nil, costs one; comparisons,
projections, tuple formation and cons add no charge in this source model.
This does not assign that count to the shared two-pass value implementation,
the two-filter quicksort tariff, or a physical runtime/stack observation.
Source and statement assessment: `docs/research/fdsa-three-way-partition.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Partition
universe u
variable {α : Type u} [LinearOrder α]

/-- Execute the tail once, then extend the selected actual returned bucket. -/
def partitionRun (p : α) : List α → Measured (List α × List α × List α) Nat
  | [] => CallCount.tick (Resources.pure ([], [], []))
  | y :: ys => CallCount.tick (Resources.bind (partitionRun p ys) (fun t =>
      Resources.pure (if y < p then (y :: t.1, t.2.1, t.2.2)
        else if p = y then (t.1, y :: t.2.1, t.2.2)
        else (t.1, t.2.1, y :: t.2.2))))

@[simp] theorem partitionRun_nil (p : α) :
    partitionRun p [] = (([], [], []), 1) := rfl

theorem partitionRun_cons (p y : α) (ys : List α) :
    partitionRun p (y :: ys) =
      CallCount.tick (Resources.bind (partitionRun p ys) (fun t =>
        Resources.pure (if y < p then (y :: t.1, t.2.1, t.2.2)
          else if p = y then (t.1, y :: t.2.1, t.2.2)
          else (t.1, t.2.1, y :: t.2.2)))) := rfl

/-- The actual tail-result bridge connects this execution to the shared values. -/
theorem partitionRun_value (p : α) (xs : List α) :
    (partitionRun p xs).1 = Sequences.Partition.partition3 p xs := by
  induction xs with
  | nil => exact (Sequences.Partition.partition3_nil p).symm
  | cons y ys ih =>
      rw [partitionRun_cons, CallCount.tick_value, Resources.bind_value, ih,
        Sequences.Partition.partition3_cons]
      rfl

@[simp] theorem partitionRun_nil_cost (p : α) :
    (partitionRun p []).2 = 1 := rfl

/-- The actual tail execution supplies all work apart from this entry. -/
theorem partitionRun_cons_cost (p y : α) (ys : List α) :
    (partitionRun p (y :: ys)).2 = (partitionRun p ys).2 + 1 := rfl

/-- The count follows the execution recurrence, independently of bucket values. -/
theorem partitionRun_cost (p : α) (xs : List α) :
    (partitionRun p xs).2 = xs.length + 1 := by
  induction xs with
  | nil => exact partitionRun_nil_cost p
  | cons y ys ih => rw [partitionRun_cons_cost, ih, List.length_cons]

end Resources.Partition
