import Applications.Search.Incremental.RepairCosts
import Applications.Search.Incremental.FreshCosts

/-! Observation-inclusive accounting and agreement of the two search machines.
The memory bound counts live logical cells, not Lean closure or trace storage. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
open Accounting
variable {n : Nat}

def measuredInitialize (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ConsistentHeuristic w goal h) : Accounting.Measured (State n × Cost) :=
  let out := Measured.initializeState w hw start goal h hh
  let obs := Measured.observe goal out.1
  ((out.1, obs.1), out.2 ++ obs.2)

def measuredRepair (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (s : State n) (hs : Valid w start s)
    (es : Batch n) (hp : PositiveBatch es) (hh : ConsistentHeuristic (applyBatch w es) goal h) :
    Accounting.Measured (State n × Cost) :=
  let out := Measured.repair w hw start goal h s hs es hp hh
  let obs := Measured.observe goal out.1
  ((out.1, obs.1), out.2 ++ obs.2)

theorem measuredRepair_correct (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (s : State n) (hs : Valid w start s)
    (es : Batch n) (hp : PositiveBatch es) (hh : ConsistentHeuristic (applyBatch w es) goal h) :
    Valid (applyBatch w es) start (measuredRepair w hw start goal h s hs es hp hh).1.1 ∧
      DistanceResult (applyBatch w es) start goal (measuredRepair w hw start goal h s hs es hp hh).1.2 := by
  simpa [measuredRepair, Measured.observe] using repair_correct w hw start goal h s hs es hp hh

theorem measuredRepair_fresh (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (s : State n) (hs : Valid w start s)
    (es : Batch n) (hp : PositiveBatch es) (hh : ConsistentHeuristic (applyBatch w es) goal h) :
    (measuredRepair w hw start goal h s hs es hp hh).1.2 =
      (FreshCosts.result (applyBatch w es) h start goal).1 :=
  distance_unique (measuredRepair_correct w hw start goal h s hs es hp hh).2
    (FreshCosts.result_correct (applyBatch_positive w hw es hp) hh start)

/-- The rerun comparator receives the same ordered assignments. -/
def measuredGraphPatch : Graph n → Batch n → Accounting.Measured (Graph n)
  | w, [] => (w, [.read,.branch])
  | w, e :: es =>
    let tail := measuredGraphPatch (assign w e) es
    (tail.1, [.read,.branch,.read,.read,.read,.write] ++ tail.2)

@[simp] theorem measuredGraphPatch_value (w : Graph n) (es : Batch n) :
    (measuredGraphPatch w es).1 = applyBatch w es := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih => exact ih (assign w e)

def measuredRerun (w : Graph n) (es : Batch n) (h : Fin n → ℚ) (start goal : Fin n) :
    Accounting.Measured Cost :=
  let patched := measuredGraphPatch w es
  let out := FreshCosts.result patched.1 h start goal
  (out.1, patched.2 ++ out.2)

@[simp] theorem measuredRerun_value (w : Graph n) (es : Batch n) (h : Fin n → ℚ) (start goal : Fin n) :
    (measuredRerun w es h start goal).1 = Fresh.result (applyBatch w es) h start goal := by
  simp [measuredRerun]

/-- Graph cells, heuristic cells, two label maps, queued identifiers, endpoints. -/
def retainedCells (s : State n) : Nat := n*n + 3*n + s.queue.length + 2

theorem retainedCells_le {w : Graph n} {start : Fin n} {s : State n} (hs : Valid w start s) :
    retainedCells s ≤ n*n + 4*n + 2 := by
  have hq : s.queue.length ≤ n := by simpa using hs.2.1.length_le_card
  unfold retainedCells
  omega

end Search.Incremental
