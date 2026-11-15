import Applications.Search.Incremental.Patches
import Applications.Search.Incremental.Fresh
import SquareKit.Relations

/-! A retained-state repair and its distance observer compose as relational
squares. This exposes proved operations; it does not add recursion to FirstOrder. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
variable {n : Nat}

structure RepairInput (n : Nat) (start goal : Fin n) (h : Fin n → ℚ) where
  graph : Graph n
  positive : Positive graph
  retained : State n
  valid : Valid graph start retained
  changes : Batch n
  changes_positive : PositiveBatch changes
  final_heuristic : ConsistentHeuristic (applyBatch graph changes) goal h

def RepairInput.execute {start goal : Fin n} {h : Fin n → ℚ}
    (p : RepairInput n start goal h) : Graph n × State n :=
  (applyBatch p.graph p.changes,
    repair p.graph p.positive start goal h p.retained p.valid p.changes p.changes_positive p.final_heuristic)

def inputRep (n : Nat) (start goal : Fin n) (h : Fin n → ℚ) : Relational.RelRep :=
  ⟨RepairInput n start goal h, Graph n × Batch n,
    fun p spec => p.graph = spec.1 ∧ p.changes = spec.2⟩

def retainedRep (n : Nat) (start goal : Fin n) : Relational.RelRep :=
  ⟨Graph n × State n, Graph n, fun p w =>
    p.1 = w ∧ Valid w start p.2 ∧ DistanceResult w start goal (p.2.g goal)⟩

def distanceRep (n : Nat) (start goal : Fin n) : Relational.RelRep :=
  ⟨Graph n × Cost, Graph n, fun p w => p.1 = w ∧ DistanceResult w start goal p.2⟩

def repairSquare (n : Nat) (start goal : Fin n) (h : Fin n → ℚ) :
    Relational.RelSquare (inputRep n start goal h) (retainedRep n start goal) where
  impl := RepairInput.execute
  spec := fun p => applyBatch p.1 p.2
  preserves := by
    intro p spec hp
    rcases hp with ⟨hw, he⟩
    change p.graph = spec.1 at hw
    change p.changes = spec.2 at he
    change (RepairInput.execute p).1 = applyBatch spec.1 spec.2 ∧ _
    rw [← hw, ← he]
    exact ⟨rfl, repair_correct p.graph p.positive start goal h p.retained p.valid
      p.changes p.changes_positive p.final_heuristic⟩

def observationSquare (n : Nat) (start goal : Fin n) :
    Relational.RelSquare (retainedRep n start goal) (distanceRep n start goal) where
  impl := fun p => (p.1, p.2.g goal)
  spec := id
  preserves := by intro p w hp; exact ⟨hp.1, hp.2.2⟩

def repairDistanceSquare (n : Nat) (start goal : Fin n) (h : Fin n → ℚ) :=
  Relational.compose (observationSquare n start goal) (repairSquare n start goal h)

theorem repairDistanceSquare_correct (start goal : Fin n) (h : Fin n → ℚ)
    (p : RepairInput n start goal h) :
    DistanceResult (applyBatch p.graph p.changes) start goal
      ((repairDistanceSquare n start goal h).impl p).2 :=
  ((repairDistanceSquare n start goal h).preserves (s := (p.graph,p.changes)) ⟨rfl,rfl⟩).2

end Search.Incremental
