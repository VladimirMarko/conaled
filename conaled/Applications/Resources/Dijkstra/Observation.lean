import Applications.Resources.Dijkstra.Execution
import Applications.Dijkstra.Observation

/-! Cost-preserving observations of the actual measured executor. Target lookup
and queue comparison here are semantic observations, not extra charged runtime.
Segments share one source base charge, including after failure. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.DijkstraCosts
open Dijkstra.Core Dijkstra.Observation
variable {n : Nat}

def executionSquare (n : Nat) := Resources.erasureSquare
  (fun i : Weights n × Fin n => dijkstraRun i.1 i.2)
  (fun i => dijkstra i.1 i.2) (fun i => dijkstraRun_value i.1 i.2)

/-- Semantic projection retains the measured computation's charge. -/
def targetObservationSquare (target : Fin n) :
    Squares.Square ⟨Measured (Option (State n)) Nat, Option (State n), Prod.fst⟩
      ⟨Measured (Option Distance) Nat, Option Distance, Prod.fst⟩ where
  impl r := Resources.bind r
    (fun out => Resources.pure (out.map (fun s => distance s target)))
  spec out := out.map (fun s => distance s target)
  commutes _ := rfl

def targetSquare (target : Fin n) :=
  Squares.compose (targetObservationSquare target) (executionSquare n)

/-- Observe the returned state; both failure and unreachable target stay explicit. -/
def targetRun (i : Problem n) : Measured (Option Distance) Nat :=
  (targetSquare i.target).impl (i.weights,i.root)

theorem targetRun_value (i : Problem n) : (targetRun i).1 = some (result i).2 := by
  change ((dijkstraRun i.weights i.root).1.map (fun s => distance s i.target)) = _
  rw [dijkstraRun_value, final_exact, Option.map_some, result_distance]

theorem targetRun_work (i : Problem n) : (targetRun i).2 = (dijkstraRun i.weights i.root).2 := by
  change (dijkstraRun i.weights i.root).2 + 0 = _
  exact Nat.add_zero _

theorem targetRun_bound (i : Problem n) :
    (targetRun i).2 ≤ (n-1)*(18*n+6)+2*n+3 := by
  rw [targetRun_work]
  exact dijkstraRun_work _ _

theorem targetRun_correct (i : Problem n) :
    ∃ d, (targetRun i).1 = some d ∧
      Search.Heuristic.DistanceResult (Dijkstra.Semantics.adjacency i.weights)
        (Dijkstra.Semantics.goal i.target) i.root d :=
  ⟨_, targetRun_value i, permitted_distance (result_permitted i)⟩

/-- Actual queue execution agrees on value; its implementation has no price claim here. -/
theorem targetRun_queue (i : Problem n) :
    (targetRun i).1 = (queueRun i).map (Option.map Search.Heuristic.Path.cost) := by
  rw [targetRun_value, queueResult_exact, Option.map_some, queue_distance_eq]

/-- A continuation accepts the actual previous result, including failure. -/
def segment (wa : Weights n) (k : Nat) (s : Option (State n)) :
    Measured (Option (State n)) Nat :=
  Resources.run (iteration wa) (List.replicate k ()) s

def segmentedRun (wa : Weights n) (k l : Nat) (s : State n) :
    Measured (Option (State n)) Nat :=
  Resources.bind (Resources.bind (some s,1) (segment wa k)) (segment wa l)

theorem segment_append (wa : Weights n) (k l : Nat) (s : Option (State n)) :
    Resources.bind (segment wa k s) (segment wa l) = segment wa (k+l) s := by
  unfold segment
  rw [List.replicate_add, Resources.run_append]

theorem segmentedRun_exact (wa : Weights n) (k l : Nat) (s : State n) :
    segmentedRun wa k l s = runCost wa (k+l) s := by
  calc
    segmentedRun wa k l s =
        let r := Resources.bind (segment wa k (some s)) (segment wa l)
        (r.1, 1+r.2) := by simp [segmentedRun, Resources.bind, Nat.add_assoc]
    _ = let r := segment wa (k+l) (some s); (r.1, 1+r.2) := by rw [segment_append]
    _ = runCost wa (k+l) s := by simp [segment, runCost, Nat.add_comm]

theorem segmentedRun_value (wa : Weights n) (k l : Nat) (s : State n) :
    (segmentedRun wa k l s).1 = Dijkstra.Core.run wa (k+l) s := by
  rw [segmentedRun_exact, runCost_value]

theorem segmentedRun_bound (wa : Weights n) (k l : Nat) (s : State n)
    (hn : s.fresh.Nodup) : (segmentedRun wa k l s).2 ≤ (k+l)*(18*n+6)+1 := by
  rw [segmentedRun_exact]
  exact runCost_work _ _ _ hn

end Resources.DijkstraCosts
