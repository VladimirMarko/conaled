import Applications.Dijkstra.Sentinel.Range
import Applications.Dijkstra.Observation
import Squares

/-! Raw executions retain their Option failure through composed observations.
The sufficient domain is explicit, and the queue consumer is the existing executor. -/
set_option autoImplicit false
set_option warningAsError true
namespace Dijkstra.Sentinel
open Dijkstra.Core Dijkstra.Optimality
variable {n : Nat}

/-- A sufficient source-correspondence domain, not a characterization of safety. -/
structure SafeProblem (n : Nat) where
  weights : Weights n
  root : Fin n
  bound : Nat
  sentinel : Nat
  edgeBound : EdgeBound weights bound
  range : n * bound < sentinel
  reachable : Reachable weights root

abbrev inputRep (n : Nat) : Squares.Rep := ⟨SafeProblem n, SafeProblem n, id⟩
abbrev rawRep (n : Nat) : Squares.Rep := ⟨Option (RawState n), Option (RawState n), id⟩

/-- Both arrows execute their own loops. The specification reuses accepted Dijkstra. -/
def executionSquare : Squares.Square (inputRep n) (rawRep n) where
  impl i := rawDijkstra i.sentinel (encodeWeights i.sentinel i.weights) i.root
  spec i := (dijkstra i.weights i.root).map (encodeState i.sentinel)
  commutes i := source_dijkstra_refines i.weights i.root i.reachable i.bound i.sentinel
    i.edgeBound i.range

/-- Lift a state observation through the existing outer execution failure. -/
def observationSquare {α : Type} (f : RawState n → α) :
    Squares.Square (rawRep n) (⟨Option α, Option α, id⟩ : Squares.Rep) where
  impl := Option.map f
  spec := Option.map f
  commutes _ := rfl

def allDistances : Squares.Square (inputRep n)
    (⟨Option (List Int), Option (List Int), id⟩ : Squares.Rep) :=
  Squares.compose (observationSquare (fun s => (List.finRange n).map (rawDistance s))) executionSquare

def allParents : Squares.Square (inputRep n)
    (⟨Option (List (Fin n)), Option (List (Fin n)), id⟩ : Squares.Rep) :=
  Squares.compose (observationSquare (fun s => (List.finRange n).map (rawParent s))) executionSquare

def targetDistance (v : Fin n) : Squares.Square (inputRep n)
    (⟨Option Int, Option Int, id⟩ : Squares.Rep) :=
  Squares.compose (observationSquare (fun s => rawDistance s v)) executionSquare

theorem execution_exact (i : SafeProblem n) : executionSquare.impl i =
    some (encodeState i.sentinel (Dijkstra.Observation.final i.weights i.root)) := by
  have he := executionSquare.commutes i
  change executionSquare.impl i = (dijkstra i.weights i.root).map (encodeState i.sentinel) at he
  rw [he]
  rw [Dijkstra.Observation.final_exact]
  rfl

theorem allDistances_exact (i : SafeProblem n) : allDistances.impl i =
    some ((Dijkstra.Observation.allDistanceSquare.impl (i.weights,i.root)).2.map (encode i.sentinel)) := by
  change (executionSquare.impl i).map _ = _
  rw [execution_exact]
  simp only [Option.map_some]
  change some ((List.finRange n).map (fun v => rawDistance (encodeState i.sentinel _) v)) =
    some (((Dijkstra.Observation.allResults i.weights i.root).map Prod.snd).map (encode i.sentinel))
  simp only [encode_distance,Dijkstra.Observation.allResults,List.map_map,
    Function.comp_def,Dijkstra.Observation.result_distance]

theorem allParents_exact (i : SafeProblem n) : allParents.impl i =
    some ((List.finRange n).map (parent (Dijkstra.Observation.final i.weights i.root))) := by
  change (executionSquare.impl i).map _ = _
  rw [execution_exact]
  simp only [Option.map_some]
  exact congrArg some (List.map_congr_left (fun v _ => encode_parent i.sentinel _ v))

/-- Queue outer failure and completed no-path remain distinct in this expression.
Safe all-reachable inputs exclude both by the accepted correctness theorems. -/
theorem targetDistance_queue (i : SafeProblem n) (v : Fin n) : (targetDistance v).impl i =
    (Dijkstra.Observation.queueRun ⟨i.weights,i.root,v⟩).map
      (fun out => encode i.sentinel (out.map Search.Heuristic.Path.cost)) := by
  change (executionSquare.impl i).map _ = _
  rw [execution_exact,Dijkstra.Observation.queueResult_exact]
  simp only [Option.map_some,encode_distance,Dijkstra.Observation.queue_distance_eq,
    Dijkstra.Observation.result_distance]

/-- The actual raw target observation is finite and has the accepted independent optimum. -/
theorem targetDistance_shortest (i : SafeProblem n) (v : Fin n) :
    ∃ d : Nat, (targetDistance v).impl i = some (d : Int) ∧
      Search.Heuristic.DistanceResult (Dijkstra.Semantics.adjacency i.weights)
        (Dijkstra.Semantics.goal v) i.root (some d) := by
  obtain ⟨out,ho,hs⟩ := source_dijkstra_shortest i.weights i.root i.reachable
    i.bound i.sentinel i.edgeBound i.range
  obtain ⟨d,hd,hshort⟩ := hs v
  refine ⟨d,?_,(Dijkstra.Semantics.shortest_iff _ _ _ _).mp hshort⟩
  change (rawDijkstra i.sentinel (encodeWeights i.sentinel i.weights) i.root).map _ = _
  rw [ho]
  exact congrArg some hd

end Dijkstra.Sentinel
