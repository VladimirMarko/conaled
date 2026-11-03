import Applications.Resources.Dijkstra.Observation
import Examples.Dijkstra

/-! Public cost/value contracts specialized to source branches, real graph
outputs, ordered stores and continuations through failure. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.DijkstraCosts
open _root_.Dijkstra.Core _root_.Dijkstra.Observation Resources.DijkstraCosts
open Examples.Dijkstra

def finiteScore (d v : Nat) : Score := toLex (d,v)

theorem comparator_prices :
    compareRun (finiteScore 5 0) (finiteScore 3 1) = (false,1) ∧
    compareRun (finiteScore 3 9) (finiteScore 5 0) = (true,2) ∧
    compareRun (finiteScore 3 9) (finiteScore 3 0) = (false,3) ∧
    compareRun (finiteScore 3 2) (finiteScore 3 2) = (true,3) := by decide

theorem comparator_value : (compareRun (finiteScore 3 9) (finiteScore 3 0)).1 =
    decide (finiteScore 3 9 ≤ finiteScore 3 0) := compareRun_value _ _

theorem selector_boundaries : minimumRun ([] : List (Candidate 2)) = (none,1) ∧
    chooseByRun (fun _ : Fin 2 => finiteScore 0 0) [] = (none,1) ∧
    chooseByRun (fun _ : Fin 2 => finiteScore 0 0) [1] = (some 1,3) ∧
    chooseByRun (fun _ : Fin 2 => finiteScore 0 0) [1,0] = (some 1,9) := by decide

theorem materialized_tie_value :
    (chooseByRun (fun _ : Fin 2 => finiteScore 0 0) [1,0]).1 =
      Optimization.Thinning.argmin (fun _ => finiteScore 0 0) [1,0] := chooseByRun_value _ _

/-- Mapping may collapse distinct inputs; first occurrence still transports. -/
theorem noninjective_selection :
    Optimization.Thinning.argmin id ([3,1].map (fun n : Nat => n%2)) =
      (Optimization.Thinning.argmin (fun n : Nat => n%2) [3,1]).map (fun n => n%2) :=
  Optimization.Thinning.argmin_map _ _ _

theorem addition_prices : plusRun (some 7) none = (none,1) ∧
    plusRun none (some 7) = (none,2) ∧ plusRun (some 3) (some 7) = (some 10,3) := by decide

theorem addition_value : (plusRun none (some 7)).1 = plus none (some 7) := plusRun_value _ _

def listCell : _root_.Dijkstra.Store.Store 1 (List Nat) := Vector.ofFn (fun _ => [])

theorem repeated_bulk :
    Resources.DijkstraStore.bulkRun (fun xs x => x::xs) listCell [(0,20),(0,40)] =
      (_root_.Dijkstra.Store.accum (fun xs x => x::xs) listCell [(0,20),(0,40)],7) :=
  Resources.DijkstraStore.bulkRun_exact _ _ _

theorem repeated_bulk_observation :
    _root_.Dijkstra.Store.lookup
      (Resources.DijkstraStore.bulkRun (fun xs x => x::xs) listCell [(0,20),(0,40)]).1 0 = [40,20] := by
  rw [repeated_bulk]
  decide

theorem empty_bulk_copy : Resources.DijkstraStore.bulkRun (fun xs x => x::xs) listCell [] =
    (listCell,1) := by rw [Resources.DijkstraStore.bulkRun_exact]; rfl

def emptyFresh : State 1 := { start 0 with fresh := [] }

theorem empty_step : stepRun (noEdges 1) emptyFresh = (none,2) := rfl

theorem empty_run : runCost (noEdges 1) 0 emptyFresh = (some emptyFresh,1) ∧
    runCost (noEdges 1) 1 emptyFresh = (none,4) ∧
    runCost (noEdges 1) 2 emptyFresh = (none,5) := by
  simp only [runCost_zero, runCost_succ, empty_step]
  decide

theorem singleton_initialization : dijkstraRun (noEdges 1) 0 = (some (start 0),5) := rfl

theorem singleton_exhaustion : runCost (noEdges 1) 2 (start 0) = (none,14) ∧
    runCost (noEdges 1) 3 (start 0) = (none,15) := ⟨rfl,rfl⟩

theorem segmented_failure : segmentedRun (noEdges 1) 1 2 (start 0) = (none,15) := by
  rw [segmentedRun_exact]
  exact singleton_exhaustion.2

theorem arbitrary_segments (wa : Weights 3) (s : State 3) (k l : Nat) (hn : s.fresh.Nodup) :
    (segmentedRun wa k l s).1 = _root_.Dijkstra.Core.run wa (k+l) s ∧
    (segmentedRun wa k l s).2 ≤ (k+l)*(18*3+6)+1 :=
  ⟨segmentedRun_value _ _ _ _, segmentedRun_bound _ _ _ _ hn⟩

theorem figure_measured_distances :
    (dijkstraRun figureWeights 0).1.map distanceLabels =
      some [some 0,some 7,some 9,some 12,some 11,some 10] := by
  rw [dijkstraRun_value]
  exact figure_final_distances

theorem figure_measured_parents :
    (dijkstraRun figureWeights 0).1.map parentLabels = some [1,1,2,5,6,3] := by
  rw [dijkstraRun_value]
  decide

theorem figure_work_bounds : (dijkstraRun figureWeights 0).2 ≤ 585 ∧
    (dijkstraRun figureWeights 0).2 ≤ 1044 :=
  ⟨dijkstraRun_work _ _, dijkstraRun_quadratic _ _⟩

theorem figure_target_value : (targetRun (⟨figureWeights,0,3⟩ : Problem 6)).1 = some (some 12) := by
  rw [targetRun_value]
  exact congrArg some figure_composed_distances.1

theorem figure_measured_optimum :
    Search.Heuristic.DistanceResult (_root_.Dijkstra.Semantics.adjacency figureWeights)
      (_root_.Dijkstra.Semantics.goal 3) 0 (some 12) := by
  obtain ⟨d, he, hc⟩ := targetRun_correct (⟨figureWeights,0,3⟩ : Problem 6)
  have hd : d = some 12 := Option.some.inj (he.symm.trans figure_target_value)
  simpa only [hd] using hc

theorem figure_actual_queue :
    (queueRun (⟨figureWeights,0,3⟩ : Problem 6)).map (Option.map Search.Heuristic.Path.cost) =
      some (some 12) := by rw [← targetRun_queue, figure_target_value]

theorem disconnected_measured : (targetRun (⟨noEdges 3,0,2⟩ : Problem 3)).1 = some none ∧
    (targetRun (⟨noEdges 3,0,2⟩ : Problem 3)).2 ≤ 129 := by
  constructor
  · rw [targetRun_value]; rfl
  · exact targetRun_bound _

theorem zero_weight_measured : (targetRun (⟨zeroCycle,0,2⟩ : Problem 3)).1 = some (some 0) ∧
    (targetRun (⟨zeroCycle,0,2⟩ : Problem 3)).2 ≤ 129 := by
  constructor
  · rw [targetRun_value]; exact congrArg (fun p => some p.2) zero_cycle_simple
  · exact targetRun_bound _

theorem tied_measured_parent : (dijkstraRun tiedWeights 0).1.map (fun s => parent s 3) = some 1 := by
  rw [dijkstraRun_value]
  exact tied_old_parent.2

end Examples.DijkstraCosts
