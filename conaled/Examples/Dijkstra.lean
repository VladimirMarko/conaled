import Applications.Dijkstra.Observation

/-! Checked source figures and boundary applications of the public Dijkstra
contracts, including actual zero-heuristic queue agreement. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.Dijkstra
open _root_.Dijkstra.Core _root_.Dijkstra.Optimality _root_.Dijkstra.Paths
open _root_.Dijkstra.AllPaths _root_.Dijkstra.Target _root_.Dijkstra.Semantics
open _root_.Dijkstra.Observation
variable {n : Nat}

def parentLabels (s : State n) : List Nat :=
  (List.finRange n).map (fun v => (parent s v).val+1)

def distanceLabels (s : State n) : List Distance := (List.finRange n).map (distance s)

def figureWeights : Weights 6 := fun u v =>
  match u.val,v.val with
  | 0,1 => some 7 | 0,2 => some 10
  | 1,2 => some 2 | 1,3 => some 9
  | 2,3 => some 11 | 2,4 => some 4 | 2,5 => some 1
  | 3,0 => some 2 | 4,3 => some 1 | 5,3 => some 6 | 5,4 => some 1
  | _,_ => none

def snapshot (s : State 6) : List Nat × List Distance × Option Nat :=
  (parentLabels s,distanceLabels s,(choose s).map (fun v => v.val+1))


theorem figure_successive_arrays :
    (List.range 6).map (fun k => (run figureWeights k (start (0 : Fin 6))).map snapshot)=
    [some ([1,2,3,4,5,6],[some 0,none,none,none,none,none],some 1),
     some ([1,1,1,4,5,6],[some 0,some 7,some 10,none,none,none],some 2),
     some ([1,1,2,2,5,6],[some 0,some 7,some 9,some 16,none,none],some 3),
     some ([1,1,2,2,3,3],[some 0,some 7,some 9,some 16,some 13,some 10],some 6),
     some ([1,1,2,2,6,3],[some 0,some 7,some 9,some 16,some 11,some 10],some 5),
     some ([1,1,2,5,6,3],[some 0,some 7,some 9,some 12,some 11,some 10],some 4)] := by decide

theorem figure_final_distances :
    (dijkstra figureWeights (0 : Fin 6)).map distanceLabels=
      some [some 0,some 7,some 9,some 12,some 11,some 10] := by decide

theorem figure_five_steps_leave_one_fresh :
    (start (0 : Fin 6)).fresh.length=6 ∧
    (dijkstra figureWeights (0 : Fin 6)).map (fun s => s.fresh)=some [3] ∧
    (run figureWeights 6 (start (0 : Fin 6))).map parentLabels=
      (dijkstra figureWeights (0 : Fin 6)).map parentLabels ∧
    (run figureWeights 6 (start (0 : Fin 6))).map distanceLabels=
      (dijkstra figureWeights (0 : Fin 6)).map distanceLabels := by decide

def figureDistance (v : Fin 6) : Nat :=
  match v.val with | 0 => 0 | 1 => 7 | 2 => 9 | 3 => 12 | 4 => 11 | _ => 10

theorem figure_all_shortest (v : Fin 6) : Shortest figureWeights 0 v (figureDistance v) := by
  obtain ⟨s,hs,_,_,hc⟩ := dijkstra_correct figureWeights (0 : Fin 6)
  have h : ∀u,(dijkstra figureWeights (0 : Fin 6)).map (fun t => distance t u)=
      some (some (figureDistance u)) := by decide
  have hd := h v
  rw [hs,Option.map_some] at hd
  exact hc.1 v _ (Option.some.inj hd)

theorem figure_path_to_four :
    (dijkstra figureWeights (0 : Fin 6)).bind (fun s => pathTo s 3)=
      some ([0,1,2,5,4,3],some 12) := by decide

theorem figure_path_to_four_independent :
    Path figureWeights 0 [0,1,2,5,4,3] 3 12 ∧ Shortest figureWeights 0 3 12 := by
  refine ⟨?_,figure_all_shortest 3⟩
  exact .snoc (.snoc (.snoc (.snoc (.snoc .nil
    (by decide : figureWeights 0 1=some 7))
    (by decide : figureWeights 1 2=some 2))
    (by decide : figureWeights 2 5=some 1))
    (by decide : figureWeights 5 4=some 1))
    (by decide : figureWeights 4 3=some 1)

theorem figure_all_paths :
    (dijkstra figureWeights (0 : Fin 6)).bind extractPaths=
      some [([0],some 0),([0,1],some 7),([0,1,2],some 9),
        ([0,1,2,5,4,3],some 12),([0,1,2,5,4],some 11),([0,1,2,5],some 10)] := by decide


/-- Source figure witness transported with its exact forward sequence. -/
theorem figure_accepted_route :
    ∃ p, Search.Heuristic.Route (adjacency figureWeights) 0 p ∧
      Search.Heuristic.extract p = ([0,1,2,5,4,3],12) ∧ p.vertex = 3 :=
  path_route figure_path_to_four_independent.1

theorem figure_accepted_shortest (v : Fin 6) :
    Search.Heuristic.DistanceResult (adjacency figureWeights) (goal v) 0 (some (figureDistance v)) :=
  (shortest_iff _ _ _ _).mp (figure_all_shortest v)

theorem figure_composed_distances :
    (distanceSquare.impl (⟨figureWeights, 0, 3⟩ : Problem 6)).2 = some 12 ∧
    (allDistanceSquare.impl (figureWeights, (0 : Fin 6))).2 =
      [some 0, some 7, some 9, some 12, some 11, some 10] := by decide

theorem figure_vector_contract :
    List.Forall₂ (fun v d => Search.Heuristic.DistanceResult (adjacency figureWeights) (goal v) 0 d)
      (List.finRange 6) (allDistanceSquare.impl (figureWeights, (0 : Fin 6))).2 :=
  allDistanceSquare_correct figureWeights 0

theorem figure_queue_vector :
    (allDistanceSquare.impl (figureWeights, (0 : Fin 6))).2 =
      (List.finRange 6).map (fun v => (queueResult ⟨figureWeights, 0, v⟩).map Search.Heuristic.Path.cost) :=
  allDistanceSquare_exact figureWeights 0

def noEdges (n : Nat) : Weights n := fun _ _ => none

theorem singleton_exact :
    (dijkstra (noEdges 1) 0).map (fun s => s.fresh) = some [0] ∧
    dijkstraZ (noEdges 1) 0 0 = some ([0], some 0) ∧
    (untilTarget (noEdges 1) 0 1 (start 0)).map (fun s => s.fresh) = some [] ∧
    untilTarget (noEdges 1) 0 0 (start 0) = none := by decide

theorem singleton_first_hit :
    ∃ out, untilTarget (noEdges 1) 0 1 (start 0) = some out ∧
      Iteration.UntilSpec (done 0) (stepTotal (noEdges 1)) (start 0) out := by
  obtain ⟨out, he, hs, _⟩ := dijkstraZ_first_hit (noEdges 1) 0 0
  exact ⟨out, he, hs⟩

theorem disconnected_exact :
    allResults (noEdges 3) 0 = [([0], some 0), ([1], none), ([2], none)] ∧
    dijkstraZ (noEdges 3) 0 2 = some ([2], none) ∧
    (dijkstra (noEdges 3) 0).map (fun s => s.fresh) = some [2] := by decide

theorem disconnected_no_path :
    Search.Heuristic.DistanceResult (adjacency (noEdges 3)) (goal 2) 0 none := by
  have h := distanceSquare_correct (⟨noEdges 3, 0, 2⟩ : Problem 3)
  exact h

theorem disconnected_placeholder_contract : Permitted (⟨noEdges 3, 0, 2⟩ : Problem 3) ([2], none) := by
  have h := result_permitted (⟨noEdges 3, 0, 2⟩ : Problem 3)
  exact h

theorem disconnected_queue_agreement :
    (queueResult (⟨noEdges 3, 0, 2⟩ : Problem 3)).map Search.Heuristic.Path.cost = none :=
  queue_distance_eq ⟨noEdges 3, 0, 2⟩

def tiedWeights : Weights 4 := fun u v =>
  if (u = 0 ∧ (v = 1 ∨ v = 2)) ∨ ((u = 1 ∨ u = 2) ∧ v = 3) then some 1 else none

theorem tied_old_parent : result (⟨tiedWeights, 0, 3⟩ : Problem 4) = ([0,1,3], some 2) ∧
    (dijkstra tiedWeights 0).map (fun s => parent s 3) = some 1 := by decide

theorem tied_queue_agreement :
    (queueResult (⟨tiedWeights, 0, 3⟩ : Problem 4)).map Search.Heuristic.Path.cost = some 2 :=
  queue_distance_eq ⟨tiedWeights, 0, 3⟩

theorem tied_target_agreement :
    (targetResult (⟨tiedWeights, 0, 3⟩ : Problem 4)).2 = (result (⟨tiedWeights, 0, 3⟩ : Problem 4)).2 :=
  target_distance_eq _

def reversedFresh : State 3 := ⟨Vector.ofFn (fun v => (v, some 4)), [2,1,0]⟩

theorem rank_tie_order : choose reversedFresh = some 0 ∧
    better ((2 : Fin 3), some 4) (0, some 4) = (2, some 4) := by decide

theorem rank_tie_certificate :
    Optimization.FirstMinimum (score reversedFresh) reversedFresh.fresh 0 :=
  (choose_first reversedFresh 0).mp rank_tie_order.1

def zeroCycle : Weights 3 := fun u v =>
  if (u = 0 ∧ v = 1) ∨ (u = 1 ∧ (v = 0 ∨ v = 2)) then some 0 else none

theorem zero_cycle_simple : result (⟨zeroCycle, 0, 2⟩ : Problem 3) = ([0,1,2], some 0) := by decide

theorem zero_cycle_optimum :
    Search.Heuristic.DistanceResult (adjacency zeroCycle) (goal 2) 0 (some 0) :=
  distanceSquare_correct ⟨zeroCycle, 0, 2⟩

def cyclicParents : State 2 := ⟨Vector.ofFn (fun v => (if v = 0 then 1 else 0, some 0)), []⟩

theorem malformed_failures :
    getPathFuel cyclicParents 0 0 = none ∧ getPath cyclicParents 0 = none ∧
    choose cyclicParents = none ∧ (step (noEdges 2) cyclicParents).isNone = true ∧
    (run (noEdges 2) 0 cyclicParents).isSome = true ∧
    (run (noEdges 2) 1 cyclicParents).isNone = true := by decide

theorem finite_fuel_boundary :
    getPathFuel (final figureWeights 0) 5 3 = none ∧
    getPathFuel (final figureWeights 0) 6 3 = some [3,4,5,2,1,0] ∧
    (run figureWeights 6 (start 0)).map (fun s => s.fresh) = some [] ∧
    (run figureWeights 7 (start 0)).isNone = true := by decide

theorem figure_filtered_lookup :
    (extractPaths (final figureWeights 0)).bind (pathByLast 3) = pathTo (final figureWeights 0) 3 :=
  pathByLast_exact _ _ _ (final_spec _ _).1 (final_spec _ _).2.1 _

/-- Repeated updates preserve left-to-right noncommutative accumulation. -/
theorem repeated_store_updates :
    _root_.Dijkstra.Store.lookup
      (_root_.Dijkstra.Store.accum (fun a b : Nat => 10 * a + b)
        (Vector.ofFn (fun _ : Fin 1 => 0)) [(0,1),(0,2),(0,3)]) 0 = 123 := by decide

theorem repeated_store_observation :
    _root_.Dijkstra.Store.lookup
      (_root_.Dijkstra.Store.accum (fun a b : Nat => 10 * a + b)
        (Vector.ofFn (fun _ : Fin 1 => 0)) [(0,1),(0,2),(0,3)]) 0 =
    (_root_.Dijkstra.Store.valuesAt (0 : Fin 1) [(0,1),(0,2),(0,3)]).foldl
      (fun a b : Nat => 10 * a + b) 0 :=
  _root_.Dijkstra.Store.accum_lookup _ _ _ _

end Examples.Dijkstra
