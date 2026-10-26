import Applications.Dijkstra.Sentinel.Observation
import Examples.Dijkstra

/-! Safe finite-sentinel execution, retained source figures, and unsafe-domain boundaries. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.DijkstraSentinel
open _root_.Dijkstra.Core _root_.Dijkstra.Optimality _root_.Dijkstra.Paths
open _root_.Dijkstra.Sentinel
open Examples.Dijkstra (figureWeights figureDistance figure_all_shortest parentLabels distanceLabels)

theorem figure_bound : EdgeBound figureWeights 11 := by
  have ht : ∀ u v, (figureWeights u v).getD 0 ≤ 11 := by decide
  intro u v w hw
  have h := ht u v
  simpa only [hw,Option.getD_some] using h

theorem figure_reachable : Reachable figureWeights 0 :=
  fun v => ⟨figureDistance v, (figure_all_shortest v).1⟩

def figure : SafeProblem 6 := ⟨figureWeights,0,11,100,figure_bound,by decide,figure_reachable⟩

/-- The whole raw vector is obtained through the composed accepted-vector consumer. -/
theorem figure_raw_vector : allDistances.impl figure = some [0,7,9,12,11,10] := by
  rw [allDistances_exact]
  change some ((_root_.Dijkstra.Observation.allDistanceSquare.impl (figureWeights,(0 : Fin 6))).2.map
    (encode 100)) = _
  rw [Examples.Dijkstra.figure_composed_distances.2]
  rfl

theorem figure_raw_parents : allParents.impl figure = some [0,0,1,4,5,2] := by
  rw [allParents_exact]
  have hp : (dijkstra figureWeights (0 : Fin 6)).map
      (fun s => (List.finRange 6).map (parent s)) = some [0,0,1,4,5,2] := by decide
  rw [_root_.Dijkstra.Observation.final_exact] at hp
  exact hp

/-- Both vectors of the original finite-source example, with the one-based labels restored. -/
theorem figure_finite_source :
    (rawDijkstra 100 (encodeWeights 100 figureWeights) (0 : Fin 6)).map
      (fun s => (List.finRange 6).map (rawDistance s)) = some [0,7,9,12,11,10] ∧
    (rawDijkstra 100 (encodeWeights 100 figureWeights) (0 : Fin 6)).map
      (fun s => (List.finRange 6).map (fun v => (rawParent s v).val+1)) =
      some [1,1,2,5,6,3] := by
  refine ⟨figure_raw_vector,?_⟩
  have hp := congrArg (Option.map (List.map (fun v : Fin 6 => v.val+1))) figure_raw_parents
  simpa [allParents,Squares.compose,observationSquare,executionSquare,figure,
    Option.map_map,List.map_map,Function.comp_def] using hp

example : (targetDistance (3 : Fin 6)).impl figure =
    (_root_.Dijkstra.Observation.queueRun ⟨figureWeights,0,3⟩).map
      (fun p => encode 100 (p.map Search.Heuristic.Path.cost)) := targetDistance_queue figure 3

example : (targetDistance (3 : Fin 6)).impl figure = some 12 := by
  rw [targetDistance_queue,_root_.Dijkstra.Observation.queueResult_exact]
  simp only [Option.map_some,_root_.Dijkstra.Observation.queue_distance_eq]
  have h := Examples.Dijkstra.figure_composed_distances.1
  change (_root_.Dijkstra.Observation.result ⟨figureWeights,0,3⟩).2 = some 12 at h
  change some (encode 100 (_root_.Dijkstra.Observation.result ⟨figureWeights,0,3⟩).2) = _
  rw [h]
  rfl

example : ∃ d : Nat, (targetDistance (3 : Fin 6)).impl figure = some (d : Int) ∧
    Search.Heuristic.DistanceResult (_root_.Dijkstra.Semantics.adjacency figureWeights)
      (_root_.Dijkstra.Semantics.goal 3) 0 (some d) := targetDistance_shortest figure 3

-- Three zero-weight edges give tied alternatives to vertex two.
def zeros : Weights 3 := fun u v => if (u=0 ∧ (v=1 ∨ v=2)) ∨ (u=1 ∧ v=2) then some 0 else none

theorem zeros_bound : EdgeBound zeros 0 := by
  intro u v w hw
  unfold zeros at hw
  split at hw <;> simp_all

theorem zeros_reachable : Reachable zeros 0 := by
  intro v
  have hv : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases hv with rfl | rfl | rfl
  · exact ⟨0,.nil⟩
  · exact ⟨0,.snoc .nil (by decide : zeros 0 1=some 0)⟩
  · exact ⟨0,.snoc .nil (by decide : zeros 0 2=some 0)⟩

def zeroProblem : SafeProblem 3 := ⟨zeros,0,0,1,zeros_bound,by decide,zeros_reachable⟩

example : executionSquare.impl zeroProblem =
    (dijkstra zeros 0).map (encodeState 1) := executionSquare.commutes zeroProblem
example : allDistances.impl zeroProblem = some [0,0,0] := by
  rw [allDistances_exact]
  decide
example : allParents.impl zeroProblem = some [0,0,0] := by
  rw [allParents_exact]
  decide
example : (targetDistance (2 : Fin 3)).impl zeroProblem =
    (_root_.Dijkstra.Observation.queueRun ⟨zeros,0,2⟩).map
      (fun p => encode 1 (p.map Search.Heuristic.Path.cost)) := targetDistance_queue zeroProblem 2

example (a b : Fin 3) (d : Int) : rawBetter (a,d) (b,d) = (a,d) := by
  simp [rawBetter]

-- A singleton executes zero Dijkstra updates, but arbitrary overlong runs still fail.
def singleton : SafeProblem 1 where
  weights := fun _ _ => none
  root := 0
  bound := 0
  sentinel := 1
  edgeBound := by intro _ _ _ h; cases h
  range := by decide
  reachable := by intro v; have hv : v=0 := Subsingleton.elim _ _; subst v; exact ⟨0,.nil⟩
example : allDistances.impl singleton = some [0] := by rw [allDistances_exact]; decide
example : allParents.impl singleton = some [0] := by rw [allParents_exact]; decide
example (S : Int) (wa : RawWeights 1) (s : RawState 1) : rawRun S wa 0 s = some s := rfl
example : rawRun 1 (encodeWeights 1 singleton.weights) 2 (rawStart 1 (0 : Fin 1)) = none := by decide
example : (targetDistance (0 : Fin 1)).impl singleton = some 0 := by
  change (executionSquare.impl singleton).map (fun s => rawDistance s 0) = _
  rw [execution_exact,Option.map_some,encode_distance]
  change some (encode 1 (distance (start (0 : Fin 1)) 0)) = some 0
  rw [start_distance]
  rfl

def emptyRaw : RawState 0 := ⟨Vector.ofFn (fun v => Fin.elim0 v),[]⟩
example : rawStep 1 (fun v _ => Fin.elim0 v) emptyRaw = none := rfl

-- Completed no-path is an inner none; it is not an exhausted outer run.
example : _root_.Dijkstra.Observation.queueRun ⟨Examples.Dijkstra.noEdges 3,0,2⟩ = some none := by
  rw [_root_.Dijkstra.Observation.queueResult_exact]
  apply congrArg some
  have h := Examples.Dijkstra.disconnected_queue_agreement
  cases he : _root_.Dijkstra.Observation.queueResult ⟨Examples.Dijkstra.noEdges 3,0,2⟩ with
  | none => rfl
  | some p => rw [he] at h; contradiction

-- A selected sentinel and a missing edge are different source branches.
example : rawSum 10 10 1 = 11 := (unguarded_infinity 10 (by decide)).1
example : rawSum 10 10 1 ≠ encode 10 (plus none (some 1)) :=
  (unguarded_infinity 10 (by decide)).2
example (d : Int) : rawSum 10 d 10 = 10 := by simp [rawSum]
example : encode 10 (some 10) = encode 10 none ∧ (some 10 : Distance) ≠ none := sentinel_collision 10

-- Reachability alone does not avoid a finite/sentinel collision.
def collision : Weights 2 := fun u v => if u=0 ∧ v=1 then some 10 else none

theorem collision_reachable : Reachable collision 0 := by
  intro v
  have hv : v=0 ∨ v=1 := by omega
  rcases hv with rfl | rfl
  · exact ⟨0,.nil⟩
  · exact ⟨10,.snoc .nil (by decide : collision 0 1=some 10)⟩

theorem collision_parent :
    (rawDijkstra 10 (encodeWeights 10 collision) (0 : Fin 2)).map (fun s => rawParent s 1)=some 1 ∧
    (dijkstra collision 0).map (fun s => parent s 1)=some 0 := by decide

example : rawDijkstra 10 (encodeWeights 10 collision) (0 : Fin 2) ≠
    (dijkstra collision 0).map (encodeState 10) := by
  intro he
  have hp := congrArg (Option.map (fun s => rawParent s 1)) he
  rw [collision_parent.1] at hp
  have hf : (fun s : State 2 => rawParent (encodeState 10 s) 1) = fun s => parent s 1 :=
    funext (fun s => encode_parent 10 s 1)
  rw [Option.map_map] at hp
  change some (1 : Fin 2) = (dijkstra collision 0).map (fun s => rawParent (encodeState 10 s) 1) at hp
  rw [hf,collision_parent.2] at hp
  contradiction

example : rawSum 9 4 4 = (4 : Int)+4 ∧ 0 ≤ rawSum 9 4 4 ∧ rawSum 9 4 4 < 9 :=
  relaxation_addition_range (0 : Fin 2) 4 9 4 4 (by decide) (by decide) (by decide)
example : 0 ≤ (4 : Int)+4+4 ∧ (4 : Int)+4+4 < 13 :=
  jogger_addition_range (0 : Fin 2) 4 13 4 4 4 (by decide) (by decide) (by decide) (by decide)

end Examples.DijkstraSentinel
