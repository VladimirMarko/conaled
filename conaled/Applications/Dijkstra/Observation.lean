import Applications.Dijkstra.Semantics
import Applications.Dijkstra.Target
import Applications.Optimization.Relations
import Applications.Search.ExactPriority

/-! Total source observations preserve the matrix, root and destination. Witness
sets distinguish a genuine route from the source's unreachable singleton. The
second executor is the accepted closed search with zero heuristic and an exact
leftist queue; its distance is unique even when its tied witness differs. -/
set_option autoImplicit false
set_option warningAsError true
namespace Dijkstra.Observation
open Core Optimality Paths AllPaths Semantics
variable {n : Nat}

structure Problem (n : Nat) where
  weights : Weights n
  root : Fin n
  target : Fin n

abbrev Output (n : Nat) := List (Fin n) × Distance

/-- Independent ordered route evidence, or an explicit no-path singleton. -/
def Permitted (i : Problem n) (pd : Output n) : Prop :=
  match pd.2 with
  | some d => pd.1.Nodup ∧
      (∃ p, Search.Heuristic.Route (adjacency i.weights) i.root p ∧
        Search.Heuristic.extract p = (pd.1, d) ∧ p.vertex = i.target) ∧
      Search.Heuristic.DistanceResult (adjacency i.weights) (goal i.target) i.root (some d)
  | none => pd.1 = [i.target] ∧
      Search.Heuristic.DistanceResult (adjacency i.weights) (goal i.target) i.root none

/-- The fallback is proved unreachable by `final_exact`. -/
def final (wa : Weights n) (root : Fin n) : State n := (dijkstra wa root).getD (start root)

theorem final_exact (wa : Weights n) (root : Fin n) : dijkstra wa root = some (final wa root) := by
  obtain ⟨s, hs, _⟩ := dijkstra_correct wa root
  simp [final, hs]

theorem final_spec (wa : Weights n) (root : Fin n) :
    Parents wa root (final wa root) ∧ InfinitySelf (final wa root) ∧ Correct wa root (final wa root) := by
  obtain ⟨s, hs, hp, hi, hc, _⟩ := dijkstra_all_paths wa root
  simpa [final, hs] using And.intro hp (And.intro hi hc)

def result (i : Problem n) : Output n := pathValue (final i.weights i.root) i.target

theorem result_exact (i : Problem n) :
    (dijkstra i.weights i.root).bind (fun s => pathTo s i.target) = some (result i) := by
  rw [final_exact, Option.bind_some]
  exact pathValue_exact _ _ _ (final_spec _ _).1 (final_spec _ _).2.1 _

theorem result_permitted (i : Problem n) : Permitted i (result i) := by
  obtain ⟨hp, hi, hc⟩ := final_spec i.weights i.root
  cases hd : distance (final i.weights i.root) i.target with
  | none =>
      have he : result i = ([i.target], none) := by
        simp [result, pathValue, pathTo, getPath_self _ _ (hi _ hd), hd]
      rw [he]
      exact ⟨rfl, (no_path_iff _ _ _).mp ((hc.2 _).mp hd)⟩
  | some d =>
      obtain ⟨ps, hg, hn, hpath⟩ := reconstruct_finite _ _ _ hp _ _ hd
      have he : result i = (ps.reverse, some d) := by
        simp [result, pathValue, pathTo, hg, hd]
      rw [he]
      exact ⟨List.pairwise_reverse.mpr (hn.imp (fun h => Ne.symm h)),
        path_route hpath, (shortest_iff _ _ _ _).mp (hc.1 _ _ hd)⟩

theorem permitted_distance {i : Problem n} {pd : Output n} (h : Permitted i pd) :
    Search.Heuristic.DistanceResult (adjacency i.weights) (goal i.target) i.root pd.2 := by
  unfold Permitted at h
  cases hd : pd.2 <;> simp only [hd] at h
  case none => exact h.2
  case some d => exact h.2.2
def witnessSquare : Relational.RelSquare (Optimization.inputRep (Problem n))
    (Optimization.membershipRep (I := Problem n) (id : Output n → Output n)) where
  impl i := (i, result i)
  spec i := (i, {pd | Permitted i pd})
  preserves := by rintro i _ rfl; exact ⟨rfl, result_permitted i⟩

def distanceSquare : Relational.RelSquare (Optimization.inputRep (Problem n))
    (Optimization.membershipRep (I := Problem n) (id : Distance → Distance)) :=
  Relational.compose (Optimization.observationSquare Prod.snd) witnessSquare

theorem distanceSquare_correct (i : Problem n) :
    Search.Heuristic.DistanceResult (adjacency i.weights) (goal i.target) i.root
      (distanceSquare.impl i).2 := permitted_distance (result_permitted i)

theorem result_distance (i : Problem n) : (result i).2 = distance (final i.weights i.root) i.target :=
  (pathTo_endpoint _ _ _ (pathValue_exact _ _ _ (final_spec _ _).1 (final_spec _ _).2.1 _)).2

/-- Total first-hit interface; the fallback is excluded by `targetResult_exact`. -/
def targetResult (i : Problem n) : Output n := (Target.dijkstraZ i.weights i.root i.target).getD ([], none)

theorem targetResult_exact (i : Problem n) :
    Target.dijkstraZ i.weights i.root i.target = some (targetResult i) := by
  obtain ⟨ps, d, he, _⟩ := Target.dijkstraZ_total i.weights i.root i.target
  simp [targetResult, he]

theorem targetResult_permitted (i : Problem n) : Permitted i (targetResult i) := by
  obtain ⟨ps, d, he, hc⟩ := Target.dijkstraZ_total i.weights i.root i.target
  have ht : targetResult i = (ps, d) := by simp [targetResult, he]
  rw [ht]
  cases d with
  | none => exact ⟨hc.1, (no_path_iff _ _ _).mp hc.2⟩
  | some d => exact ⟨hc.1, path_route hc.2.1, (shortest_iff _ _ _ _).mp hc.2.2⟩

theorem target_distance_eq (i : Problem n) : (targetResult i).2 = (result i).2 :=
  (permitted_distance (targetResult_permitted i)).unique (permitted_distance (result_permitted i))

/-- Actual accepted exact-occurrence queue, viewed through its weaker keyed laws. -/
def queue (n : Nat) : Search.Heuristic.Frontier (Fin n) :=
  Search.PriorityInterface.exactLeftist.keyed Search.Heuristic.Path.vertex

def queueRun (i : Problem n) : Option (Option (Search.Heuristic.Path (Fin n))) :=
  Search.Heuristic.run (queue n) .closed (adjacency i.weights) (fun _ => 0) (goal i.target)
    (Search.Heuristic.closedBudget (List.finRange n) n) []
    (Search.Heuristic.start (queue n) (fun _ => 0) i.root)

theorem queueRun_completed (i : Problem n) : ∃ out, queueRun i = some out :=
  Search.Heuristic.mstar_terminates (queue n) (adjacency i.weights) (fun _ => 0) (goal i.target)
    (List.finRange n) n i.root (List.mem_finRange _) (fun _ _ v _ _ => List.mem_finRange v)
    (fun v _ => adjacency_length i.weights v)

def queueResult (i : Problem n) : Option (Search.Heuristic.Path (Fin n)) := (queueRun i).getD none

theorem queueResult_exact (i : Problem n) : queueRun i = some (queueResult i) := by
  obtain ⟨out, he⟩ := queueRun_completed i
  simp [queueResult, he]

theorem queueResult_correct (i : Problem n) :
    Search.Heuristic.CorrectResult (adjacency i.weights) (goal i.target) i.root (queueResult i) :=
  Search.Heuristic.mstar_correct (queue n) (adjacency i.weights) (fun _ => 0) (goal i.target)
    i.root (Search.Heuristic.zero_monotonic _) (fun _ _ => rfl) _ (queueResult_exact i)

theorem queue_distance_eq (i : Problem n) :
    (queueResult i).map Search.Heuristic.Path.cost = (result i).2 :=
  ((Search.Heuristic.observeDistance _ _ _).preserves (s := ()) (queueResult_correct i)).unique
    (permitted_distance (result_permitted i))

/-- Whole output in source vertex order, rather than a set of target observations. -/
def allResults (wa : Weights n) (root : Fin n) : List (Output n) :=
  (List.finRange n).map (fun v => result ⟨wa, root, v⟩)

theorem allResults_exact (wa : Weights n) (root : Fin n) :
    (dijkstra wa root).bind extractPaths = some (allResults wa root) := by
  rw [final_exact, Option.bind_some]
  exact extractPaths_exact _ _ _ (final_spec _ _).1 (final_spec _ _).2.1

def allWitnessSquare : Relational.RelSquare (Optimization.inputRep (Weights n × Fin n))
    (Optimization.membershipRep (I := Weights n × Fin n)
      (id : List (Output n) → List (Output n))) where
  impl i := (i, allResults i.1 i.2)
  spec i := (i, {ps | List.Forall₂ (fun v pd => Permitted ⟨i.1, i.2, v⟩ pd) (List.finRange n) ps})
  preserves := by
    rintro i _ rfl
    refine ⟨rfl, ?_⟩
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun v _ => result_permitted ⟨i.1, i.2, v⟩))

def allDistanceSquare : Relational.RelSquare (Optimization.inputRep (Weights n × Fin n))
    (Optimization.membershipRep (I := Weights n × Fin n) (id : List Distance → List Distance)) :=
  Relational.compose (Optimization.observationSquare (List.map Prod.snd)) allWitnessSquare

theorem allDistanceSquare_correct (wa : Weights n) (root : Fin n) :
    List.Forall₂ (fun v d => Search.Heuristic.DistanceResult (adjacency wa) (goal v) root d)
      (List.finRange n) (allDistanceSquare.impl (wa, root)).2 := by
  change List.Forall₂ _ _ ((allResults wa root).map Prod.snd)
  simp only [allResults, List.map_map]
  exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
    (fun v _ => permitted_distance (result_permitted ⟨wa, root, v⟩)))

theorem allDistanceSquare_exact (wa : Weights n) (root : Fin n) :
    (allDistanceSquare.impl (wa, root)).2 =
      (List.finRange n).map (fun v => (queueResult ⟨wa, root, v⟩).map Search.Heuristic.Path.cost) := by
  change (allResults wa root).map Prod.snd = _
  simp only [allResults, List.map_map]
  apply List.map_congr_left
  intro v _
  exact (queue_distance_eq ⟨wa, root, v⟩).symm

end Dijkstra.Observation
