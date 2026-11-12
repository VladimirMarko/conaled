import Applications.Search.Incremental.Fresh

/-! Independent distance fixtures and the actual fresh rational A* comparator. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.IncrementalSearchSemantics
open Search.Incremental

def disconnected : Graph 3 := fun u v =>
  if u=v then (1 : ℚ) else if u=0 ∧ v=1 then ((2/7 : ℚ) : Cost) else ⊤

def distances : Labels 3 := fun v => if v=0 then 0 else if v=1 then ((2/7 : ℚ) : Cost) else ⊤

def heuristic : Fin 3 → ℚ := fun v => if v=0 then 2/7 else 0

theorem disconnected_positive : Positive disconnected := by unfold Positive; decide +kernel
theorem distances_nonnegative : Nonnegative distances := by unfold Nonnegative; decide +kernel
theorem distances_bellman : Bellman disconnected 0 distances := by unfold Bellman; decide +kernel
theorem heuristic_consistent : ConsistentHeuristic disconnected 1 heuristic := by unfold ConsistentHeuristic; decide +kernel

/-- Bellman attainment gives an actual finite walk with the fractional cost. -/
example : Search.RationalCost.Walk (adjacency disconnected) 0 1 (2/7) :=
  bellman_attains disconnected_positive distances_bellman 1 (2/7) rfl

/-- Infinity means no finite walk; it is not an unattained finite optimum. -/
example : DistanceResult disconnected 0 2 ⊤ :=
  bellman_correct disconnected_positive distances_nonnegative distances_bellman 2

example : DistanceResult disconnected 0 0 0 :=
  bellman_correct disconnected_positive distances_nonnegative distances_bellman 0

example : Fresh.result disconnected heuristic 0 1 = ((2/7 : ℚ) : Cost) :=
  distance_unique (Fresh.result_correct disconnected_positive heuristic_consistent 0)
    (bellman_correct disconnected_positive distances_nonnegative distances_bellman 1)

example : Fresh.result disconnected (fun _ => 0) 0 2 = ⊤ :=
  distance_unique (Fresh.result_correct disconnected_positive
    (show ConsistentHeuristic disconnected 2 (fun _ => 0) by unfold ConsistentHeuristic; decide +kernel) 0)
    (bellman_correct disconnected_positive distances_nonnegative distances_bellman 2)

example : DistanceResult disconnected 0 1 (Fresh.result disconnected heuristic 0 1) :=
  Fresh.result_correct disconnected_positive heuristic_consistent 0

example : Fresh.result disconnected heuristic 0 1 = distances 1 :=
  distance_unique (Fresh.result_correct disconnected_positive heuristic_consistent 0)
    (bellman_correct disconnected_positive distances_nonnegative distances_bellman 1)

/-- Equal shortest routes 0-1-3 and 0-2-3 have cost 1/3+2/5=11/15. -/
def ties : Graph 4 := fun u v =>
  if u=v then (1 : ℚ) else
  if u=0 ∧ (v=1 ∨ v=2) then ((1/3 : ℚ) : Cost) else
  if (u=1 ∨ u=2) ∧ v=3 then ((2/5 : ℚ) : Cost) else ⊤

def tieHeuristic : Fin 4 → ℚ := fun u => if u=0 then 11/15 else if u=3 then 0 else 2/5

theorem ties_positive : Positive ties := by unfold Positive; decide +kernel
theorem tieHeuristic_consistent : ConsistentHeuristic ties 3 tieHeuristic := by unfold ConsistentHeuristic; decide +kernel

def tieDistances : Labels 4 := fun v => if v=0 then 0 else if v=3 then ((11/15 : ℚ) : Cost) else ((1/3 : ℚ) : Cost)
theorem tieDistances_nonnegative : Nonnegative tieDistances := by unfold Nonnegative; decide +kernel
theorem tieDistances_bellman : Bellman ties 0 tieDistances := by unfold Bellman; decide +kernel

example : Fresh.result ties tieHeuristic 0 3 = ((11/15 : ℚ) : Cost) :=
  distance_unique (Fresh.result_correct ties_positive tieHeuristic_consistent 0)
    (bellman_correct ties_positive tieDistances_nonnegative tieDistances_bellman 3)

example : DistanceResult ties 0 3 (Fresh.result ties tieHeuristic 0 3) :=
  Fresh.result_correct ties_positive tieHeuristic_consistent 0

/-- A query-specific scale admits any new denominator, without an old-scale premise. -/
example (q : ℚ) (hq : 0 ≤ q) : (Fresh.scale [q]).Fits q :=
  Fresh.scale_fits [q] q (by simp) hq

/-- Run the actual per-query preparation and bounded search, separately from
kernel proofs of its independent observation. -/
def runtimeChecks : IO Unit := do
  unless Fresh.result disconnected heuristic 0 1 == ((2/7 : ℚ) : Cost) do
    throw (IO.userError "fresh fractional reachable distance")
  unless Fresh.result disconnected (fun _ => 0) 0 2 == (⊤ : Cost) do
    throw (IO.userError "fresh unreachable distance")
  unless Fresh.result disconnected (fun _ => 0) 0 0 == (0 : Cost) do
    throw (IO.userError "fresh start equals goal")
  unless Fresh.result ties tieHeuristic 0 3 == ((11/15 : ℚ) : Cost) do
    throw (IO.userError "fresh equal-route nonzero heuristic")
  IO.println "four fresh rational search fixtures passed"

end Examples.IncrementalSearchSemantics
