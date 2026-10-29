import Applications.Parallel.ScanSearch
import Examples.MeasuredScan

/-! Bounded scan search, loss of coarse boundary information, and checked selectors. -/
namespace Examples.ScanSearch
open Applications.Parallel Applications.Parallel.ScanSearch
open Optimization Optimization.Thinning
open ScanPlan (pair bush)

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open MeasuredScan

def catalog : List ScanPlan :=
  [pair.rightPow 4, mixed, bush 2, pairBlocks, pair.leftPow 4, fourBlocks]

theorem catalog_size : ∀ p ∈ catalog, p.shape.size = 16 := by
  intro p hp
  simp only [catalog, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem catalog_coverage (p : ScanPlan) (hp : p ∈ catalog) :
    Grammar [] catalog 0 0 ⟨0,p⟩ := .seed p hp

/-- No continuation frames are used for the six-plan comparison. -/
def retained : List Candidate := search [] catalog 0

theorem minimum_work_selected : argmin work retained = some ⟨0,fourBlocks⟩ := by decide

theorem minimum_work :
    (⟨0,fourBlocks⟩ : Candidate) ∈ minimizers {a | a ∈ generate [] catalog 0} work :=
  selected_work [] catalog 0 _ minimum_work_selected

theorem deadline_selected : argmin work (feasible 4 retained) = some ⟨0,mixed⟩ := by decide

theorem deadline_minimum :
    (⟨0,mixed⟩ : Candidate) ∈ minimizers {a | a ∈ feasible 4 (generate [] catalog 0)} work :=
  selected_deadline [] catalog 0 4 _ deadline_selected

theorem balanced_selected : argmin (weighted 1 1) retained = some ⟨0,fourBlocks⟩ := by decide

theorem balanced_minimum :
    (⟨0,fourBlocks⟩ : Candidate) ∈ minimizers {a | a ∈ generate [] catalog 0} (weighted 1 1) :=
  selected_weighted [] catalog 0 1 1 _ balanced_selected

theorem depth_emphasis_selected : argmin (weighted 1 10) retained = some ⟨0,mixed⟩ := by decide

theorem depth_emphasis_minimum :
    (⟨0,mixed⟩ : Candidate) ∈ minimizers {a | a ∈ generate [] catalog 0} (weighted 1 10) :=
  selected_weighted [] catalog 0 1 10 _ depth_emphasis_selected

theorem mixed_pareto :
    (⟨0,mixed⟩ : Candidate) ∈ pareto {a | a ∈ generate [] catalog 0} costs :=
  pareto_of_search [] catalog 0 _
    (weighted_pareto (by decide) (by decide)
      (argmin_correct (weighted 1 10) retained _ depth_emphasis_selected))

def balancedFour : ScanPlan := .prod pair pair
def coarseA : ScanPlan := .prod balancedFour sequentialFour
def coarseB : ScanPlan := .comp balancedFour pair

def coarse (a b : ScanPlan) : Prop := a.work ≤ b.work ∧ a.depth ≤ b.depth
instance (a b : ScanPlan) : Decidable (coarse a b) := by unfold coarse; infer_instance

theorem coarse_tie :
    (coarseA.work, coarseA.depth) = (11,4) ∧ (coarseB.work, coarseB.depth) = (11,4) := by decide

theorem coarse_arrivals :
    coarseA.arrivals (fun _ => 0) = [0,0,1,2,2,3,3,3,4] ∧
    coarseB.arrivals (fun _ => 0) = [0,0,1,2,2,3,3,4,3] := by decide

theorem coarse_pruning_loses :
    thinBy coarse [coarseA,coarseB] = [coarseA] ∧
    (ScanPlan.prod coarseA .leaf).depth = 5 ∧
    (ScanPlan.prod coarseB .leaf).depth = 4 := by decide

def appendLeaf : List Frame := [.prodLeft .leaf]

theorem richer_retains :
    prune appendLeaf [⟨1,coarseA⟩,⟨1,coarseB⟩] = [⟨1,coarseA⟩,⟨1,coarseB⟩] := by decide

/-- Both alternatives survive until the supported enclosing context is measured. -/
theorem richer_selects :
    argmin work (feasible 4 (search appendLeaf [coarseA,coarseB] 1)) =
      some ⟨0,.prod coarseB .leaf⟩ := by decide

theorem richer_correct :
    (⟨0,.prod coarseB .leaf⟩ : Candidate) ∈
      minimizers {a | a ∈ feasible 4 (generate appendLeaf [coarseA,coarseB] 1)} work :=
  selected_deadline appendLeaf [coarseA,coarseB] 1 4 _ richer_selects

/-- A syntax-distinct identity wrapper is safely removed even before extension. -/
def wrappedPair : ScanPlan := .comp .leaf pair

theorem positive_replacement : Dominates appendLeaf ⟨1,pair⟩ ⟨1,wrappedPair⟩ := by decide

theorem positive_extended :
    Covers (Dominates appendLeaf)
      (extend appendLeaf ⟨1,pair⟩) (extend appendLeaf ⟨1,wrappedPair⟩) :=
  extend_covers appendLeaf _ _ positive_replacement

theorem positive_pruning :
    search appendLeaf [pair,wrappedPair] 1 = [⟨0,.prod pair .leaf⟩] := by decide

def allFrames : List Frame :=
  [.prodLeft pair, .prodRight pair, .compOuter pair, .compInner pair]

theorem all_constructor_replacement : Dominates allFrames ⟨2,pair⟩ ⟨2,wrappedPair⟩ := by decide

theorem all_constructor_coverage :
    Represents (Dominates allFrames) (generate allFrames [pair,wrappedPair] 2)
      (search allFrames [pair,wrappedPair] 2) :=
  search_represents allFrames [pair,wrappedPair] 2

/-- The selector uses the first retained occurrence for equal objective values. -/
theorem first_retained_tie : argmin work [⟨0,coarseA⟩,⟨0,coarseB⟩] = some ⟨0,coarseA⟩ := by
  apply argmin_first
  intro y hy
  have he := List.mem_singleton.mp hy
  subst y
  decide

def leftThree : ScanPlan := .prod pair .leaf
def rightThree : ScanPlan := .prod .leaf pair

theorem nonuniform_counterexample :
    coarse leftThree rightThree ∧
    leftThree.totalArrival (fun i => if i = 0 then 2 else 0) = 4 ∧
    rightThree.totalArrival (fun i => if i = 0 then 2 else 0) = 3 ∧
    ¬ ObservedLE leftThree rightThree := by decide

/-- The proved profile relation covers arbitrary input delays after replacement. -/
theorem positive_nonuniform (t : Nat → Nat) :
    List.Forall₂ (· ≤ ·) (pair.arrivals t) (wrappedPair.arrivals t) :=
  observed_arrivals _ _ (dominates_observed appendLeaf _ _ positive_replacement) t

/-- Declaring the workload permits strict circuit improvements, not just wrapper removal. -/
theorem workload_strict_replacement :
    Workload.Dominates (fun _ => 0) appendLeaf ⟨1,mixed⟩ ⟨1,pair.rightPow 4⟩ ∧
    mixed.work < (pair.rightPow 4).work := by decide

theorem workload_improves_context :
    Workload.Dominates (fun _ => 0) appendLeaf ⟨1,coarseB⟩ ⟨1,coarseA⟩ := by decide

theorem workload_replacement_safe :
    Covers (Workload.Dominates (fun _ => 0) appendLeaf)
      (extend appendLeaf ⟨1,coarseB⟩) (extend appendLeaf ⟨1,coarseA⟩) :=
  Workload.extension_safe (fun _ => 0) appendLeaf _ _ workload_improves_context

theorem workload_prunes_before_extension :
    profilePrune (Workload.Observation (fun _ => 0)) appendLeaf [⟨1,coarseA⟩,⟨1,coarseB⟩] =
      [⟨1,coarseB⟩] := by decide

theorem workload_completion :
    Workload.search (fun _ => 0) appendLeaf [coarseA,coarseB] 1 = [⟨0,.prod coarseB .leaf⟩] := by decide

def workloadRetained : List Candidate := Workload.search (fun _ => 0) [] catalog 0

theorem workload_catalog_pruning :
    workloadRetained = [⟨0,mixed⟩, ⟨0,pairBlocks⟩, ⟨0,fourBlocks⟩] := by decide

theorem workload_catalog_work :
    (⟨0,fourBlocks⟩ : Candidate) ∈ minimizers {a | a ∈ generate [] catalog 0} work :=
  Workload.selected_work (fun _ => 0) [] catalog 0 _ (by decide)

theorem workload_catalog_deadline :
    (⟨0,mixed⟩ : Candidate) ∈ minimizers
      {a | a ∈ Workload.feasible (fun _ => 0) 4 (generate [] catalog 0)} work :=
  Workload.selected_deadline (fun _ => 0) [] catalog 0 4 _ (by decide)

theorem workload_catalog_weighted :
    (⟨0,mixed⟩ : Candidate) ∈ minimizers {a | a ∈ generate [] catalog 0}
      (Workload.weighted (fun _ => 0) 1 10) :=
  Workload.selected_weighted (fun _ => 0) [] catalog 0 1 10 _ (by decide)

/-- The same workload-specific contract is valid for delayed inputs. -/
theorem delayed_workload :
    (⟨0,rightThree⟩ : Candidate) ∈ minimizers
      {a | a ∈ Workload.feasible (fun i => if i = 0 then 2 else 0) 3
        (generate [] [leftThree,rightThree] 0)} work :=
  Workload.selected_deadline (fun i => if i = 0 then 2 else 0) [] [leftThree,rightThree]
    0 3 _ (by decide)

end Examples.ScanSearch
