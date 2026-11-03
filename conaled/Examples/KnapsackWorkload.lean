import Applications.Resources.KnapsackWorkload

/-! Full selections and independently calculated charges for the complete
immutable workload. Equal labels denote distinct input occurrences. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.KnapsackWorkload
open Optimization.KnapsackThinning Resources
open Resources.Knapsack

def free : Item String := ⟨"free",7,0⟩
def repeated : List (Item String) := [⟨"same",3,1⟩,⟨"same",4,1⟩]
def ties : List (Item String) := [⟨"a",5,1⟩,⟨"b",5,1⟩]
def heavy : Item String := ⟨"heavy",100,4⟩
def twoRows : List (Item String) := [⟨"a",5,1⟩,⟨"b",7,1⟩]

theorem empty_workload : runMeasured 2 ([] : List (Item String)) =
    (emptySelection,(0,0,0,19)) := by
  rw [runMeasured_exact]
  decide +kernel

theorem zero_capacity_free : runMeasured 0 [free] =
    (⟨["free"],7,0⟩,(1,1,1,72)) := by
  rw [runMeasured_exact]
  decide +kernel

theorem repeated_labels : runMeasured 2 repeated =
    (⟨["same","same"],7,2⟩,(6,4,6,275)) := by
  rw [runMeasured_exact]
  decide +kernel

/-- Skip wins at the first row's tie, retaining the later original occurrence. -/
theorem tied_values : runMeasured 1 ties = (⟨["b"],5,1⟩,(4,2,4,177)) := by
  rw [runMeasured_exact]
  decide +kernel

theorem overweight : runMeasured 2 [heavy] = (emptySelection,(3,0,3,98)) := by
  rw [runMeasured_exact]
  decide +kernel

/-- Capacity three leaves one slot unused: each of the two occurrences is
available once, despite ascending batch indices in both rows. -/
theorem two_old_rows : runMeasured 3 twoRows =
    (⟨["a","b"],12,2⟩,(8,6,8,370)) := by
  rw [runMeasured_exact]
  decide +kernel

theorem all_capacity_entry : (table 3 twoRows)[2]? = some ⟨["a","b"],12,2⟩ := by
  rw [table_entry 3 twoRows 2 (by decide)]
  decide +kernel

theorem selection_consumer : Optimal 2 repeated ⟨["same","same"],7,2⟩ := by
  have h := runMeasured_optimal 2 repeated
  rwa [repeated_labels] at h

theorem zero_capacity_optimal : Optimal 0 [free] ⟨["free"],7,0⟩ := by
  have h := runMeasured_optimal 0 [free]
  rwa [zero_capacity_free] at h

/-- The pruned frontier and full array agree on value without requiring the
same selection under ties. This consumer crosses the two implementations. -/
theorem frontier_consumer (s : Selection String) (hs : solve 1 ties = some s) :
    s.value = 5 := by
  have h := select_frontier_value 1 ties s hs
  have hv : (select 1 ties).value = 5 := by decide +kernel
  omega

theorem reweighted_consumer :
    (reweight (tariff 2 3 5 0) (runMeasured 2 repeated)).2 = 54 ∧
    (reweight (tariff 0 0 0 1) (runMeasured 2 repeated)).2 = 275 := by
  constructor <;> rw [runMeasured_tariff] <;> decide +kernel

theorem reweighted_selection :
    (reweight (tariff 2 3 5 0) (runMeasured 2 repeated)).1 = ⟨["same","same"],7,2⟩ := by
  rw [reweight_value,repeated_labels]

/-- Reweighting is connected to the actual row, read and traversal sequence. -/
theorem reweighted_pipeline :
    reweight (tariff 2 3 5 0) (runMeasured 2 repeated) =
      bind (reweight (tariff 2 3 5 0) (rowsMeasured 2 repeated)) fun row =>
        bind (reweight (tariff 2 3 5 0) (read row 2,(0,0,0,3)))
          (fun s => reweight (tariff 2 3 5 0) (observeMeasured s)) :=
  runMeasured_reweight _ _ _

theorem output_names_charged :
    observeMeasured (⟨["same","same"],7,2⟩ : Selection String) =
      (⟨["same","same"],7,2⟩,(0,0,0,10)) := by
  rw [observeMeasured_exact]
  rfl

theorem actual_copies_charged : (copyCharges 2 repeated).sum = 14 := by
  rw [immutable_copy_contribution]
  rfl

theorem source_scalar_consumer : sourceRun 2 repeated = (⟨["same","same"],7,2⟩,275) := by
  rw [← runMeasured_sourceScalar,repeated_labels]
  rfl

theorem source_bound : (sourceRun 2 repeated).2 ≤ 720 := sourceRun_bound 2 repeated

theorem scalar_bound : (runMeasured 2 repeated).2.2.2.2 ≤ 720 := runMeasured_bound 2 repeated

end Examples.KnapsackWorkload
