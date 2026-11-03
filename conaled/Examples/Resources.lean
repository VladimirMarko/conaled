import Applications.Resources.Thinning
import Applications.Resources.KnapsackSourceCosts

namespace Examples.Resources
open _root_.Resources
open Optimization.KnapsackThinning

/-- Connected recovery of two source models from the same short-circuiting run. -/
theorem thinning_two_models :
    reweight Prod.fst (Thinning.thinMeasured (· ≤ ·) [3,1,2]) = ([1],3) ∧
    reweight Prod.snd (Thinning.thinMeasured (· ≤ ·) [3,1,2]) = ([1],13) := by
  rw [Thinning.thinMeasured_calls, Thinning.thinMeasured_work]
  decide

theorem reverse_guard :
    reweight Prod.fst (Thinning.bumpMeasured (· ≤ ·) 3 [1]) = ([1],2) := by
  rw [Thinning.bumpMeasured_calls]
  decide

theorem incomparable_guards :
    reweight Prod.snd (Thinning.bumpMeasured (· < ·) 1 [1]) = ([1,1],5) := by
  rw [Thinning.bumpMeasured_work]
  decide

/-- Reweighting commutes with actual sequential executions, retaining the
intermediate list supplied to the second execution. -/
theorem composed_thinning (xs : List Nat) :
    reweight (AddMonoidHom.fst Nat Nat)
      (bind (Thinning.thinMeasured (· ≤ ·) xs) (Thinning.thinMeasured (· ≤ ·))) =
    bind (Thinning.thinRun (· ≤ ·) xs) (Thinning.thinRun (· ≤ ·)) := by
  rw [reweight_bind]
  change bind (reweight Prod.fst (Thinning.thinMeasured (· ≤ ·) xs))
    (fun x => reweight Prod.fst (Thinning.thinMeasured (· ≤ ·) x)) = _
  simp only [Thinning.thinMeasured_calls]

theorem composed_erasure (xs : List Nat) :
    (bind (Thinning.thinMeasured (· ≤ ·) xs) (Thinning.thinMeasured (· ≤ ·))).1 =
      Optimization.Thinning.thinBy (· ≤ ·) (Optimization.Thinning.thinBy (· ≤ ·) xs) :=
  bind_erases _ _ _ _ (Thinning.thinMeasured_value _) (Thinning.thinMeasured_value _) xs

def item : Item String := ⟨"one",7,1⟩
def old : Array (Selection String) := #[emptySelection,emptySelection,emptySelection]

theorem row_observations : (Knapsack.stepMeasured 2 item old).2 = (3,2,3,124) := by
  rw [Knapsack.stepMeasured_exact]
  rfl

theorem row_tariffs :
    (reweight (Knapsack.tariff 1 1 1 0) (Knapsack.stepMeasured 2 item old)).2 = 8 ∧
    (reweight (Knapsack.tariff 0 0 0 1) (Knapsack.stepMeasured 2 item old)).2 = 124 := by
  simp only [reweight, row_observations]
  decide

/-- Capacity two cannot select the same weight-one occurrence twice. -/
theorem old_row_once : ((Knapsack.stepMeasured 2 item old).1[2]?).map Selection.value = some 7 := by
  rw [Knapsack.stepMeasured_value]
  decide

theorem copy_charged_without_fits :
    (Knapsack.stepMeasured 2 (⟨"heavy",100,4⟩ : Item String) old).2 = (3,0,3,78) := by
  rw [Knapsack.stepMeasured_exact]
  rfl

theorem skip_on_value_tie :
    ((Knapsack.stepMeasured 2 (⟨"tie",0,0⟩ : Item String) old).1[2]?).map Selection.names = some [] := by
  rw [Knapsack.stepMeasured_value]
  decide

theorem scalar_source_recovered :
    reweight (fun w : Knapsack.Work => w.2.2.2) (Knapsack.stepMeasured 2 item old) =
      Knapsack.sourceStepRun 2 item old := Knapsack.stepMeasured_sourceScalar _ _ _

theorem row_bound : (Knapsack.stepMeasured 2 item old).2.2.2.2 ≤ 160 :=
  Knapsack.stepMeasured_bound _ _ _ rfl

theorem monotone_work_bound :
    (reweight (fun w : Knapsack.Work => w.2.2.2) (Knapsack.stepMeasured 2 item old)).2 ≤ 160 := by
  have hm : Monotone (fun w : Knapsack.Work => w.2.2.2) := fun _ _ h => h.2.2.2
  apply reweight_bound (fun w : Knapsack.Work => w.2.2.2) hm _ (3,3,3,160)
  rw [row_observations]
  decide

/-- The existing function and erasure proof supply a semantic square directly. -/
def rowSquare : Squares.Square ⟨Array (Selection String), Array (Selection String), id⟩
    ⟨Measured (Array (Selection String)) Knapsack.Work, Array (Selection String), Prod.fst⟩ :=
  erasureSquare (Knapsack.stepMeasured 2 item) (Knapsack.step 2 item)
    (Knapsack.stepMeasured_value 2 item)

/-- Even these concrete tariffs agree on values while disagreeing on cost. -/
theorem value_equality_does_not_transport_cost :
    (reweight (Knapsack.tariff 1 1 1 0) (Knapsack.stepMeasured 2 item old)).1 =
      (reweight (Knapsack.tariff 0 0 0 1) (Knapsack.stepMeasured 2 item old)).1 ∧
    (reweight (Knapsack.tariff 1 1 1 0) (Knapsack.stepMeasured 2 item old)).2 ≠
      (reweight (Knapsack.tariff 0 0 0 1) (Knapsack.stepMeasured 2 item old)).2 := by
  constructor
  · rfl
  · rw [row_tariffs.1, row_tariffs.2]
    decide

end Examples.Resources
