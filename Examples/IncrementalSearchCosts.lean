import Applications.Search.Incremental.Costs
import Examples.IncrementalSearchUpdates

/-! Exact same-price comparisons for two specified update workloads. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.IncrementalSearchCosts
open Search.Incremental Search.Incremental.Accounting
open Examples.IncrementalSearch Examples.IncrementalSearchUpdates

def setup := measuredInitialize earlyGraph early_positive 0 1 (fun _ => 0) (zero_heuristic early_positive 1)
def irrelevant : Batch 4 := [⟨2,3,2⟩]
theorem irrelevant_positive : PositiveBatch irrelevant := by norm_num [PositiveBatch, irrelevant]
def reused := measuredRepair earlyGraph early_positive 0 1 (fun _ => 0) early.state early.valid
  irrelevant irrelevant_positive (zero_heuristic (applyBatch_positive _ early_positive _ irrelevant_positive) 1)
def rerun := measuredRerun earlyGraph irrelevant (fun _ => 0) 0 1

/-- Neither the cached goal nor any distance label changes on this update. -/
example : reused.1.2 = 1 ∧ ∀ v, reused.1.1.g v = early.state.g v := by decide +kernel
example : bill unitPrices setup.2 = 445 := by decide +kernel
example : bill unitPrices reused.2 = 110 := by decide +kernel
example : bill unitPrices rerun.2 = 559 := by decide +kernel
example : bill unitPrices reused.2 < bill unitPrices rerun.2 := by decide +kernel

/-- The initial result and one update, including initialization and observation. -/
example : bill unitPrices setup.2 + bill unitPrices reused.2 = 555 := by decide +kernel
example : bill unitPrices setup.2 + bill unitPrices reused.2 <
    FreshCosts.cost unitPrices earlyGraph (fun _ => 0) 0 1 + bill unitPrices rerun.2 := by decide +kernel

def adverse : Batch 3 := [⟨0,1,3⟩]
theorem adverse_positive : PositiveBatch adverse := by norm_num [PositiveBatch, adverse]
def invalidated := measuredRepair triangle triangle_positive 0 2 (fun _ => 0) started.state started.valid
  adverse adverse_positive (zero_heuristic (applyBatch_positive _ triangle_positive _ adverse_positive) 2)
def adverseRerun := measuredRerun triangle adverse (fun _ => 0) 0 2

/-- One assignment changes both previously settled downstream labels. -/
example : invalidated.1.2 = 2 ∧ invalidated.1.1.g 1 = ⊤ ∧ started.state.g 1 = (1/2 : ℚ) := by decide +kernel
example : bill unitPrices invalidated.2 = 641 := by decide +kernel
example : bill unitPrices adverseRerun.2 = 429 := by decide +kernel
example : bill unitPrices adverseRerun.2 < bill unitPrices invalidated.2 := by decide +kernel

end Examples.IncrementalSearchCosts
