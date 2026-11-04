import Applications.Resources.RandomSelectionMean
import Examples.RandomSelectionRun
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.NormNum

/-! Connected expectations of the checked selection executions.

The empty extension has means W=0,T=2. The valid and invalid singleton
examples have means (1,9) and (1,11). On [0,1] at rank zero, the two actual
index paths have work pairs (2,11) and (3,20), hence means 5/2 and 31/2.
Two equal values retain two occurrence choices: scan volume is always two,
while source calls are 12 and 13, giving mean 25/2.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomSelectionMean
open Resources.RandomSelection MeasureTheory
open scoped BigOperators ENNReal
universe u
variable {α : Type u} [LinearOrder α]

noncomputable section

theorem empty_means (k : Nat) :
    scanMean k ([] : List α) = 0 ∧ sourceMean k ([] : List α) = 2 := by
  simp

theorem singleton_means (x : α) : scanMean 0 [x] = 1 ∧ sourceMean 0 [x] = 9 := by
  constructor
  · simp [scanMean, scanLaw, Examples.RandomSelectionRun.singleton_execution,
      PMF.pure_map, PMF.toMeasure_pure]
  · simp [sourceMean, sourceLaw, Examples.RandomSelectionRun.singleton_execution,
      PMF.pure_map, PMF.toMeasure_pure]

/-- The invalid extension retains its actual empty-continuation charge. -/
theorem invalid_singleton_means :
    scanMean 1 ([7] : List Nat) = 1 ∧ sourceMean 1 ([7] : List Nat) = 11 := by
  constructor
  · simp [scanMean, scanLaw, Examples.RandomSelectionRun.invalid_singleton,
      PMF.pure_map, PMF.toMeasure_pure]
  · simp [sourceMean, sourceLaw, Examples.RandomSelectionRun.invalid_singleton,
      PMF.pure_map, PMF.toMeasure_pure]

private theorem integral_nat_map_fin {n : Nat} (p : PMF (Fin n)) (f : Fin n → Nat) :
    (∫ k : Nat, (k : ℝ) ∂(p.map f).toMeasure) =
      ∑ i : Fin n, (p i).toReal * (f i : ℝ) := by
  rw [← PMF.toMeasure_map (f := f) (p := p) (measurable_of_countable f)]
  rw [integral_map (measurable_of_countable f).aemeasurable
    (measurable_of_countable (fun k : Nat => (k : ℝ))).aestronglyMeasurable]
  simpa only [smul_eq_mul] using PMF.integral_eq_sum p (fun i => (f i : ℝ))

theorem two_key_scan_law :
    scanLaw 0 ([0, 1] : List Nat) =
      PMF.map (fun i : Fin 2 => if i = 0 then 2 else 3)
        (Resources.RandomQuickSort.uniformIndex 1) := by
  rw [scanLaw, Examples.RandomSelectionRun.two_key_execution, PMF.map_comp]
  apply congrArg (fun f : Fin 2 → Nat => PMF.map f (Resources.RandomQuickSort.uniformIndex 1))
  funext i
  fin_cases i <;> rfl

theorem two_key_source_law :
    sourceLaw 0 ([0, 1] : List Nat) =
      PMF.map (fun i : Fin 2 => if i = 0 then 11 else 20)
        (Resources.RandomQuickSort.uniformIndex 1) := by
  rw [sourceLaw, Examples.RandomSelectionRun.two_key_execution, PMF.map_comp]
  apply congrArg (fun f : Fin 2 → Nat => PMF.map f (Resources.RandomQuickSort.uniformIndex 1))
  funext i
  fin_cases i <;> rfl

theorem two_key_scan_mean : scanMean 0 ([0, 1] : List Nat) = (5 : ℝ) / 2 := by
  rw [scanMean, two_key_scan_law, integral_nat_map_fin, Fin.sum_univ_two]
  norm_num [Resources.RandomQuickSort.uniformIndex_apply]

theorem two_key_source_mean : sourceMean 0 ([0, 1] : List Nat) = (31 : ℝ) / 2 := by
  rw [sourceMean, two_key_source_law, integral_nat_map_fin, Fin.sum_univ_two]
  norm_num [Resources.RandomQuickSort.uniformIndex_apply]

theorem duplicate_scan_law (x : α) : scanLaw 1 [x, x] = PMF.pure 2 := by
  rw [scanLaw, Examples.RandomSelectionRun.duplicate_execution, PMF.map_comp]
  change PMF.map (Function.const (Fin 2) 2) (Resources.RandomQuickSort.uniformIndex 1) = _
  exact PMF.map_const _ _

theorem duplicate_source_law (x : α) :
    sourceLaw 1 [x, x] = PMF.map (fun i : Fin 2 => 12 + i.val)
      (Resources.RandomQuickSort.uniformIndex 1) := by
  rw [sourceLaw, Examples.RandomSelectionRun.duplicate_execution, PMF.map_comp]

theorem duplicate_means (x : α) :
    scanMean 1 [x, x] = 2 ∧ sourceMean 1 [x, x] = (25 : ℝ) / 2 := by
  constructor
  · simp [scanMean, duplicate_scan_law, PMF.toMeasure_pure]
  · rw [sourceMean, duplicate_source_law, integral_nat_map_fin, Fin.sum_univ_two]
    norm_num [Resources.RandomQuickSort.uniformIndex_apply]

/-- Consume the actual conditional scan equation: only the pivot-one outcome
continues, and its requested child is the singleton [0]. -/
theorem two_key_scan_step :
    scanExpectation 0 ([0, 1] : List Nat) =
      2 + (2 : ℝ≥0∞)⁻¹ * scanExpectation 0 ([0] : List Nat) := by
  rw [scanExpectation_cons, Fin.sum_univ_two]
  simp [stepRun_eq, Applications.Selection.partition3_eq_filters]

theorem arbitrary_input_integrable (k : Nat) (xs : List α) :
    Integrable (fun w : Nat => (w : ℝ)) (scanLaw k xs).toMeasure ∧
      Integrable (fun t : Nat => (t : ℝ)) (sourceLaw k xs).toMeasure :=
  ⟨scanLaw_integrable k xs, sourceLaw_integrable k xs⟩

theorem actual_mean_bridge (k : Nat) (xs : List α) :
    scanMean k xs ≤ sourceMean k xs ∧ sourceMean k xs ≤ 9 * scanMean k xs + 2 :=
  sourceMean_comparison k xs

/-- Semantic correctness and expected resource lower bounds refer to the
same execution; no equality of path costs is inferred from its common value. -/
theorem selected_value_and_mean_bounds (k : Nat) (xs : List α) (hk : k < xs.length)
    (result : Outcome α) (hr : result ∈ (run k xs).support) :
    ∃ a, result.1 = some a ∧ Applications.Selection.RankedAt xs k a ∧
      (xs.length : ℝ) ≤ scanMean k xs ∧ scanMean k xs ≤ sourceMean k xs := by
  obtain ⟨a, ha, hRank⟩ := run_valid k xs hk result hr
  exact ⟨a, ha, hRank, scanMean_initial_le k xs, (sourceMean_comparison k xs).1⟩

end
end Examples.RandomSelectionMean
