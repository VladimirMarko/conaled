import Applications.Resources.RandomSelectionTail
import Examples.RandomSelectionDrift
import Mathlib.Tactic.NormNum

/-! Connected cases for the actual trace, residual expectations and exact tail.

The two distinct-key traces have sizes [2] and [2,1], so at time one their
sizes and residual works are 0 and 1, each with probability one half. Duplicate
equal-block runs stop after their first length-two scan. The singleton and
invalid singleton both absorb after one active call, retaining source costs
nine and eleven. Empty input has probability one at its zero non-strict scan
threshold and therefore refutes the tail conclusion without positive length.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomSelectionTail
open Resources.RandomSelection MeasureTheory
open scoped BigOperators ENNReal
universe u
variable {α : Type u} [LinearOrder α]

noncomputable section

theorem finite_trace_decomposition :
    scanVolume [(5, 1), (1, 0)] = 6 ∧
      residualWork 0 [(5, 1), (1, 0)] = 6 ∧
      residualWork 1 [(5, 1), (1, 0)] = 1 ∧
      residualWork 2 [(5, 1), (1, 0)] = 0 ∧
      scanVolume ([(5, 1), (1, 0)].take 1) + residualWork 1 [(5, 1), (1, 0)] =
        scanVolume [(5, 1), (1, 0)] :=
  ⟨rfl, rfl, rfl, rfl, scanVolume_take_add_residualWork 1 [(5, 1), (1, 0)]⟩

theorem finite_trace_absorption (j : Nat) (hj : 2 ≤ j) :
    activeSize j [(5, 1), (1, 0)] = 0 ∧ residualWork j [(5, 1), (1, 0)] = 0 :=
  ⟨activeSize_eq_zero_of_length_le j _ hj, residualWork_eq_zero_of_length_le j _ hj⟩

theorem actual_pair_trace_observations :
    ((some 0, ([(2, 0)], 11)) : Outcome Nat) ∈ (run 0 [0, 1]).support ∧
      ((some 0, ([(2, 1), (1, 0)], 20)) : Outcome Nat) ∈ (run 0 [0, 1]).support ∧
      activeSize 1 [(2, 0)] = 0 ∧ activeSize 1 [(2, 1), (1, 0)] = 1 ∧
      residualWork 1 [(2, 0)] = 0 ∧ residualWork 1 [(2, 1), (1, 0)] = 1 :=
  ⟨Examples.RandomSelectionRun.two_key_first_path, Examples.RandomSelectionRun.two_key_long_path,
    rfl, rfl, rfl, rfl⟩

theorem singleton_scan_expectation (x : α) : scanExpectation 0 [x] = 1 := by
  simp [scanExpectation, scanLaw, Examples.RandomSelectionRun.singleton_execution,
    PMF.pure_map, PMF.toMeasure_pure]

theorem singleton_absorption (x : α) :
    sizeExpectation 1 0 [x] = 0 ∧ residualExpectation 1 0 [x] = 0 ∧ sourceMean 0 [x] = 9 :=
  ⟨sizeExpectation_absorbed 1 0 [x] (by simp),
    residualExpectation_absorbed 1 0 [x] (by simp),
    (Examples.RandomSelectionMean.singleton_means x).2⟩

theorem invalid_singleton_absorption :
    sizeExpectation 1 1 ([7] : List Nat) = 0 ∧
      residualExpectation 1 1 ([7] : List Nat) = 0 ∧ sourceMean 1 ([7] : List Nat) = 11 :=
  ⟨sizeExpectation_absorbed 1 1 [7] (by simp),
    residualExpectation_absorbed 1 1 [7] (by simp),
    Examples.RandomSelectionMean.invalid_singleton_means.2⟩

theorem two_key_next_size_expectation :
    sizeExpectation 1 0 ([0, 1] : List Nat) = (1 : ℝ≥0∞) / 2 := by
  rw [sizeExpectation_succ_cons]
  change (∑ i : Fin 2, Resources.RandomQuickSort.uniformIndex 1 i *
    match (stepRun 0 ([0, 1] : List Nat) i).1 with
    | Sum.inl (j, ys) => sizeExpectation 0 j ys
    | Sum.inr _ => 0) = _
  rw [Fin.sum_univ_two]
  simp [Resources.RandomQuickSort.uniformIndex_apply, stepRun_eq,
    Applications.Selection.partition3_eq_filters, div_eq_mul_inv]

theorem two_key_size_expectations :
    sizeExpectation 0 0 ([0, 1] : List Nat) = 2 ∧
      sizeExpectation 1 0 ([0, 1] : List Nat) = (1 : ℝ≥0∞) / 2 ∧
      sizeExpectation 2 0 ([0, 1] : List Nat) = 0 := by
  refine ⟨by simp, two_key_next_size_expectation, ?_⟩
  exact sizeExpectation_absorbed 2 0 [0, 1] (by simp)

theorem two_key_residual_first :
    residualExpectation 1 0 ([0, 1] : List Nat) = (1 : ℝ≥0∞) / 2 := by
  rw [residualExpectation_succ_cons]
  change (∑ i : Fin 2, Resources.RandomQuickSort.uniformIndex 1 i *
    match (stepRun 0 ([0, 1] : List Nat) i).1 with
    | Sum.inl (j, ys) => residualExpectation 0 j ys
    | Sum.inr _ => 0) = _
  rw [Fin.sum_univ_two]
  simp [Resources.RandomQuickSort.uniformIndex_apply, stepRun_eq,
    Applications.Selection.partition3_eq_filters, singleton_scan_expectation, div_eq_mul_inv]

theorem two_key_residual_expectations :
    residualExpectation 0 0 ([0, 1] : List Nat) = (5 : ℝ≥0∞) / 2 ∧
      residualExpectation 1 0 ([0, 1] : List Nat) = (1 : ℝ≥0∞) / 2 ∧
      residualExpectation 2 0 ([0, 1] : List Nat) = 0 := by
  refine ⟨?_, two_key_residual_first, residualExpectation_absorbed 2 0 [0, 1] (by simp)⟩
  rw [residualExpectation_zero, Examples.RandomSelectionMean.two_key_scan_step,
    singleton_scan_expectation, mul_one]
  apply (ENNReal.eq_div_iff (by simp) ENNReal.ofNat_ne_top).2
  rw [mul_add, ENNReal.mul_inv_cancel (by simp) ENNReal.ofNat_ne_top]
  norm_num

/-- Both equal occurrences retain their own draw, but neither leaves residual
work after the first active scan. -/
theorem duplicate_residual_law (w : Nat) (x : α) : residualLaw (w + 1) 1 [x, x] = PMF.pure 0 := by
  rw [residualLaw, Examples.RandomSelectionRun.duplicate_execution, PMF.map_comp]
  change PMF.map (fun i : Fin 2 => residualWork (w + 1) [(2, i.val)])
    (Resources.RandomQuickSort.uniformIndex 1) = _
  have hzero : (fun i : Fin 2 => residualWork (w + 1) [(2, i.val)]) =
      Function.const (Fin 2) 0 := by
    funext i
    change residualWork w [] = 0
    exact residualWork_nil w
  rw [hzero]
  exact PMF.map_const _ _

theorem duplicate_after_first (w : Nat) (x : α) :
    sizeExpectation (w + 1) 1 [x, x] = 0 ∧ residualExpectation (w + 1) 1 [x, x] = 0 := by
  constructor
  · rw [sizeExpectation_succ_cons]
    change (∑ i : Fin 2, Resources.RandomQuickSort.uniformIndex 1 i *
      match (stepRun 1 [x, x] i).1 with
      | Sum.inl (j, ys) => sizeExpectation w j ys
      | Sum.inr _ => 0) = 0
    rw [Fin.sum_univ_two]
    simp [stepRun_eq, Applications.Selection.partition3_eq_filters]
  · rw [← residualLaw_lintegral, duplicate_residual_law, PMF.toMeasure_pure]
    simp

theorem arbitrary_absorption (j k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) (hj : xs.length ≤ j) :
    activeSize j result.2.1 = 0 ∧ residualWork j result.2.1 = 0 ∧
      sizeExpectation j k xs = 0 ∧ residualExpectation j k xs = 0 :=
  ⟨run_activeSize_absorbed j k xs result hr hj, run_residualWork_absorbed j k xs result hr hj,
    sizeExpectation_absorbed j k xs hj, residualExpectation_absorbed j k xs hj⟩

theorem arbitrary_residual_integrability (w k : Nat) (xs : List α) :
    Integrable (fun r : Nat => (r : ℝ)) (residualLaw w k xs).toMeasure ∧
      sizeExpectation w k xs ≤ (3 / 4 : ℝ≥0∞) ^ w * xs.length ∧
      residualExpectation w k xs ≤ 4 * (3 / 4 : ℝ≥0∞) ^ w * xs.length :=
  ⟨residualLaw_integrable w k xs, sizeExpectation_geometric_le w k xs,
    residualExpectation_geometric_le w k xs⟩

theorem positive_input_tails (w k : Nat) (xs : List α) (hn : 0 < xs.length) :
    (scanLaw k xs).toMeasure {s : Nat | (4 + w) * xs.length ≤ s} ≤ (3 / 4 : ℝ≥0∞) ^ w ∧
      (sourceLaw k xs).toMeasure {t : Nat | 9 * ((4 + w) * xs.length) + 2 ≤ t} ≤
        (3 / 4 : ℝ≥0∞) ^ w :=
  ⟨scanLaw_tail w k xs hn, sourceLaw_tail w k xs hn⟩

theorem valid_answer_and_tails (w k : Nat) (xs : List α) (hk : k < xs.length)
    (result : Outcome α) (hr : result ∈ (run k xs).support) :
    ∃ a, result.1 = some a ∧ Applications.Selection.RankedAt xs k a ∧
      (scanLaw k xs).toMeasure {s : Nat | (4 + w) * xs.length ≤ s} ≤ (3 / 4 : ℝ≥0∞) ^ w ∧
      (sourceLaw k xs).toMeasure {t : Nat | 9 * ((4 + w) * xs.length) + 2 ≤ t} ≤
        (3 / 4 : ℝ≥0∞) ^ w := by
  obtain ⟨a, ha, hRank⟩ := run_valid k xs hk result hr
  have hn : 0 < xs.length := lt_of_le_of_lt (Nat.zero_le k) hk
  exact ⟨a, ha, hRank, scanLaw_tail w k xs hn, sourceLaw_tail w k xs hn⟩

theorem zero_excess_tail (k : Nat) (xs : List α) (hn : 0 < xs.length) :
    (scanLaw k xs).toMeasure {s : Nat | 4 * xs.length ≤ s} ≤ 1 := by
  simpa only [Nat.add_zero, pow_zero] using scanLaw_tail 0 k xs hn

theorem empty_tail_countercase (k : Nat) :
    scanLaw k ([] : List α) = PMF.pure 0 ∧
      (scanLaw k ([] : List α)).toMeasure {s : Nat | 0 ≤ s} = 1 ∧
      ¬ (scanLaw k ([] : List α)).toMeasure {s : Nat | 0 ≤ s} ≤ (3 / 4 : ℝ≥0∞) := by
  refine ⟨scanLaw_nil k, ?_, ?_⟩
  · simpa only [List.length_nil, Nat.mul_zero] using scanLaw_empty_tail (α := α) 1 k
  · simpa only [List.length_nil, Nat.mul_zero, pow_one] using
      scanLaw_empty_tail_bound_fails (α := α) k

end
end Examples.RandomSelectionTail
