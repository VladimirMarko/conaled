import Applications.Resources.RandomSelectionRun
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Basic.ENNReal.BigOperators

/-! Expectations of the actual fresh-occurrence selection execution.

Ranks are the zero-based `run` ranks, including its explicit invalid-rank
extension. The separate `select` interface keeps its one-based boundary.

The scalar scan and source-cost laws are integrated on Nat. Their checked
pathwise bounds establish finiteness and real integrability for arbitrary
ordered payloads, without a measurable-space or finite-type assumption on
those payloads. The common-run weighted observation preserves the coupling
between scan volume and source calls. Its conditional equation follows the
actual selected child and includes direct equal-block termination.

The quadratic bounds here establish integrability; the separate rank-drift
argument is still needed for the book's linear expectation and exact tail.
Abstract uniform occurrence choice retains the existing declared tariff.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomSelection
open MeasureTheory
open scoped BigOperators ENNReal
universe u v
variable {α : Type u} {β : Type v}

noncomputable section

private theorem weighted_bind (p : PMF α) (f : α → PMF β) (g : β → ℝ≥0∞) :
    (∑' b, p.bind f b * g b) = ∑' a, p a * (∑' b, f a b * g b) := by
  calc
    _ = ∑' b, ∑' a, p a * f a b * g b := by
      apply tsum_congr
      intro b
      rw [PMF.bind_apply, ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' b, p a * f a b * g b := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro a
      simp only [mul_assoc, ENNReal.tsum_mul_left]

private theorem weighted_pure (x : α) (g : α → ℝ≥0∞) :
    (∑' a, PMF.pure x a * g a) = g x := by
  classical
  simp only [PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]

private theorem weighted_map (p : PMF α) (f : α → β) (g : β → ℝ≥0∞) :
    (∑' b, p.map f b * g b) = ∑' a, p a * g (f a) := by
  rw [PMF.map, weighted_bind]
  simp only [Function.comp_apply, weighted_pure]

private theorem weighted_add (p : PMF α) (f g : α → ℝ≥0∞) :
    (∑' a, p a * (f a + g a)) = (∑' a, p a * f a) + ∑' a, p a * g a := by
  simp only [mul_add, ENNReal.tsum_add]

private theorem weighted_const (p : PMF α) (c : ℝ≥0∞) :
    (∑' a, p a * c) = c := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

private theorem weighted_mono_support (p : PMF α) (f g : α → ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a ≤ g a) :
    (∑' a, p a * f a) ≤ ∑' a, p a * g a := by
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul_right (h a ((PMF.mem_support_iff p a).mpr ha)) (p a)

private theorem lintegral_nat_eq (p : PMF Nat) :
    (∫⁻ k : Nat, (k : ℝ≥0∞) ∂p.toMeasure) = ∑' k, p k * (k : ℝ≥0∞) := by
  rw [lintegral_countable']
  apply tsum_congr
  intro k
  rw [PMF.toMeasure_apply_singleton p k (measurableSet_singleton k)]
  exact mul_comm _ _

private theorem lintegral_nat_le_of_support (p : PMF Nat) (b : Nat)
    (h : p.support ⊆ Set.Iic b) :
    (∫⁻ k : Nat, (k : ℝ≥0∞) ∂p.toMeasure) ≤ (b : ℝ≥0∞) := by
  rw [lintegral_nat_eq]
  calc
    _ ≤ ∑' k, p k * (b : ℝ≥0∞) := by
      apply weighted_mono_support
      intro k hk
      have hb : k ≤ b := h hk
      exact_mod_cast hb
    _ = _ := weighted_const p _

private theorem integrable_nat_of_lower_finite (p : PMF Nat)
    (hf : (∫⁻ k : Nat, (k : ℝ≥0∞) ∂p.toMeasure) ≠ ∞) :
    Integrable (fun k : Nat => (k : ℝ)) p.toMeasure := by
  have h := integrable_toReal_of_lintegral_ne_top
    (measurable_of_countable (fun k : Nat => (k : ℝ≥0∞))).aemeasurable hf
  simpa only [ENNReal.toReal_natCast] using h

private theorem integral_nat_eq (p : PMF Nat) :
    (∫ k : Nat, (k : ℝ) ∂p.toMeasure) =
      (∫⁻ k : Nat, (k : ℝ≥0∞) ∂p.toMeasure).toReal := by
  have hfinite : ∀ᵐ k : Nat ∂p.toMeasure, (k : ℝ≥0∞) < ∞ :=
    Filter.Eventually.of_forall fun k => lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top k)
  simpa only [ENNReal.toReal_natCast] using
    integral_toReal
      (measurable_of_countable (fun k : Nat => (k : ℝ≥0∞))).aemeasurable hfinite

section Ordered
variable [LinearOrder α]

/-- Nonnegative weighted observation of the existing execution. A general
observation may have infinite expectation; scalar work finiteness is proved below. -/
def workExpectation (k : Nat) (xs : List α) (f : Outcome α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' result, run k xs result * f result

theorem workExpectation_mono (k : Nat) (xs : List α) (f g : Outcome α → ℝ≥0∞)
    (h : ∀ result ∈ (run k xs).support, f result ≤ g result) :
    workExpectation k xs f ≤ workExpectation k xs g :=
  weighted_mono_support _ _ _ h

theorem workExpectation_const (k : Nat) (xs : List α) (c : ℝ≥0∞) :
    workExpectation k xs (fun _ => c) = c := weighted_const _ _

theorem workExpectation_add (k : Nat) (xs : List α) (f g : Outcome α → ℝ≥0∞) :
    workExpectation k xs (fun result => f result + g result) =
      workExpectation k xs f + workExpectation k xs g := weighted_add _ _ _

theorem workExpectation_mul (k : Nat) (xs : List α) (c : ℝ≥0∞)
    (f : Outcome α → ℝ≥0∞) :
    workExpectation k xs (fun result => c * f result) = c * workExpectation k xs f := by
  unfold workExpectation
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro result
  exact mul_left_comm _ _ _

theorem workExpectation_nil (k : Nat) (f : Outcome α → ℝ≥0∞) :
    workExpectation k [] f = f (none, ([], 2)) := by
  rw [workExpectation, run_nil, weighted_pure]

/-- Conditioning on the actual fresh current occurrence. The continuation
observation prepends this step to the one child actually selected by `stepRun`.
There is no independence assumption on successive active sizes. -/
theorem workExpectation_cons (k : Nat) (head : α) (tail : List α)
    (f : Outcome α → ℝ≥0∞) :
    workExpectation k (head :: tail) f =
      ∑ i : Fin (tail.length + 1),
        let action := stepRun k (head :: tail) i
        (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) *
          match action.1 with
          | Sum.inl (j, ys) => workExpectation j ys
              (fun result => f (prepend (head :: tail).length i.val action.2 result))
          | Sum.inr p => f (some p, ([((head :: tail).length, i.val)], action.2)) := by
  rw [workExpectation, run_cons, weighted_bind, tsum_fintype]
  simp only [RandomQuickSort.uniformIndex_apply]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  apply congrArg (fun e : ℝ≥0∞ => (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) * e)
  cases (stepRun k (head :: tail) i).1 with
  | inl state =>
      rcases state with ⟨j, ys⟩
      exact weighted_map (run j ys)
        (prepend (head :: tail).length i.val (stepRun k (head :: tail) i).2) f
  | inr p =>
      exact weighted_pure
        (some p, ([((head :: tail).length, i.val)], (stepRun k (head :: tail) i).2)) f

/-- Standard nonnegative expectation of the actual scan-volume marginal. -/
def scanExpectation (k : Nat) (xs : List α) : ℝ≥0∞ :=
  ∫⁻ w : Nat, (w : ℝ≥0∞) ∂(scanLaw k xs).toMeasure

/-- Standard nonnegative expectation of the actual source-call marginal. -/
def sourceExpectation (k : Nat) (xs : List α) : ℝ≥0∞ :=
  ∫⁻ t : Nat, (t : ℝ≥0∞) ∂(sourceLaw k xs).toMeasure

theorem scanExpectation_eq_workExpectation (k : Nat) (xs : List α) :
    scanExpectation k xs =
      workExpectation k xs (fun result => (scanVolume result.2.1 : ℝ≥0∞)) := by
  rw [scanExpectation, lintegral_nat_eq, scanLaw, weighted_map]

theorem sourceExpectation_eq_workExpectation (k : Nat) (xs : List α) :
    sourceExpectation k xs =
      workExpectation k xs (fun result => (result.2.2 : ℝ≥0∞)) := by
  rw [sourceExpectation, lintegral_nat_eq, sourceLaw, weighted_map]

/-- The natural triangular bound is divided before its cast. It proves
finiteness without assuming the forthcoming linear expected bound. -/
theorem scanExpectation_quadratic_le (k : Nat) (xs : List α) :
    scanExpectation k xs ≤ ((xs.length * (xs.length + 1) / 2 : Nat) : ℝ≥0∞) :=
  lintegral_nat_le_of_support _ _ (scanLaw_support k xs)

theorem sourceExpectation_quadratic_le (k : Nat) (xs : List α) :
    sourceExpectation k xs ≤
      ((9 * (xs.length * (xs.length + 1) / 2) + 2 : Nat) : ℝ≥0∞) :=
  lintegral_nat_le_of_support _ _ (sourceLaw_support k xs)

theorem scanExpectation_ne_top (k : Nat) (xs : List α) : scanExpectation k xs ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (scanExpectation_quadratic_le k xs)

theorem sourceExpectation_ne_top (k : Nat) (xs : List α) : sourceExpectation k xs ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (sourceExpectation_quadratic_le k xs)

/-- Integrability is established on the countable work carrier, with no
measurability or finite-type assumption on the ordered payload. -/
theorem scanLaw_integrable (k : Nat) (xs : List α) :
    Integrable (fun w : Nat => (w : ℝ)) (scanLaw k xs).toMeasure :=
  integrable_nat_of_lower_finite _ (scanExpectation_ne_top k xs)

theorem sourceLaw_integrable (k : Nat) (xs : List α) :
    Integrable (fun t : Nat => (t : ℝ)) (sourceLaw k xs).toMeasure :=
  integrable_nat_of_lower_finite _ (sourceExpectation_ne_top k xs)

theorem scanExpectation_initial_le (k : Nat) (xs : List α) :
    (xs.length : ℝ≥0∞) ≤ scanExpectation k xs := by
  rw [scanExpectation_eq_workExpectation]
  calc
    _ = workExpectation k xs (fun _ => (xs.length : ℝ≥0∞)) :=
      (workExpectation_const k xs _).symm
    _ ≤ _ := by
      apply workExpectation_mono
      intro result hr
      exact_mod_cast run_initial_scan_le k xs result hr

/-- Transport through the common run, preserving the actual joint observation.
The additive two retains the possible empty continuation of an invalid rank. -/
theorem sourceExpectation_comparison (k : Nat) (xs : List α) :
    scanExpectation k xs ≤ sourceExpectation k xs ∧
      sourceExpectation k xs ≤ 9 * scanExpectation k xs + 2 := by
  constructor
  · rw [scanExpectation_eq_workExpectation, sourceExpectation_eq_workExpectation]
    apply workExpectation_mono
    intro result hr
    exact_mod_cast (run_source_bridge k xs result hr).1
  · calc
      _ = workExpectation k xs (fun result => (result.2.2 : ℝ≥0∞)) :=
        sourceExpectation_eq_workExpectation k xs
      _ ≤ workExpectation k xs
          (fun result => 9 * (scanVolume result.2.1 : ℝ≥0∞) + 2) := by
        apply workExpectation_mono
        intro result hr
        exact_mod_cast (run_source_bridge k xs result hr).2
      _ = _ := by
        rw [workExpectation_add, workExpectation_mul, workExpectation_const,
          ← scanExpectation_eq_workExpectation]

@[simp] theorem scanExpectation_nil (k : Nat) : scanExpectation k ([] : List α) = 0 := by
  rw [scanExpectation_eq_workExpectation]
  exact workExpectation_nil k _

@[simp] theorem sourceExpectation_nil (k : Nat) : sourceExpectation k ([] : List α) = 2 := by
  rw [sourceExpectation_eq_workExpectation]
  exact workExpectation_nil k _

/-- The actual scan recurrence: pay this positive active length, then average
only the selected child, assigning zero continuation to the equal branch.
This is not an equality with a larger-partition process. -/
theorem scanExpectation_cons (k : Nat) (head : α) (tail : List α) :
    scanExpectation k (head :: tail) =
      ((tail.length + 1 : Nat) : ℝ≥0∞) +
        (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) *
          ∑ i : Fin (tail.length + 1),
            match (stepRun k (head :: tail) i).1 with
            | Sum.inl (j, ys) => scanExpectation j ys
            | Sum.inr _ => 0 := by
  have hconst :
      (∑ _i : Fin (tail.length + 1),
        (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) *
          ((tail.length + 1 : Nat) : ℝ≥0∞)) =
        ((tail.length + 1 : Nat) : ℝ≥0∞) := by
    simpa only [tsum_fintype, RandomQuickSort.uniformIndex_apply] using
      weighted_const (RandomQuickSort.uniformIndex tail.length)
        ((tail.length + 1 : Nat) : ℝ≥0∞)
  rw [scanExpectation_eq_workExpectation, workExpectation_cons]
  calc
    _ = ∑ i : Fin (tail.length + 1),
        (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) *
          (((tail.length + 1 : Nat) : ℝ≥0∞) +
            match (stepRun k (head :: tail) i).1 with
            | Sum.inl (j, ys) => scanExpectation j ys
            | Sum.inr _ => 0) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only
      apply congrArg (fun e : ℝ≥0∞ => (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) * e)
      cases (stepRun k (head :: tail) i).1 with
      | inl state =>
          rcases state with ⟨j, ys⟩
          simp only [prepend, scanVolume_cons, List.length_cons, Nat.cast_add,
            workExpectation_add, workExpectation_const, ← scanExpectation_eq_workExpectation]
      | inr _p =>
          simp only [scanVolume_cons, scanVolume_nil, List.length_cons, add_zero]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [hconst, Finset.mul_sum]

/-- Real expectation of the actual scan-volume distribution. -/
def scanMean (k : Nat) (xs : List α) : ℝ :=
  ∫ w : Nat, (w : ℝ) ∂(scanLaw k xs).toMeasure

/-- Real expectation of the actual source-call distribution. -/
def sourceMean (k : Nat) (xs : List α) : ℝ :=
  ∫ t : Nat, (t : ℝ) ∂(sourceLaw k xs).toMeasure

theorem scanMean_eq_toReal (k : Nat) (xs : List α) :
    scanMean k xs = (scanExpectation k xs).toReal := integral_nat_eq _

theorem sourceMean_eq_toReal (k : Nat) (xs : List α) :
    sourceMean k xs = (sourceExpectation k xs).toReal := integral_nat_eq _

theorem scanMean_nonneg (k : Nat) (xs : List α) : 0 ≤ scanMean k xs :=
  integral_nonneg (fun w => Nat.cast_nonneg w)

theorem sourceMean_nonneg (k : Nat) (xs : List α) : 0 ≤ sourceMean k xs :=
  integral_nonneg (fun t => Nat.cast_nonneg t)

theorem scanMean_initial_le (k : Nat) (xs : List α) : (xs.length : ℝ) ≤ scanMean k xs := by
  rw [scanMean_eq_toReal]
  simpa only [ENNReal.toReal_natCast] using
    ENNReal.toReal_mono (scanExpectation_ne_top k xs) (scanExpectation_initial_le k xs)

theorem scanMean_quadratic_le (k : Nat) (xs : List α) :
    scanMean k xs ≤ ((xs.length * (xs.length + 1) / 2 : Nat) : ℝ) := by
  rw [scanMean_eq_toReal]
  simpa only [ENNReal.toReal_natCast] using
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) (scanExpectation_quadratic_le k xs)

theorem sourceMean_quadratic_le (k : Nat) (xs : List α) :
    sourceMean k xs ≤ ((9 * (xs.length * (xs.length + 1) / 2) + 2 : Nat) : ℝ) := by
  rw [sourceMean_eq_toReal]
  simpa only [ENNReal.toReal_natCast] using
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) (sourceExpectation_quadratic_le k xs)

theorem sourceMean_comparison (k : Nat) (xs : List α) :
    scanMean k xs ≤ sourceMean k xs ∧ sourceMean k xs ≤ 9 * scanMean k xs + 2 := by
  obtain ⟨hlo, hup⟩ := sourceExpectation_comparison k xs
  constructor
  · rw [scanMean_eq_toReal, sourceMean_eq_toReal]
    exact ENNReal.toReal_mono (sourceExpectation_ne_top k xs) hlo
  · rw [scanMean_eq_toReal, sourceMean_eq_toReal]
    have hmul : 9 * scanExpectation k xs ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top 9) (scanExpectation_ne_top k xs)
    have hfinite : 9 * scanExpectation k xs + 2 ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨hmul, ENNReal.natCast_ne_top 2⟩
    have h := ENNReal.toReal_mono hfinite hup
    simpa only [ENNReal.toReal_add hmul (ENNReal.natCast_ne_top 2),
      ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h

@[simp] theorem scanMean_nil (k : Nat) : scanMean k ([] : List α) = 0 := by
  simp only [scanMean_eq_toReal, scanExpectation_nil, ENNReal.toReal_zero]

@[simp] theorem sourceMean_nil (k : Nat) : sourceMean k ([] : List α) = 2 := by
  simp only [sourceMean_eq_toReal, sourceExpectation_nil, ENNReal.toReal_ofNat]

end Ordered
end
end Resources.RandomSelection
