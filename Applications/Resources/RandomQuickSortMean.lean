import Applications.Resources.RandomQuickSort
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Basic.ENNReal.BigOperators

/-! Finite expectations of the existing actual fresh occurrence-pivot run.
The natural cost laws are integrated on Nat, leaving payload universes and
instances unrestricted. Actual support bounds prove real integrability before
the bind-mean equation is used. The equation averages actual indexed partitions;
it is not the later distinct-key rank recurrence or an asymptotic bound.
The literal mean includes the actual source appends, but neither observation
charges pivot sampling, index lookup/removal, or random-bit implementation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomQuickSort
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
  · exact mul_le_mul_left' (h a ((PMF.mem_support_iff p a).mpr ha)) (p a)

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

/-- Real mean of the actual exercise-cost projection. Integrability is proved
below from its actual finite support bound. -/
def exerciseMean (lt : α → α → Bool) (xs : List α) : ℝ :=
  ∫ k : Nat, (k : ℝ) ∂(exerciseLaw lt xs).toMeasure

/-- Real mean of the actual append-inclusive body cost. Pivot implementation
work remains outside the observation, just as in literalLaw. -/
def literalMean (lt : α → α → Bool) (xs : List α) : ℝ :=
  ∫ k : Nat, (k : ℝ) ∂(literalLaw lt xs).toMeasure

/-- The lower expectation is bounded before taking any real integral. -/
theorem exerciseLaw_lintegral_le (lt : α → α → Bool) (xs : List α) :
    (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(exerciseLaw lt xs).toMeasure) ≤
      ((2 * xs.length ^ 2 + 2 * xs.length + 1 : Nat) : ℝ≥0∞) :=
  lintegral_nat_le_of_support _ _ (exerciseLaw_support lt xs)

/-- The bound performs natural division before the cast. -/
theorem literalLaw_lintegral_le (lt : α → α → Bool) (xs : List α) :
    (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(literalLaw lt xs).toMeasure) ≤
      (((5 * xs.length ^ 2 + 9 * xs.length + 2) / 2 : Nat) : ℝ≥0∞) :=
  lintegral_nat_le_of_support _ _ (literalLaw_support lt xs)

theorem exerciseLaw_lintegral_ne_top (lt : α → α → Bool) (xs : List α) :
    (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(exerciseLaw lt xs).toMeasure) ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (exerciseLaw_lintegral_le lt xs)

theorem literalLaw_lintegral_ne_top (lt : α → α → Bool) (xs : List α) :
    (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(literalLaw lt xs).toMeasure) ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (literalLaw_lintegral_le lt xs)

private theorem integrable_nat_of_lower_finite (p : PMF Nat)
    (hf : (∫⁻ k : Nat, (k : ℝ≥0∞) ∂p.toMeasure) ≠ ∞) :
    Integrable (fun k : Nat => (k : ℝ)) p.toMeasure := by
  have h := integrable_toReal_of_lintegral_ne_top
    (measurable_of_countable (fun k : Nat => (k : ℝ≥0∞))).aemeasurable hf
  simpa only [ENNReal.toReal_natCast] using h

/-- Genuine real integrability of the actual exercise observation, for every
input and comparator. There is no measurable-space premise on payloads. -/
theorem exerciseLaw_integrable (lt : α → α → Bool) (xs : List α) :
    Integrable (fun k : Nat => (k : ℝ)) (exerciseLaw lt xs).toMeasure :=
  integrable_nat_of_lower_finite _ (exerciseLaw_lintegral_ne_top lt xs)

theorem literalLaw_integrable (lt : α → α → Bool) (xs : List α) :
    Integrable (fun k : Nat => (k : ℝ)) (literalLaw lt xs).toMeasure :=
  integrable_nat_of_lower_finite _ (literalLaw_lintegral_ne_top lt xs)

private theorem integral_nat_eq (p : PMF Nat) :
    (∫ k : Nat, (k : ℝ) ∂p.toMeasure) =
      (∫⁻ k : Nat, (k : ℝ≥0∞) ∂p.toMeasure).toReal := by
  have hfinite : ∀ᵐ k : Nat ∂p.toMeasure, (k : ℝ≥0∞) < ∞ :=
    Filter.Eventually.of_forall fun k => lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top k)
  simpa only [ENNReal.toReal_natCast] using
    integral_toReal
      (measurable_of_countable (fun k : Nat => (k : ℝ≥0∞))).aemeasurable hfinite

/-- The actual cost's real integrability is the preceding independent theorem;
this equality alone would not certify finiteness for an arbitrary PMF. -/
theorem exerciseMean_eq_toReal_lintegral (lt : α → α → Bool) (xs : List α) :
    exerciseMean lt xs =
      (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(exerciseLaw lt xs).toMeasure).toReal :=
  integral_nat_eq _

theorem literalMean_eq_toReal_lintegral (lt : α → α → Bool) (xs : List α) :
    literalMean lt xs =
      (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(literalLaw lt xs).toMeasure).toReal :=
  integral_nat_eq _

theorem exerciseMean_nonneg (lt : α → α → Bool) (xs : List α) :
    0 ≤ exerciseMean lt xs := integral_nonneg (fun k => Nat.cast_nonneg k)

theorem literalMean_nonneg (lt : α → α → Bool) (xs : List α) :
    0 ≤ literalMean lt xs := integral_nonneg (fun k => Nat.cast_nonneg k)

theorem exerciseMean_le (lt : α → α → Bool) (xs : List α) :
    exerciseMean lt xs ≤ ((2 * xs.length ^ 2 + 2 * xs.length + 1 : Nat) : ℝ) := by
  rw [exerciseMean_eq_toReal_lintegral]
  simpa only [ENNReal.toReal_natCast] using
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) (exerciseLaw_lintegral_le lt xs)

theorem literalMean_le (lt : α → α → Bool) (xs : List α) :
    literalMean lt xs ≤ (((5 * xs.length ^ 2 + 9 * xs.length + 2) / 2 : Nat) : ℝ) := by
  rw [literalMean_eq_toReal_lintegral]
  simpa only [ENNReal.toReal_natCast] using
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) (literalLaw_lintegral_le lt xs)

@[simp] theorem exerciseMean_nil (lt : α → α → Bool) : exerciseMean lt [] = 1 := by
  simp [exerciseMean, PMF.toMeasure_pure]

@[simp] theorem literalMean_nil (lt : α → α → Bool) : literalMean lt [] = 1 := by
  simp [literalMean, PMF.toMeasure_pure]

@[simp] theorem exerciseMean_singleton (lt : α → α → Bool) (x : α) :
    exerciseMean lt [x] = 5 := by
  simp [exerciseMean, PMF.toMeasure_pure]

@[simp] theorem literalMean_singleton (lt : α → α → Bool) (x : α) :
    literalMean lt [x] = 8 := by
  simp [literalMean, PMF.toMeasure_pure]

private theorem weighted_two_children (p q : PMF Nat) (m : Nat) :
    (∑' k, (p.bind (fun left => q.bind (fun right =>
      PMF.pure (left + right + 4 * m + 3)))) k * (k : ℝ≥0∞)) =
        (∑' left, p left * (left : ℝ≥0∞)) +
          (∑' right, q right * (right : ℝ≥0∞)) + ((4 * m + 3 : Nat) : ℝ≥0∞) := by
  simp only [weighted_bind, weighted_pure, Nat.cast_add, weighted_add,
    weighted_const, add_assoc]

private theorem exerciseLaw_lintegral_cons (lt : α → α → Bool) (head : α)
    (tail : List α) :
    (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(exerciseLaw lt (head :: tail)).toMeasure) =
      (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) *
        (∑ i : Fin (tail.length + 1),
          let pivot := (head :: tail)[i.val]'i.isLt
          let rest := (head :: tail).eraseIdx i.val
          (∫⁻ k : Nat, (k : ℝ≥0∞)
            ∂(exerciseLaw lt (rest.filter (fun x => lt x pivot))).toMeasure) +
          (∫⁻ k : Nat, (k : ℝ≥0∞)
            ∂(exerciseLaw lt (rest.filter (fun x => !(lt x pivot)))).toMeasure)) +
        ((4 * tail.length + 3 : Nat) : ℝ≥0∞) := by
  have hrest (i : Fin (tail.length + 1)) :
      ((head :: tail).eraseIdx i.val).length = tail.length := by
    have h : ((head :: tail).eraseIdx i.val).length + 1 = (head :: tail).length :=
      List.length_eraseIdx_add_one i.isLt
    simp only [List.length_cons] at h
    omega
  rw [lintegral_nat_eq, exerciseLaw_cons, weighted_bind]
  simp only [weighted_two_children, ← lintegral_nat_eq, hrest]
  rw [weighted_add, weighted_const, tsum_fintype]
  simp only [uniformIndex_apply, ← Finset.mul_sum]

/-- The mean of the actual recursive run averages its actual indexed children.
This equation needs no distinctness or order law. It is not a size-only rank
recurrence: the selected occurrence, removal and both filters remain explicit. -/
theorem exerciseMean_cons (lt : α → α → Bool) (head : α) (tail : List α) :
    exerciseMean lt (head :: tail) =
      (((tail.length + 1 : Nat) : ℝ)⁻¹) *
        (∑ i : Fin (tail.length + 1),
          let pivot := (head :: tail)[i.val]'i.isLt
          let rest := (head :: tail).eraseIdx i.val
          exerciseMean lt (rest.filter (fun x => lt x pivot)) +
            exerciseMean lt (rest.filter (fun x => !(lt x pivot)))) +
        ((4 * tail.length + 3 : Nat) : ℝ) := by
  let left (i : Fin (tail.length + 1)) :=
    ((head :: tail).eraseIdx i.val).filter
      (fun x => lt x ((head :: tail)[i.val]'i.isLt))
  let right (i : Fin (tail.length + 1)) :=
    ((head :: tail).eraseIdx i.val).filter
      (fun x => !(lt x ((head :: tail)[i.val]'i.isLt)))
  let L (i : Fin (tail.length + 1)) :=
    ∫⁻ k : Nat, (k : ℝ≥0∞) ∂(exerciseLaw lt (left i)).toMeasure
  let R (i : Fin (tail.length + 1)) :=
    ∫⁻ k : Nat, (k : ℝ≥0∞) ∂(exerciseLaw lt (right i)).toMeasure
  let W : ℝ≥0∞ := (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹)
  have hL (i) : L i ≠ ∞ := exerciseLaw_lintegral_ne_top lt (left i)
  have hR (i) : R i ≠ ∞ := exerciseLaw_lintegral_ne_top lt (right i)
  have hterm (i) : L i + R i ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hL i, hR i⟩
  have hsum : (∑ i : Fin (tail.length + 1), L i + R i) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun i _ => hterm i)
  have hW : W ≠ ∞ := by simp [W]
  have hreal (i) : (L i + R i).toReal =
      exerciseMean lt (left i) + exerciseMean lt (right i) := by
    rw [ENNReal.toReal_add (hL i) (hR i)]
    exact congrArg₂ (fun a b : ℝ => a + b)
      (exerciseMean_eq_toReal_lintegral lt (left i)).symm
      (exerciseMean_eq_toReal_lintegral lt (right i)).symm
  rw [exerciseMean_eq_toReal_lintegral, exerciseLaw_lintegral_cons]
  change (W * (∑ i : Fin (tail.length + 1), L i + R i) +
      ((4 * tail.length + 3 : Nat) : ℝ≥0∞)).toReal =
    (((tail.length + 1 : Nat) : ℝ)⁻¹) *
      (∑ i : Fin (tail.length + 1),
        exerciseMean lt (left i) + exerciseMean lt (right i)) +
      ((4 * tail.length + 3 : Nat) : ℝ)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hW hsum) (ENNReal.natCast_ne_top _),
    ENNReal.toReal_mul]
  simp only [W, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [ENNReal.toReal_sum (fun i _ => hterm i)]
  simp only [hreal]

private theorem exercise_lintegral_run (lt : α → α → Bool) (xs : List α) :
    (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(exerciseLaw lt xs).toMeasure) =
      ∑' result, run lt xs result * (result.2.1 : ℝ≥0∞) := by
  rw [lintegral_nat_eq, exerciseLaw, weighted_map]

private theorem literal_lintegral_run (lt : α → α → Bool) (xs : List α) :
    (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(literalLaw lt xs).toMeasure) =
      ∑' result, run lt xs result * ((result.2.1 + result.2.2 : Nat) : ℝ≥0∞) := by
  rw [lintegral_nat_eq, literalLaw, weighted_map]

/-- Compare the two observations through their common actual run, preserving
its coupling. No integral comparison across unrelated marginal measures occurs. -/
theorem literalMean_comparison (lt : α → α → Bool) (xs : List α) :
    exerciseMean lt xs ≤ literalMean lt xs ∧
      literalMean lt xs ≤ 2 * exerciseMean lt xs := by
  have hlo :
      (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(exerciseLaw lt xs).toMeasure) ≤
        (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(literalLaw lt xs).toMeasure) := by
    rw [exercise_lintegral_run, literal_lintegral_run]
    apply weighted_mono_support
    intro result hr
    exact_mod_cast (literalCost_comparison lt xs result hr).1
  have hup :
      (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(literalLaw lt xs).toMeasure) ≤
        2 * (∫⁻ k : Nat, (k : ℝ≥0∞) ∂(exerciseLaw lt xs).toMeasure) := by
    rw [literal_lintegral_run, exercise_lintegral_run]
    calc
      _ ≤ ∑' result, run lt xs result * (2 * (result.2.1 : ℝ≥0∞)) := by
        apply weighted_mono_support
        intro result hr
        exact_mod_cast (literalCost_comparison lt xs result hr).2
      _ = _ := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro result
        exact mul_left_comm _ _ _
  constructor
  · rw [exerciseMean_eq_toReal_lintegral, literalMean_eq_toReal_lintegral]
    exact ENNReal.toReal_mono (literalLaw_lintegral_ne_top lt xs) hlo
  · rw [literalMean_eq_toReal_lintegral, exerciseMean_eq_toReal_lintegral]
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top 2) (exerciseLaw_lintegral_ne_top lt xs)) hup
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h

/-- A source-specific all-false family keeps its quadratic actual mean. -/
theorem exerciseMean_of_all_false (lt : α → α → Bool) (xs : List α)
    (hf : ∀ a ∈ xs, ∀ b ∈ xs, lt a b = false) :
    exerciseMean lt xs = ((2 * xs.length ^ 2 + 2 * xs.length + 1 : Nat) : ℝ) := by
  have h := congrArg (PMF.map (Prod.fst : Nat × Nat → Nat))
    (jointCostLaw_of_all_false lt xs hf)
  have hp : exerciseLaw lt xs = PMF.pure (2 * xs.length ^ 2 + 2 * xs.length + 1) := by
    simpa only [exerciseLaw, PMF.map_comp, Function.comp_def, PMF.pure_map] using h
  simp [exerciseMean, hp, PMF.toMeasure_pure]

/-- Random order among equal-key tags cannot improve this measured body cost. -/
theorem literalMean_of_all_false (lt : α → α → Bool) (xs : List α)
    (hf : ∀ a ∈ xs, ∀ b ∈ xs, lt a b = false) :
    literalMean lt xs = ((2 * xs.length ^ 2 + 5 * xs.length + 1 : Nat) : ℝ) := by
  have h := congrArg (PMF.map (fun cost : Nat × Nat => cost.1 + cost.2))
    (jointCostLaw_of_all_false lt xs hf)
  have hp : literalLaw lt xs =
      PMF.pure (2 * xs.length ^ 2 + 2 * xs.length + 1 + 3 * xs.length) := by
    simpa only [literalLaw, PMF.map_comp, Function.comp_def, PMF.pure_map] using h
  have hcost : 2 * xs.length ^ 2 + 2 * xs.length + 1 + 3 * xs.length =
      2 * xs.length ^ 2 + 5 * xs.length + 1 := by omega
  rw [hcost] at hp
  simp [literalMean, hp, PMF.toMeasure_pure]

end
end Resources.RandomQuickSort
