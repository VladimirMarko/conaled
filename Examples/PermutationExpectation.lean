import Applications.Probability.PermutationExpectation
import Examples.PermutationExpectationBoundary
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Actual preceding counts, ordinal positions and numeric minima

The Fin3 subset `{0, 1}` has expected strict-before count `1/3` and actual
one-based first position `4/3`. Both ENNReal and real count means use the
public theorem, and the position mean observes the finite-image minimum.
A nonidentity rank equivalence checks the pointwise bridge without an
assumption that ranks follow the keys' order. Fin4 supplies another proper
subset with means `2/3` and `5/3`.

The Int-valued priorities `100 + 10*j` have the same count mean. Their raw
minimum is defined by the actual numeric image, then related to the ordinal
minimum through the existing monotone-image law. Its real mean is `310/3`,
not the ordinal mean `4/3`. Finite integrability is used in that affine
expectation calculation; no raw minimum is defined to be the desired answer.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationExpectation

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationExpectation
open scoped ENNReal

local instance : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤

def selected : Finset (Fin 3) := {0, 1}
def rank3 : Fin 3 ≃ Fin 3 := Equiv.refl _

theorem selected_nonempty : selected.Nonempty := by decide

noncomputable def law3 : Measure (Equiv.Perm (Fin 3)) := uniformOn Set.univ

/-- The value bound is independent of probability and priority injectivity. -/
theorem count_le_one (π : Equiv.Perm (Fin 3)) :
    beforeCount rank3 selected π ≤ 1 := by
  simpa [selected, Nat.card_eq_fintype_card] using beforeCount_le rank3 selected π

theorem count_mean_ennreal :
    (∫⁻ π, (beforeCount rank3 selected π : ℝ≥0∞) ∂law3) = 1 / 3 := by
  calc
    _ = ((Nat.card (Fin 3) - selected.card : ℕ) : ℝ≥0∞) /
        ((selected.card + 1 : ℕ) : ℝ≥0∞) :=
      lintegral_beforeCount_uniformOn rank3 rank3.injective selected
    _ = 1 / 3 := by norm_num [selected, Nat.card_eq_fintype_card]

theorem count_mean_real :
    (∫ π, (beforeCount rank3 selected π : ℝ) ∂law3) = 1 / 3 := by
  calc
    _ = ((Nat.card (Fin 3) - selected.card : ℕ) : ℝ) /
        ((selected.card + 1 : ℕ) : ℝ) :=
      integral_beforeCount_uniformOn rank3 rank3.injective selected
    _ = 1 / 3 := by norm_num [selected, Nat.card_eq_fintype_card]

/-- The actual one-based minimum of the selected keys' assigned global ranks. -/
def firstPosition3 (π : Equiv.Perm (Fin 3)) : ℕ :=
  ((selected.image (fun a => rank3 (π a))).min'
    (selected_nonempty.image (fun a => rank3 (π a)))).val + 1

theorem first_position_bridge (π : Equiv.Perm (Fin 3)) :
    firstPosition3 π = beforeCount rank3 selected π + 1 := by
  unfold firstPosition3
  rw [beforeCount_rank_eq rank3 selected selected_nonempty π]

theorem first_position_mean : (∫ π, (firstPosition3 π : ℝ) ∂law3) = 4 / 3 := by
  calc
    _ = ((3 + 1 : ℕ) : ℝ) / ((selected.card + 1 : ℕ) : ℝ) :=
      integral_firstPosition_uniformOn rank3 selected selected_nonempty
    _ = 4 / 3 := by norm_num [selected]

def swappedRank : Fin 3 ≃ Fin 3 := Equiv.swap 0 2

theorem swappedRank_not_monotone : ¬ Monotone swappedRank := by decide

/-- A rank equivalence need not follow the keys' order. The count uses its
actual finite-image minimum through the generic pointwise bridge. -/
theorem swapped_count :
    beforeCount swappedRank selected (Equiv.refl (Fin 3)) = 1 := by
  calc
    _ = ((selected.image (fun a => swappedRank ((Equiv.refl (Fin 3)) a))).min'
        (selected_nonempty.image (fun a => swappedRank ((Equiv.refl (Fin 3)) a)))).val :=
      beforeCount_rank_eq swappedRank selected selected_nonempty (Equiv.refl (Fin 3))
    _ = 1 := by decide

theorem swapped_first_position :
    ((selected.image (fun a => swappedRank ((Equiv.refl (Fin 3)) a))).min'
      (selected_nonempty.image (fun a => swappedRank ((Equiv.refl (Fin 3)) a)))).val + 1 = 2 := by
  simpa only [swapped_count] using
    congrArg (fun n : ℕ => n + 1)
      (beforeCount_rank_eq swappedRank selected selected_nonempty
        (Equiv.refl (Fin 3))).symm

def selected4 : Finset (Fin 4) := {0, 3}
def rank4 : Fin 4 ≃ Fin 4 := Equiv.refl _

theorem selected4_nonempty : selected4.Nonempty := by decide

noncomputable def law4 : Measure (Equiv.Perm (Fin 4)) := uniformOn Set.univ

def firstPosition4 (π : Equiv.Perm (Fin 4)) : ℕ :=
  ((selected4.image (fun a => rank4 (π a))).min'
    (selected4_nonempty.image (fun a => rank4 (π a)))).val + 1

theorem count_mean_four :
    (∫ π, (beforeCount rank4 selected4 π : ℝ) ∂law4) = 2 / 3 := by
  calc
    _ = ((Nat.card (Fin 4) - selected4.card : ℕ) : ℝ) /
        ((selected4.card + 1 : ℕ) : ℝ) :=
      integral_beforeCount_uniformOn rank4 rank4.injective selected4
    _ = 2 / 3 := by norm_num [selected4, Nat.card_eq_fintype_card]

theorem first_position_mean_four :
    (∫ π, (firstPosition4 π : ℝ) ∂law4) = 5 / 3 := by
  calc
    _ = ((4 + 1 : ℕ) : ℝ) / ((selected4.card + 1 : ℕ) : ℝ) :=
      integral_firstPosition_uniformOn rank4 selected4 selected4_nonempty
    _ = 5 / 3 := by norm_num [selected4]

/-! ## The actual raw numeric minimum has a different expected value -/

def numericPriority (j : Fin 3) : ℤ := 100 + 10 * (j.val : ℤ)

theorem numericPriority_injective : Function.Injective numericPriority := by decide

/-- This monotonicity is used for the numeric minimum bridge, not required
as an index-order premise of the general count-mean theorem. -/
theorem numericPriority_monotone : Monotone numericPriority := by decide

theorem numeric_count_mean :
    (∫ π, (beforeCount numericPriority selected π : ℝ) ∂law3) = 1 / 3 := by
  calc
    _ = ((Nat.card (Fin 3) - selected.card : ℕ) : ℝ) /
        ((selected.card + 1 : ℕ) : ℝ) :=
      integral_beforeCount_uniformOn numericPriority numericPriority_injective selected
    _ = 1 / 3 := by norm_num [selected, Nat.card_eq_fintype_card]

/-- Take the actual minimum of the selected keys' assigned numeric values. -/
def rawMinimum (π : Equiv.Perm (Fin 3)) : ℤ :=
  (selected.image (fun a => numericPriority (π a))).min'
    (selected_nonempty.image (fun a => numericPriority (π a)))

theorem rawMinimum_eq_count (π : Equiv.Perm (Fin 3)) :
    rawMinimum π = 100 + 10 * (beforeCount rank3 selected π : ℤ) := by
  have hmin : rawMinimum π =
      numericPriority ((selected.image π).min' (selected_nonempty.image π)) := by
    simpa only [rawMinimum, Finset.image_image] using
      (Finset.min'_image numericPriority_monotone (selected.image π)
        ((selected_nonempty.image π).image numericPriority))
  calc
    rawMinimum π =
        numericPriority ((selected.image π).min' (selected_nonempty.image π)) := hmin
    _ = 100 + 10 * (beforeCount rank3 selected π : ℤ) := by
      unfold numericPriority
      rw [beforeCount_rank_eq rank3 selected selected_nonempty π]

theorem raw_minimum_mean : (∫ π, (rawMinimum π : ℝ) ∂law3) = 310 / 3 := by
  letI : IsProbabilityMeasure law3 := by
    unfold law3
    infer_instance
  have hcount : Integrable (fun π => (beforeCount rank3 selected π : ℝ)) law3 :=
    Integrable.of_finite
  have hconstant : Integrable (fun _π : Equiv.Perm (Fin 3) => (100 : ℝ)) law3 :=
    Integrable.of_finite
  calc
    _ = ∫ π, (100 : ℝ) + 10 * (beforeCount rank3 selected π : ℝ) ∂law3 := by
      apply integral_congr_ae
      filter_upwards [] with π
      rw [rawMinimum_eq_count]
      push_cast
    _ = (∫ _π : Equiv.Perm (Fin 3), (100 : ℝ) ∂law3) +
        ∫ π, (10 : ℝ) * (beforeCount rank3 selected π : ℝ) ∂law3 :=
      integral_add hconstant (hcount.const_mul 10)
    _ = 100 + 10 * (1 / 3 : ℝ) := by
      rw [integral_const_mul, count_mean_real]
      simp
    _ = 310 / 3 := by norm_num

theorem raw_mean_differs_from_position_mean :
    (∫ π, (rawMinimum π : ℝ) ∂law3) ≠ ∫ π, (firstPosition3 π : ℝ) ∂law3 := by
  rw [raw_minimum_mean, first_position_mean]
  norm_num

end Examples.PermutationExpectation
