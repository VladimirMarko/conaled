import Applications.Probability.PermutationExpectation
import Applications.Probability.PermutationTail
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Boundaries of the global preceding-count mean

Empty sets retain their actual count, with no first-member interpretation.
The deterministic complement bound applies to tied priorities, although the
injective-priority mean does not. A singleton selected from the sampled
global minimum also has a different mean from a fixed singleton.

The final example conditions the actual Fin3 global order on key `0` being
first. The count before the fixed singleton `{1}` then has mean `3/2`, while
its original mean is `1`. Its relative-order observation has the same
singleton HasLaw under both measures. The count is connected to the actual
rank minimum and conditional tail; no new independent sample is introduced.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationExpectationBoundary

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationExpectation
open Applications.Probability.PermutationOrder
open Applications.Probability.PermutationTail
open scoped ENNReal ProbabilityTheory

local instance : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 3)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm (Fin 2)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 2)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm Empty) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm Empty) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (Fin 3)) := ⊤
local instance : MeasurableSingletonClass (List (Fin 3)) := ⟨fun _ => trivial⟩

def rank3 : Fin 3 ≃ Fin 3 := Equiv.refl _

noncomputable def original : Measure (Equiv.Perm (Fin 3)) := uniformOn Set.univ

local instance original_isProbabilityMeasure : IsProbabilityMeasure original := by
  dsimp [original]
  infer_instance

/-- All three keys satisfy the vacuous comparison against an empty subset. -/
theorem empty_subset_count (π : Equiv.Perm (Fin 3)) :
    beforeCount rank3 ∅ π = 3 := by
  simpa using beforeCount_empty rank3 π

theorem empty_subset_mean :
    (∫ π, (beforeCount rank3 ∅ π : ℝ) ∂original) = 3 := by
  simpa [original] using
    integral_beforeCount_uniformOn rank3 rank3.injective (∅ : Finset (Fin 3))

/-- This value lies beyond the universe; no nonempty rank minimum is invoked. -/
theorem empty_subset_sentinel (π : Equiv.Perm (Fin 3)) :
    beforeCount rank3 ∅ π + 1 = 4 := by
  rw [empty_subset_count]

def emptyPriority : Empty → ℕ := fun a => nomatch a

private theorem emptyPriority_injective : Function.Injective emptyPriority := by
  intro a
  exact a.elim

theorem empty_indices_normalized :
    uniformOn (Set.univ : Set (Equiv.Perm Empty)) Set.univ = 1 := by
  simp

theorem empty_indices_count (π : Equiv.Perm Empty) :
    beforeCount emptyPriority ∅ π = 0 := by
  simpa using beforeCount_empty emptyPriority π

/-- The generic mean permits an empty index type; no key is manufactured. -/
theorem empty_indices_mean :
    (∫ π : Equiv.Perm Empty, (beforeCount emptyPriority ∅ π : ℝ)
      ∂uniformOn Set.univ) = 0 := by
  simpa using
    integral_beforeCount_uniformOn emptyPriority emptyPriority_injective
      (∅ : Finset Empty)

def singleton : Finset (Fin 3) := {1}

private theorem singleton_nonempty : singleton.Nonempty := by decide

/-- The singleton's actual image minimum is the assigned zero-based rank of key 1. -/
theorem singleton_count_eq (π : Equiv.Perm (Fin 3)) :
    beforeCount rank3 singleton π = (π 1).val := by
  simpa [singleton, rank3] using
    beforeCount_rank_eq rank3 singleton singleton_nonempty π

theorem singleton_count_mean :
    (∫ π, (beforeCount rank3 singleton π : ℝ) ∂original) = 1 := by
  simpa [original, singleton] using
    integral_beforeCount_uniformOn rank3 rank3.injective singleton

theorem singleton_first_position_mean :
    (∫ π : Equiv.Perm (Fin 3), (((π 1).val + 1 : ℕ) : ℝ) ∂original) = 2 := by
  have h := integral_firstPosition_uniformOn rank3 singleton singleton_nonempty
  norm_num [singleton, rank3] at h
  simpa [original, Nat.cast_add] using h

/-- With no outsiders, the complement bound forces the actual count to zero. -/
theorem full_subset_count (π : Equiv.Perm (Fin 3)) :
    beforeCount rank3 Finset.univ π = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using beforeCount_le rank3 (Finset.univ : Finset (Fin 3)) π

private theorem full_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty :=
  ⟨0, Finset.mem_univ 0⟩

noncomputable def fullFirstPosition (π : Equiv.Perm (Fin 3)) : ℕ :=
  (((Finset.univ : Finset (Fin 3)).image (fun a => rank3 (π a))).min'
    (full_nonempty.image (fun a => rank3 (π a)))).val + 1

theorem full_subset_first_position_mean :
    (∫ π, (fullFirstPosition π : ℝ) ∂original) = 1 := by
  simpa [original, fullFirstPosition] using
    integral_firstPosition_uniformOn rank3 (Finset.univ : Finset (Fin 3)) full_nonempty

def tiedPriority (_ : Fin 2) : ℕ := 0

def tiedSubset : Finset (Fin 2) := {0}

/-- Strict comparison with the sole selected priority is always false. -/
theorem tied_count (π : Equiv.Perm (Fin 2)) :
    beforeCount tiedPriority tiedSubset π = 0 := by
  simp [beforeCount, tiedPriority, tiedSubset]

/-- The deterministic theorem needs no injectivity and remains applicable. -/
theorem tied_count_bound (π : Equiv.Perm (Fin 2)) :
    beforeCount tiedPriority tiedSubset π ≤ 1 := by
  simpa [tiedSubset] using beforeCount_le tiedPriority tiedSubset π

theorem tied_count_mean :
    (∫ π : Equiv.Perm (Fin 2), (beforeCount tiedPriority tiedSubset π : ℝ)
      ∂uniformOn Set.univ) = 0 := by
  simp only [tied_count, Nat.cast_zero, integral_zero]

theorem tied_formula_value :
    ((Nat.card (Fin 2) - tiedSubset.card : ℕ) : ℝ) /
      ((tiedSubset.card + 1 : ℕ) : ℝ) = 1 / 2 := by
  norm_num [tiedSubset]

/-- Dropping injectivity would predict a positive mean for an identically zero count. -/
theorem tied_mean_ne_formula :
    (∫ π : Equiv.Perm (Fin 2), (beforeCount tiedPriority tiedSubset π : ℝ)
      ∂uniformOn Set.univ) ≠
      ((Nat.card (Fin 2) - tiedSubset.card : ℕ) : ℝ) /
        ((tiedSubset.card + 1 : ℕ) : ℝ) := by
  rw [tied_count_mean, tied_formula_value]
  norm_num

def adaptiveSubset (π : Equiv.Perm (Fin 3)) : Finset (Fin 3) := {π.symm 0}

theorem adaptive_subset_card (π : Equiv.Perm (Fin 3)) :
    (adaptiveSubset π).card = 1 := by
  simp [adaptiveSubset]

/-- The pointwise rank bridge applies even though the mean theorem fixes S earlier. -/
theorem adaptive_count (π : Equiv.Perm (Fin 3)) :
    beforeCount rank3 (adaptiveSubset π) π = 0 := by
  have hS : (adaptiveSubset π).Nonempty := by simp [adaptiveSubset]
  rw [beforeCount_rank_eq rank3 (adaptiveSubset π) hS π]
  simp [adaptiveSubset, rank3]

theorem adaptive_count_mean :
    (∫ π, (beforeCount rank3 (adaptiveSubset π) π : ℝ) ∂original) = 0 := by
  simp only [adaptive_count, Nat.cast_zero, integral_zero]

theorem adaptive_mean_ne_fixed_singleton :
    (∫ π, (beforeCount rank3 (adaptiveSubset π) π : ℝ) ∂original) ≠
      ∫ π, (beforeCount rank3 singleton π : ℝ) ∂original := by
  rw [adaptive_count_mean, singleton_count_mean]
  norm_num

def positions : List (Fin 3) := [0, 1, 2]

private theorem positions_nodup : positions.Nodup := by decide

private theorem positions_complete (a : Fin 3) : a ∈ positions := by
  fin_cases a <;> decide

def globalOrder (π : Equiv.Perm (Fin 3)) : List (Fin 3) :=
  restrictedOrder positions Finset.univ π

def firstZero : Set (Equiv.Perm (Fin 3)) := firstEvent globalOrder 0

noncomputable def afterZero : Measure (Equiv.Perm (Fin 3)) := original[|firstZero]

def tail21 : Set (Equiv.Perm (Fin 3)) := {π | (globalOrder π).tail = [2, 1]}

/-- Conditioning refers to the actual full global order in the original experiment. -/
theorem first_zero_mass : original firstZero = 1 / 3 := by
  simpa [original, firstZero, globalOrder, one_div] using
    uniformOn_firstEvent positions positions_nodup positions_complete
      (Finset.univ : Finset (Fin 3)) 0 (Finset.mem_univ 0)

local instance afterZero_isProbabilityMeasure : IsProbabilityMeasure afterZero := by
  apply cond_isProbabilityMeasure (μ := original) (s := firstZero)
  rw [first_zero_mass]
  norm_num

private theorem remaining_card : ((Finset.univ : Finset (Fin 3)).erase 0).card = 2 :=
  by decide

theorem conditional_tail12_mass :
    afterZero {π | (globalOrder π).tail = [1, 2]} = 1 / 2 := by
  have hmem : ([1, 2] : List (Fin 3)) ∈
      orders positions ((Finset.univ : Finset (Fin 3)).erase 0) := by decide
  calc
    _ = if ([1, 2] : List (Fin 3)) ∈
          orders positions ((Finset.univ : Finset (Fin 3)).erase 0)
        then (Nat.factorial ((Finset.univ : Finset (Fin 3)).erase 0).card : ℝ≥0∞)⁻¹
        else 0 :=
      cond_tail_eq positions positions_nodup positions_complete
        Finset.univ 0 (Finset.mem_univ 0) [1, 2]
    _ = 1 / 2 := by rw [if_pos hmem, remaining_card] <;> norm_num [one_div]

theorem conditional_tail21_mass : afterZero tail21 = 1 / 2 := by
  have hmem : ([2, 1] : List (Fin 3)) ∈
      orders positions ((Finset.univ : Finset (Fin 3)).erase 0) := by decide
  calc
    _ = if ([2, 1] : List (Fin 3)) ∈
          orders positions ((Finset.univ : Finset (Fin 3)).erase 0)
        then (Nat.factorial ((Finset.univ : Finset (Fin 3)).erase 0).card : ℝ≥0∞)⁻¹
        else 0 :=
      cond_tail_eq positions positions_nodup positions_complete
        Finset.univ 0 (Finset.mem_univ 0) [2, 1]
    _ = 1 / 2 := by rw [if_pos hmem, remaining_card] <;> norm_num [one_div]

private theorem supported_head_zero_table :
    ∀ xs ∈ orders positions (Finset.univ : Finset (Fin 3)),
      xs.head? = some 0 → xs = [0, 1, 2] ∨ xs = [0, 2, 1] := by decide

/-- The two cases come from the support of the actual same-sample global order. -/
theorem global_order_of_first_zero (π : Equiv.Perm (Fin 3)) (hπ : π ∈ firstZero) :
    globalOrder π = [0, 1, 2] ∨ globalOrder π = [0, 2, 1] := by
  apply supported_head_zero_table (globalOrder π)
    (restrictedOrder_mem_orders positions positions_nodup positions_complete Finset.univ π)
  exact hπ

/-- Applying key-to-label π to the inverse ordering recovers the listed labels. -/
private theorem map_globalOrder (π : Equiv.Perm (Fin 3)) :
    (globalOrder π).map π = positions := by
  simp [globalOrder, restrictedOrder, positions]

private theorem count_on_first_zero (π : Equiv.Perm (Fin 3)) (hπ : π ∈ firstZero) :
    (beforeCount rank3 singleton π : ℝ) = 1 + tail21.indicator 1 π := by
  classical
  rcases global_order_of_first_zero π hπ with horder | horder
  · have hpoint := congrArg (fun xs : List (Fin 3) => xs[1]?) (map_globalOrder π)
    rw [horder] at hpoint
    have hkey : π 1 = 1 := by simpa [positions] using hpoint
    have hnot : π ∉ tail21 := by
      change (globalOrder π).tail ≠ [2, 1]
      rw [horder]
      decide
    rw [singleton_count_eq, hkey, Set.indicator_of_not_mem hnot] <;> norm_num
  · have hpoint := congrArg (fun xs : List (Fin 3) => xs[2]?) (map_globalOrder π)
    rw [horder] at hpoint
    have hkey : π 1 = 2 := by simpa [positions] using hpoint
    have hmem : π ∈ tail21 := by
      change (globalOrder π).tail = [2, 1]
      simp [horder]
    rw [singleton_count_eq, hkey, Set.indicator_of_mem hmem] <;> norm_num

private theorem conditional_count_moment :
    Integrable (fun π => (beforeCount rank3 singleton π : ℝ)) afterZero ∧
      (∫ π, (beforeCount rank3 singleton π : ℝ) ∂afterZero) = 3 / 2 := by
  have hactual : Integrable (fun π => (beforeCount rank3 singleton π : ℝ)) afterZero :=
    Integrable.of_finite
  have hconst : Integrable (fun _ : Equiv.Perm (Fin 3) => (1 : ℝ)) afterZero :=
    Integrable.of_finite
  have hindicator : Integrable (tail21.indicator (1 : Equiv.Perm (Fin 3) → ℝ)) afterZero :=
    Integrable.of_finite
  have heq : (fun π => (beforeCount rank3 singleton π : ℝ)) =ᵐ[afterZero]
      (fun π => 1 + tail21.indicator 1 π) :=
    ae_cond_of_forall_mem (μ := original) (s := firstZero) (by trivial)
      (fun π hπ => count_on_first_zero π hπ)
  refine ⟨hactual, ?_⟩
  calc
    _ = ∫ π, 1 + tail21.indicator 1 π ∂afterZero := integral_congr_ae heq
    _ = (∫ _ : Equiv.Perm (Fin 3), (1 : ℝ) ∂afterZero) +
        ∫ π, tail21.indicator 1 π ∂afterZero := integral_add hconst hindicator
    _ = 1 + (afterZero tail21).toReal := by
      rw [integral_const, integral_indicator_one (by trivial)]
      simp [measureReal_def]
    _ = 3 / 2 := by
      rw [conditional_tail21_mass]
      norm_num [ENNReal.toReal_div]

/-- The count under the conditioned global environment has a genuinely finite mean. -/
theorem conditional_count_mean :
    (∫ π, (beforeCount rank3 singleton π : ℝ) ∂afterZero) = 3 / 2 :=
  conditional_count_moment.2

theorem placement_means_differ :
    (∫ π, (beforeCount rank3 singleton π : ℝ) ∂afterZero) ≠
      ∫ π, (beforeCount rank3 singleton π : ℝ) ∂original := by
  rw [conditional_count_mean, singleton_count_mean]
  norm_num

def singletonOrder (π : Equiv.Perm (Fin 3)) : List (Fin 3) :=
  restrictedOrder positions singleton π

theorem singleton_order_value (π : Equiv.Perm (Fin 3)) : singletonOrder π = [1] := by
  have hs : orders positions singleton = {([1] : List (Fin 3))} := by decide
  have h := restrictedOrder_mem_orders positions positions_nodup positions_complete singleton π
  rw [hs] at h
  exact Finset.mem_singleton.mp h

/-- The original singleton law comes from XU02's actual projection map. -/
theorem singleton_order_original_hasLaw :
    HasLaw singletonOrder
      (uniformOn (orders positions singleton : Set (List (Fin 3)))) original where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := map_restrictedOrder_uniformOn positions positions_nodup positions_complete singleton

/-- XU03 gives the same observation law under the changed global environment. -/
theorem singleton_order_conditional_hasLaw :
    HasLaw singletonOrder
      (uniformOn (orders positions singleton : Set (List (Fin 3)))) afterZero where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := map_restrictedOrder_cond_first positions positions_nodup positions_complete
    Finset.univ 0 (Finset.mem_univ 0) singleton (by decide)

end Examples.PermutationExpectationBoundary
