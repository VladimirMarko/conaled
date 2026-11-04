import Applications.Resources.UniformQuickSortMean
import Examples.QuickSortMean
import Examples.QuickSortTransport
import Examples.PermutationTail
import Mathlib.Tactic

/-!
# Connected actual uniform-input means and their boundaries

The three-key calculation is retained twice: the actual revealed-head events
have costs 25, 21, 25 and mass 1/3 each, while the universal rank/induction result
gives the same 71/3. Labels have no order or default instance. An outside label
deliberately shares a selected key. Arbitrary payloads retain their occurrences,
and the equal-key tagged family exhibits the distinct-key hypothesis's role.

The imported conditional-tail and transport examples retain the changed full
environment, biased outside-subset masses 1/3 and 2/3, duplicate payload mapping,
and comparator-sensitive literal-cost boundaries. No independence is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.UniformQuickSortMean

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationOrder
open Applications.Probability.PermutationTail
open Resources.UniformQuickSortMean
open scoped ENNReal BigOperators

universe u v
variable {α : Type u} {κ : Type v}

local instance emptyMeasurableSpace : MeasurableSpace (Equiv.Perm Empty) := ⊤
local instance emptyMeasurableSingletons : MeasurableSingletonClass (Equiv.Perm Empty) :=
  ⟨fun _ => trivial⟩

/-- Empty labels still have an identity permutation, and the source nil tariff is 1. -/
theorem empty_labels_mean :
    meanBy ([] : List Empty) (fun a _ => nomatch a) ∅ = 1 :=
  meanBy_empty [] (fun a => nomatch a) _

theorem arbitrary_empty (lt : α → α → Bool) : inputMeanBy lt [] = 1 := inputMeanBy_nil lt

theorem arbitrary_singleton (lt : α → α → Bool) (x : α) :
    inputMeanBy lt [x] = 5 := inputMeanBy_singleton lt x

/-- Either branch orientation on a two-element input costs 5+1+7=13. -/
theorem actual_pair_cost (lt : α → α → Bool) (a b : α) :
    Resources.QuickSort.exerciseCost lt [a, b] = 13 := by
  rw [Resources.QuickSort.exerciseCost_cons]
  cases h : lt b a <;> simp [h]

theorem two_orders :
    Resources.QuickSort.exerciseCost (fun a b : Nat => decide (a < b)) [0, 1] = 13 ∧
      Resources.QuickSort.exerciseCost (fun a b : Nat => decide (a < b)) [1, 0] = 13 :=
  ⟨actual_pair_cost _ _ _, actual_pair_cost _ _ _⟩

theorem two_input_means :
    inputMean (id : Nat → Nat) [0, 1] = 13 ∧ inputMean (id : Nat → Nat) [1, 0] = 13 := by
  constructor <;> rw [inputMean_eq_closedForm _ _ (by decide)] <;>
    exact Examples.QuickSortMean.two_mean

private theorem observed_card_one {I : Type*} [DecidableEq I]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (lt : I → I → Bool) (S : Finset I) (hcard : S.card = 1) (π : Equiv.Perm I) :
    observedCost positions lt S π = 5 := by
  have hlen : (restrictedOrder positions S π).length = 1 :=
    (restrictedOrder_length positions hnd hcomplete S π).trans hcard
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  simp [observedCost, ha]

private theorem observed_card_two {I : Type*} [DecidableEq I]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (lt : I → I → Bool) (S : Finset I) (hcard : S.card = 2) (π : Equiv.Perm I) :
    observedCost positions lt S π = 13 := by
  have hlen : (restrictedOrder positions S π).length = 2 :=
    (restrictedOrder_length positions hnd hcomplete S π).trans hcard
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  unfold observedCost
  rw [hab, actual_pair_cost]
  norm_num

/-! ## Three selected labels inside a larger environment -/

inductive Label
  | high | low | middle | outside
  deriving DecidableEq

instance instFintypeLabel : Fintype Label where
  elems := {Label.high, Label.low, Label.middle, Label.outside}
  complete := by
    intro x
    cases x <;> simp

open Label

def positions : List Label := [middle, outside, high, low]
def selected : Finset Label := {low, middle, high}

def key : Label → Int
  | high => 10
  | low => -5
  | middle => 7
  | outside => 10

def comparator (a b : Label) : Bool := decide (key a < key b)

local instance labelMeasurableSpace : MeasurableSpace (Equiv.Perm Label) := ⊤
local instance labelMeasurableSingletons : MeasurableSingletonClass (Equiv.Perm Label) :=
  ⟨fun _ => trivial⟩

noncomputable def law : Measure (Equiv.Perm Label) := uniformOn Set.univ

theorem positions_nodup : positions.Nodup := by decide

theorem positions_complete (a : Label) : a ∈ positions := by
  cases a <;> decide

theorem selected_keys : Set.InjOn key (selected : Set Label) := by
  intro a ha b hb h
  cases a <;> cases b <;> simp_all [selected, key]

theorem selected_card : selected.card = 3 := by decide

/-- The outside collision makes a global injectivity premise unusable here. -/
theorem outside_collision : outside ∉ selected ∧ key outside = key high ∧
    ¬ Function.Injective key := by
  refine ⟨by decide, rfl, ?_⟩
  intro h
  have heq : outside = high := h rfl
  cases heq

theorem low_children :
    leftChild comparator selected low = ∅ ∧
      rightChild comparator selected low = {middle, high} := by decide

theorem middle_children :
    leftChild comparator selected middle = {low} ∧
      rightChild comparator selected middle = {high} := by decide

theorem high_children :
    leftChild comparator selected high = {low, middle} ∧
      rightChild comparator selected high = ∅ := by decide

/-- Cost 21 is from two singleton recursive calls and source toll 11. -/
theorem middle_actual_cost (π : Equiv.Perm Label)
    (hπ : π ∈ firstEvent (restrictedOrder positions selected) middle) :
    observedCost positions comparator selected π = 21 := by
  rw [observedCost_on_first positions positions_nodup positions_complete comparator selected middle π hπ,
    middle_children.1, middle_children.2,
    observed_card_one positions positions_nodup positions_complete comparator {low} (by decide),
    observed_card_one positions positions_nodup positions_complete comparator {high} (by decide),
    selected_card]
  norm_num

/-- The extreme ranks have an empty child (cost 1), a pair (cost 13), and toll 11. -/
theorem low_actual_cost (π : Equiv.Perm Label)
    (hπ : π ∈ firstEvent (restrictedOrder positions selected) low) :
    observedCost positions comparator selected π = 25 := by
  rw [observedCost_on_first positions positions_nodup positions_complete comparator selected low π hπ,
    low_children.1, low_children.2,
    observed_card_two positions positions_nodup positions_complete comparator {middle, high}
      (by decide), selected_card]
  norm_num [observedCost, restrictedOrder]

theorem high_actual_cost (π : Equiv.Perm Label)
    (hπ : π ∈ firstEvent (restrictedOrder positions selected) high) :
    observedCost positions comparator selected π = 25 := by
  rw [observedCost_on_first positions positions_nodup positions_complete comparator selected high π hπ,
    high_children.1, high_children.2,
    observed_card_two positions positions_nodup positions_complete comparator {low, middle}
      (by decide), selected_card]
  norm_num [observedCost, restrictedOrder]

theorem middle_first_mass : law (firstEvent (restrictedOrder positions selected) middle) = 1 / 3 := by
  unfold law
  rw [uniformOn_firstEvent positions positions_nodup positions_complete selected middle (by decide),
    selected_card]
  norm_num [one_div]

theorem low_first_mass : law (firstEvent (restrictedOrder positions selected) low) = 1 / 3 := by
  unfold law
  rw [uniformOn_firstEvent positions positions_nodup positions_complete selected low (by decide),
    selected_card]
  norm_num [one_div]

theorem high_first_mass : law (firstEvent (restrictedOrder positions selected) high) = 1 / 3 := by
  unfold law
  rw [uniformOn_firstEvent positions positions_nodup positions_complete selected high (by decide),
    selected_card]
  norm_num [one_div]

theorem extreme_first_mass :
    law (firstEvent (restrictedOrder positions selected) low ∪
      firstEvent (restrictedOrder positions selected) high) = 2 / 3 := by
  rw [measure_union
    (firstEvents_disjoint positions selected (by decide : low ∈ selected)
      (by decide : high ∈ selected) (by decide : low ≠ high)) (by trivial),
    low_first_mass, high_first_mass]
  have h : (1 / 3 : NNReal) + 1 / 3 = 2 / 3 := by norm_num
  have h3 : (3 : NNReal) ≠ 0 := by norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_div (p := 1) h3,
    ENNReal.coe_div (p := 2) h3, ENNReal.coe_one, ENNReal.coe_ofNat] using
    congrArg (fun x : NNReal => (x : ENNReal)) h

private theorem conditional_of_constant (a : Label) (ha : a ∈ selected) (c : ℝ)
    (hc : ∀ π ∈ firstEvent (restrictedOrder positions selected) a,
      observedCost positions comparator selected π = c) :
    (∫ π, observedCost positions comparator selected π ∂
      law[|firstEvent (restrictedOrder positions selected) a]) = c := by
  let : IsProbabilityMeasure (law[|firstEvent (restrictedOrder positions selected) a]) := by
    unfold law
    exact cond_isProbabilityMeasure
      (ne_of_gt (firstEvent_positive_finite positions positions_nodup positions_complete selected a ha).1)
  rw [integral_congr_ae (ae_cond_of_forall_mem (by trivial) hc)]
  simp

theorem middle_conditional_mean :
    (∫ π, observedCost positions comparator selected π ∂
      law[|firstEvent (restrictedOrder positions selected) middle]) = 21 :=
  conditional_of_constant middle (by decide) 21 middle_actual_cost

theorem low_conditional_mean :
    (∫ π, observedCost positions comparator selected π ∂
      law[|firstEvent (restrictedOrder positions selected) low]) = 25 :=
  conditional_of_constant low (by decide) 25 low_actual_cost

theorem high_conditional_mean :
    (∫ π, observedCost positions comparator selected π ∂
      law[|firstEvent (restrictedOrder positions selected) high]) = 25 :=
  conditional_of_constant high (by decide) 25 high_actual_cost

/-- This computes the actual integral through its proved head partition and
the independently derived execution costs; it does not reduce a closed form. -/
theorem three_mean_from_heads : meanBy positions comparator selected = (71 : ℝ) / 3 := by
  let term : Label → ℝ := fun a =>
    meanBy positions comparator (leftChild comparator selected a) +
      meanBy positions comparator (rightChild comparator selected a) + 11
  have hlo : term low = 25 := by
    have h := (conditional_mean positions positions_nodup positions_complete comparator
      selected low (by decide)).symm.trans low_conditional_mean
    simpa [term, selected_card] using h
  have hmid : term middle = 21 := by
    have h := (conditional_mean positions positions_nodup positions_complete comparator
      selected middle (by decide)).symm.trans middle_conditional_mean
    simpa [term, selected_card] using h
  have hhi : term high = 25 := by
    have h := (conditional_mean positions positions_nodup positions_complete comparator
      selected high (by decide)).symm.trans high_conditional_mean
    simpa [term, selected_card] using h
  have hsum : (∑ a ∈ selected, term a) = term low + term middle + term high := by
    simp [selected, add_assoc]
  rw [meanBy_recurrence positions positions_nodup positions_complete comparator selected
    (by decide), selected_card]
  change (1 / (3 : ℝ)) * (∑ a ∈ selected, term a) = 71 / 3
  rw [hsum, hlo, hmid, hhi]
  norm_num

/-- The separate universal rank/cardinality proof gives the same expectation
despite unsorted label positions and the deliberate outside key collision. -/
theorem three_mean_from_closedForm : meanBy positions comparator selected = (71 : ℝ) / 3 := by
  unfold comparator
  rw [meanBy_eq_closedForm positions positions_nodup positions_complete key selected selected_keys,
    selected_card]
  exact Examples.QuickSortMean.three_mean

theorem low_empty_actual_child (π : Equiv.Perm Label)
    (hπ : π ∈ firstEvent (restrictedOrder positions selected) low) :
    (restrictedOrder positions selected π).tail.filter (fun b => comparator b low) = [] := by
  rw [left_filter_on_first positions positions_nodup comparator selected low π hπ, low_children.1]
  simp [restrictedOrder]

theorem low_empty_child_mean :
    (∫ π, observedCost positions comparator (leftChild comparator selected low) π ∂
      law[|firstEvent (restrictedOrder positions selected) low]) = 1 := by
  unfold law
  rw [child_integral_cond positions positions_nodup positions_complete comparator selected low
    (by decide) _ (leftChild_subset_erase comparator selected low), low_children.1,
    meanBy_empty positions positions_complete]

theorem high_empty_child_mean :
    (∫ π, observedCost positions comparator (rightChild comparator selected high) π ∂
      law[|firstEvent (restrictedOrder positions selected) high]) = 1 := by
  unfold law
  rw [child_integral_cond positions positions_nodup positions_complete comparator selected high
    (by decide) _ (rightChild_subset_erase comparator selected high), high_children.2,
    meanBy_empty positions positions_complete]

/-! ## Arbitrary payloads and actual growing families -/

theorem arbitrary_payload_occurrences (xs : List α) (π : Equiv.Perm (Fin xs.length)) :
    (occurrenceInput xs π).Perm xs ∧ (occurrenceInput xs π).length = xs.length :=
  ⟨occurrenceInput_perm xs π, occurrenceInput_length xs π⟩

theorem arbitrary_tagged_three (x y z : α) :
    inputMean (Prod.fst : Int × α → Int) [(10, x), (-5, y), (7, z)] = (71 : ℝ) / 3 := by
  rw [inputMean_eq_closedForm _ _ (by simp)]
  exact Examples.QuickSortMean.three_mean

def taggedEqual (n : Nat) : List (Nat × Nat) := (List.range n).map (fun i => (0, i))

theorem taggedEqual_payloads_distinct (n : Nat) : (taggedEqual n).Nodup := by
  apply List.Nodup.map _ (List.nodup_range (n := n))
  intro i j h
  exact congrArg Prod.snd h

theorem taggedEqual_mean (n : Nat) :
    inputMean Prod.fst (taggedEqual n) = ((2 * n ^ 2 + 2 * n + 1 : Nat) : ℝ) := by
  have h := inputMean_of_equal_keys Prod.fst (taggedEqual n) 0 (by
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    rfl)
  simpa only [taggedEqual, List.length_map, List.length_range] using h

/-- Distinct records are insufficient: three equal sort keys give 25, not 71/3. -/
theorem equal_key_counterexample :
    (taggedEqual 3).Nodup ∧ ¬ ((taggedEqual 3).map Prod.fst).Nodup ∧
      inputMean Prod.fst (taggedEqual 3) = 25 ∧
      inputMean Prod.fst (taggedEqual 3) ≠ (71 : ℝ) / 3 := by
  refine ⟨taggedEqual_payloads_distinct 3, by decide, ?_, ?_⟩ <;>
    rw [taggedEqual_mean] <;> norm_num

def taggedRange (payload : Nat → α) (n : Nat) : List (Nat × α) :=
  (List.range n).map (fun i => (i, payload i))

theorem taggedRange_length (payload : Nat → α) (n : Nat) :
    (taggedRange payload n).length = n := by simp [taggedRange]

theorem taggedRange_keys (payload : Nat → α) (n : Nat) :
    ((taggedRange payload n).map Prod.fst).Nodup := by
  simpa [taggedRange, List.map_map, Function.comp_def] using (List.nodup_range (n := n))

theorem taggedRange_mean (payload : Nat → α) (n : Nat) :
    inputMean Prod.fst (taggedRange payload n) = Resources.QuickSortMean.closedForm n := by
  rw [inputMean_eq_closedForm _ _ (taggedRange_keys payload n), taggedRange_length]

theorem arbitrary_payload_growth (payload : Nat → α) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => inputMean Prod.fst (taggedRange payload n))
      (fun n : Nat => (n : ℝ) * Real.logb 2 (n : ℝ)) :=
  inputMean_family_isBigO Prod.fst (taggedRange payload)
    (taggedRange_length payload) (taggedRange_keys payload)

theorem taggedRange_scalar_bound (payload : Nat → α) (n : Nat) (hn : 2 ≤ n) :
    0 ≤ inputMean Prod.fst (taggedRange payload n) ∧
      inputMean Prod.fst (taggedRange payload n) ≤ 32 * ((n : ℝ) * Real.logb 2 (n : ℝ)) := by
  constructor
  · exact inputMean_nonneg _ _ (taggedRange_keys payload n)
  · simpa only [taggedRange_length] using inputMean_le_nlogb Prod.fst (taggedRange payload n)
      (taggedRange_keys payload n) (by simpa only [taggedRange_length] using hn)

theorem taggedRange_literal_bound (payload : Nat → α) (n : Nat) (hn : 2 ≤ n) :
    inputLiteralMean Prod.fst (taggedRange payload n) ≤
      64 * ((n : ℝ) * Real.logb 2 (n : ℝ)) := by
  simpa only [taggedRange_length] using inputLiteralMean_le_nlogb Prod.fst (taggedRange payload n)
    (taggedRange_keys payload n) (by simpa only [taggedRange_length] using hn)

theorem actual_zero_log_boundary [LinearOrder κ] (key : α → κ) (C : ℝ) :
    ¬ inputMean key [] ≤ C * ((0 : ℝ) * Real.logb 2 0) := by simp

theorem actual_one_log_boundary [LinearOrder κ] (key : α → κ) (x : α) (C : ℝ) :
    ¬ inputMean key [x] ≤ C * ((1 : ℝ) * Real.logb 2 1) := by simp

end Examples.UniformQuickSortMean
