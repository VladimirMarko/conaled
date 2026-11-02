import Applications.Probability.PermutationTail
import Examples.PermutationOrder
import Mathlib.Tactic

/-!
# Empty, proper-union and overlap boundaries for paired relative orders

The first cases use the new universal law on the actual pair of restrictions
of one global permutation. Unequal subset sizes do not require covering the
universe. An empty subset contributes its empty list, including when the
entire index type is empty. The latter case also applies the generic pair-
filter HasLaw to the actual old whole-order observation.

The overlap example identifies its actual paired event with the first-key-1
event of the full Fin3 order. Its mass is `1/3`, whereas the product of its
two marginal masses is `1/4`. That argument uses the old whole-order and
conditional-head interfaces; it does not assume disjointness for overlapping
sets or replace the common sample by independent draws.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationJointBoundary

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationOrder
open Applications.Probability.PermutationTail
open Examples.PermutationOrder (positions positions_nodup positions_complete law)
open scoped ENNReal

local instance : MeasurableSpace (Equiv.Perm (Fin 5)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 5)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 4)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 3)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm Empty) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm Empty) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List Empty) := ⊤
local instance : MeasurableSingletonClass (List Empty) := ⟨fun _ => trivial⟩

/-- Shared Fin5 fixture for the proper-union and later conditional examples. -/
def positions5 : List (Fin 5) := [0, 1, 2, 3, 4]

theorem positions5_nodup : positions5.Nodup := by decide

theorem positions5_complete (a : Fin 5) : a ∈ positions5 := by
  fin_cases a <;> decide

noncomputable def law5 : Measure (Equiv.Perm (Fin 5)) := uniformOn Set.univ

def properLeft : Finset (Fin 5) := {0}
def properRight : Finset (Fin 5) := {1, 2, 3}

theorem proper_disjoint : Disjoint properLeft properRight := by decide

/-- Key 4 is unused by either restriction. -/
theorem proper_union_excludes_four : (4 : Fin 5) ∉ properLeft ∪ properRight := by decide

theorem proper_union_ne_univ : properLeft ∪ properRight ≠ Finset.univ := by decide

def properPair (π : Equiv.Perm (Fin 5)) : List (Fin 5) × List (Fin 5) :=
  (restrictedOrder positions5 properLeft π, restrictedOrder positions5 properRight π)

/-- The pair has unequal component lengths and ignores an outside label. -/
theorem proper_pair_mass : law5 {π | properPair π = ([0], [1, 2, 3])} = 1 / 6 := by
  have hmem : ([0] : List (Fin 5)) ∈ orders positions5 properLeft ∧
      ([1, 2, 3] : List (Fin 5)) ∈ orders positions5 properRight := by decide
  calc
    _ = if ([0] : List (Fin 5)) ∈ orders positions5 properLeft ∧
          ([1, 2, 3] : List (Fin 5)) ∈ orders positions5 properRight
        then ((Nat.factorial properLeft.card * Nat.factorial properRight.card : ℕ) : ℝ≥0∞)⁻¹
        else 0 :=
      uniformOn_restrictedOrder_pair_eq positions5 positions5_nodup positions5_complete
        properLeft properRight proper_disjoint [0] [1, 2, 3]
    _ = 1 / 6 := by
      rw [if_pos hmem] <;> norm_num [properLeft, properRight, one_div]

def emptyFullPair (π : Equiv.Perm (Fin 4)) : List (Fin 4) × List (Fin 4) :=
  (restrictedOrder positions ∅ π, restrictedOrder positions Finset.univ π)

/-- The full coordinate is the actual inverse order; the empty coordinate is []. -/
theorem empty_full_value (π : Equiv.Perm (Fin 4)) :
    emptyFullPair π = ([], positions.map π.symm) := by
  simp [emptyFullPair, restrictedOrder]

theorem empty_full_mass : law {π | emptyFullPair π = ([], [0, 1, 2, 3])} = 1 / 24 := by
  have hmem : ([] : List (Fin 4)) ∈ orders positions ∅ ∧
      ([0, 1, 2, 3] : List (Fin 4)) ∈ orders positions Finset.univ := by decide
  calc
    _ = if ([] : List (Fin 4)) ∈ orders positions ∅ ∧
          ([0, 1, 2, 3] : List (Fin 4)) ∈ orders positions Finset.univ
        then ((Nat.factorial (∅ : Finset (Fin 4)).card *
          Nat.factorial (Finset.univ : Finset (Fin 4)).card : ℕ) : ℝ≥0∞)⁻¹
        else 0 :=
      uniformOn_restrictedOrder_pair_eq positions positions_nodup positions_complete
        (∅ : Finset (Fin 4)) Finset.univ (by simp) [] [0, 1, 2, 3]
    _ = 1 / 24 := by rw [if_pos hmem] <;> norm_num [one_div]

private theorem empty_complete (a : Empty) : a ∈ ([] : List Empty) := by cases a

noncomputable def emptyLaw : Measure (Equiv.Perm Empty) := uniformOn Set.univ

def emptyWholeOrder (π : Equiv.Perm Empty) : List Empty :=
  restrictedOrder [] ∅ π

def emptyPair (π : Equiv.Perm Empty) : List Empty × List Empty :=
  (restrictedOrder [] ∅ π, restrictedOrder [] ∅ π)

theorem empty_indices_normalized : emptyLaw Set.univ = 1 := by
  simp [emptyLaw]

theorem empty_pair_value (π : Equiv.Perm Empty) : emptyPair π = ([], []) := by
  simp [emptyPair, restrictedOrder]

/-- The new scalar law retains the empty universe's normalized actual pair. -/
theorem empty_pair_mass : emptyLaw {π | emptyPair π = ([], [])} = 1 := by
  calc
    _ = if ([] : List Empty) ∈ orders [] ∅ ∧ ([] : List Empty) ∈ orders [] ∅
        then ((Nat.factorial (∅ : Finset Empty).card *
          Nat.factorial (∅ : Finset Empty).card : ℕ) : ℝ≥0∞)⁻¹
        else 0 :=
      uniformOn_restrictedOrder_pair_eq ([] : List Empty) (by simp) empty_complete
        (∅ : Finset Empty) ∅ (by simp) [] []
    _ = 1 := by simp [orders]

/-- The generic premise is the old actual whole-order pushforward, not a new draw. -/
theorem empty_whole_hasLaw :
    HasLaw emptyWholeOrder
      (uniformOn (orders ([] : List Empty) ∅ : Set (List Empty))) emptyLaw where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := map_restrictedOrder_uniformOn ([] : List Empty) (by simp) empty_complete ∅

/-- Apply the new generic law at S=A=B=∅ and retain the actual pair observation. -/
theorem empty_pair_hasLaw :
    HasLaw emptyPair
      ((uniformOn (orders ([] : List Empty) ∅ : Set (List Empty))).prod
        (uniformOn (orders ([] : List Empty) ∅ : Set (List Empty)))) emptyLaw := by
  have h : HasLaw
      (fun π : Equiv.Perm Empty =>
        ((emptyWholeOrder π).filter (fun a => decide (a ∈ (∅ : Finset Empty))),
          (emptyWholeOrder π).filter (fun a => decide (a ∈ (∅ : Finset Empty)))))
      ((uniformOn (orders ([] : List Empty) ∅ : Set (List Empty))).prod
        (uniformOn (orders ([] : List Empty) ∅ : Set (List Empty)))) emptyLaw :=
    hasLaw_filter_pair ([] : List Empty) (by simp) empty_complete ∅ empty_whole_hasLaw
      ∅ ∅ (by simp) (by simp) (by simp)
  apply h.congr
  exact Filter.Eventually.of_forall fun π => by
    simp [emptyPair, emptyWholeOrder, restrictedOrder]

def positions3 : List (Fin 3) := [0, 1, 2]

private theorem positions3_nodup : positions3.Nodup := by decide

private theorem positions3_complete (a : Fin 3) : a ∈ positions3 := by
  fin_cases a <;> decide

noncomputable def law3 : Measure (Equiv.Perm (Fin 3)) := uniformOn Set.univ

def overlapLeft : Finset (Fin 3) := {0, 1}
def overlapRight : Finset (Fin 3) := {1, 2}

theorem overlap_not_disjoint : ¬ Disjoint overlapLeft overlapRight := by decide

def overlapPair (π : Equiv.Perm (Fin 3)) : List (Fin 3) × List (Fin 3) :=
  (restrictedOrder positions3 overlapLeft π, restrictedOrder positions3 overlapRight π)

def fullOrder3 (π : Equiv.Perm (Fin 3)) : List (Fin 3) :=
  restrictedOrder positions3 Finset.univ π

private theorem overlap_table :
    ∀ xs ∈ orders positions3 (Finset.univ : Finset (Fin 3)),
      ((xs.filter (fun a => decide (a ∈ overlapLeft)),
          xs.filter (fun a => decide (a ∈ overlapRight))) = ([1, 0], [1, 2]) ↔
        xs.head? = some 1) := by decide

/-- The actual overlapping pair asks exactly whether 1 is globally first. -/
theorem overlap_event_eq_first :
    {π | overlapPair π = ([1, 0], [1, 2])} = firstEvent fullOrder3 1 := by
  ext π
  change (restrictedOrder positions3 overlapLeft π,
      restrictedOrder positions3 overlapRight π) = ([1, 0], [1, 2]) ↔
    (fullOrder3 π).head? = some 1
  rw [← filter_restrictedOrder_of_subset positions3 Finset.univ overlapLeft π
      (Finset.subset_univ _),
    ← filter_restrictedOrder_of_subset positions3 Finset.univ overlapRight π
      (Finset.subset_univ _)]
  exact overlap_table (fullOrder3 π)
    (restrictedOrder_mem_orders positions3 positions3_nodup positions3_complete Finset.univ π)

theorem overlap_joint_mass : law3 {π | overlapPair π = ([1, 0], [1, 2])} = 1 / 3 := by
  rw [overlap_event_eq_first]
  simpa [law3, fullOrder3, one_div] using
    uniformOn_firstEvent positions3 positions3_nodup positions3_complete
      (Finset.univ : Finset (Fin 3)) 1 (Finset.mem_univ 1)

theorem overlap_left_mass :
    law3 {π | restrictedOrder positions3 overlapLeft π = [1, 0]} = 1 / 2 := by
  have hmem : ([1, 0] : List (Fin 3)) ∈ orders positions3 overlapLeft := by decide
  calc
    _ = if ([1, 0] : List (Fin 3)) ∈ orders positions3 overlapLeft
        then (Nat.factorial overlapLeft.card : ℝ≥0∞)⁻¹ else 0 :=
      uniformOn_restrictedOrder_eq positions3 positions3_nodup positions3_complete
        overlapLeft [1, 0]
    _ = 1 / 2 := by rw [if_pos hmem] <;> norm_num [overlapLeft, one_div]

theorem overlap_right_mass :
    law3 {π | restrictedOrder positions3 overlapRight π = [1, 2]} = 1 / 2 := by
  have hmem : ([1, 2] : List (Fin 3)) ∈ orders positions3 overlapRight := by decide
  calc
    _ = if ([1, 2] : List (Fin 3)) ∈ orders positions3 overlapRight
        then (Nat.factorial overlapRight.card : ℝ≥0∞)⁻¹ else 0 :=
      uniformOn_restrictedOrder_eq positions3 positions3_nodup positions3_complete
        overlapRight [1, 2]
    _ = 1 / 2 := by rw [if_pos hmem] <;> norm_num [overlapRight, one_div]

theorem overlap_marginal_product :
    law3 {π | restrictedOrder positions3 overlapLeft π = [1, 0]} *
      law3 {π | restrictedOrder positions3 overlapRight π = [1, 2]} = 1 / 4 := by
  rw [overlap_left_mass, overlap_right_mass]
  norm_num [← ENNReal.coe_div, ← ENNReal.coe_mul]

/-- The actual overlapping joint law is not determined by multiplying its marginals. -/
theorem overlap_joint_ne_product :
    law3 {π | overlapPair π = ([1, 0], [1, 2])} ≠
      law3 {π | restrictedOrder positions3 overlapLeft π = [1, 0]} *
        law3 {π | restrictedOrder positions3 overlapRight π = [1, 2]} := by
  rw [overlap_joint_mass, overlap_marginal_product]
  norm_num [← ENNReal.coe_div]

end Examples.PermutationJointBoundary
