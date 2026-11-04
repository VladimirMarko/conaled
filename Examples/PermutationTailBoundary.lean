import Applications.Probability.PermutationTail
import Examples.PermutationOrder
import Mathlib.Tactic

/-!
# Boundary observations for conditional permutation tails

These cases keep the selected first key distinct from the first global key,
use the new tail law at a singleton, and preserve zero conditioning for empty
or outsider events. The Fin3 counterexample observes the actual original
projection onto a set outside the selected remainder under the same conditioned
sample. Its two masses come from full-order fibers and ordinary conditioning.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationTailBoundary

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationOrder
open Applications.Probability.PermutationTail
open Examples.PermutationOrder (positions selected positions_nodup positions_complete)
open scoped ENNReal ProbabilityTheory

local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 4)) :=
  ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 3)) :=
  ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm Empty) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm Empty) :=
  ⟨fun _ => trivial⟩

/-- The same sample exposes selected key 0 while global key 1 is first. -/
def swap01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1

theorem swap01_global_order :
    positions.map swap01.symm = [1, 0, 2, 3] := by
  decide

theorem swap01_selected_order :
    restrictedOrder positions selected swap01 = [0, 2, 3] := by
  decide

theorem swap01_first_events :
    swap01 ∈ firstEvent (restrictedOrder positions selected) 0 ∧
      swap01 ∈ firstEvent (fun π : Equiv.Perm (Fin 4) => positions.map π.symm) 1 ∧
      swap01 ∉ firstEvent (fun π : Equiv.Perm (Fin 4) => positions.map π.symm) 0 := by
  change (restrictedOrder positions selected swap01).head? = some 0 ∧
    (positions.map swap01.symm).head? = some 1 ∧
    (positions.map swap01.symm).head? ≠ some 0
  rw [swap01_selected_order, swap01_global_order]
  decide

/-- The new source-fiber theorem covers a singleton with empty actual tail. -/
theorem singleton_conditional_tail_mass :
    (uniformOn (Set.univ : Set (Equiv.Perm (Fin 4))))[|
      firstEvent (restrictedOrder positions {2}) 2]
      {π | (restrictedOrder positions {2} π).tail = []} = 1 := by
  simpa [orders] using
    (cond_tail_eq positions positions_nodup positions_complete {2} 2
      (Finset.mem_singleton_self 2) [])

/-- The empty observation has no first key. -/
theorem empty_subset_none_mass :
    uniformOn (Set.univ : Set (Equiv.Perm (Fin 4)))
      {π | (restrictedOrder positions ∅ π).head? = none} = 1 := by
  simp [restrictedOrder]

theorem empty_subset_first_event :
    firstEvent (restrictedOrder positions ∅) (0 : Fin 4) = ∅ :=
  firstEvent_restrictedOrder_of_not_mem positions ∅ 0 (by simp)

/-- A null first-key event gives the zero conditional measure. -/
theorem empty_subset_conditional_zero :
    (uniformOn (Set.univ : Set (Equiv.Perm (Fin 4))))[|
      firstEvent (restrictedOrder positions ∅) 0] = 0 :=
  cond_firstEvent_restrictedOrder_of_not_mem positions ∅ 0 (by simp)
    (uniformOn Set.univ)

theorem outsider_first_event :
    firstEvent (restrictedOrder positions selected) (1 : Fin 4) = ∅ :=
  firstEvent_restrictedOrder_of_not_mem positions selected 1 (by decide)

theorem outsider_conditional_zero :
    (uniformOn (Set.univ : Set (Equiv.Perm (Fin 4))))[|
      firstEvent (restrictedOrder positions selected) 1] = 0 :=
  cond_firstEvent_restrictedOrder_of_not_mem positions selected 1 (by decide)
    (uniformOn Set.univ)

/-- Empty indices still have their identity permutation; no key is manufactured. -/
theorem empty_indices_none_mass :
    uniformOn (Set.univ : Set (Equiv.Perm Empty))
      {π | (restrictedOrder ([] : List Empty) ∅ π).head? = none} = 1 := by
  simp [restrictedOrder]

/-! ## A set outside the selected remainder can have a biased conditional order -/

def counterPositions : List (Fin 3) := [0, 1, 2]
def conditionSubset : Finset (Fin 3) := {0, 1}
def outsideSubset : Finset (Fin 3) := {1, 2}

private theorem counterPositions_nodup : counterPositions.Nodup := by decide

private theorem counterPositions_complete (a : Fin 3) : a ∈ counterPositions := by
  fin_cases a <;> decide

noncomputable def counterLaw : Measure (Equiv.Perm (Fin 3)) := uniformOn Set.univ

def counterFirst : Set (Equiv.Perm (Fin 3)) :=
  firstEvent (restrictedOrder counterPositions conditionSubset) 0

noncomputable def outsideConditional : Measure (Equiv.Perm (Fin 3)) :=
  counterLaw[|counterFirst]

theorem outside_subset_boundaries :
    (0 : Fin 3) ∉ outsideSubset ∧
      ¬ (outsideSubset ⊆ conditionSubset.erase 0) := by
  decide

/-- The conditioning mass uses the new first-event theorem. -/
theorem counter_first_mass : counterLaw counterFirst = 1 / 2 := by
  simpa [counterLaw, counterFirst, conditionSubset, one_div] using
    (uniformOn_firstEvent counterPositions counterPositions_nodup
      counterPositions_complete conditionSubset 0 (by decide))

private theorem counter_full_mass (xs : List (Fin 3))
    (hxs : xs ∈ orders counterPositions Finset.univ) :
    counterLaw {π | restrictedOrder counterPositions Finset.univ π = xs} = 1 / 6 := by
  unfold counterLaw
  rw [uniformOn_restrictedOrder_eq counterPositions counterPositions_nodup
    counterPositions_complete Finset.univ xs, ite_eq_left hxs]
  norm_num [one_div]

/-- Finite value calculation over the six supported full lists, not over a new law. -/
private theorem joint12_table :
    ∀ xs ∈ orders counterPositions (Finset.univ : Finset (Fin 3)),
      (((xs.filter (fun a => decide (a ∈ conditionSubset))).head? = some 0 ∧
        xs.filter (fun a => decide (a ∈ outsideSubset)) = [1, 2]) ↔
        xs = [0, 1, 2]) := by
  simp only [orders, Finset.mem_univ, decide_true, List.filter_true]
  rw [List.toFinset_eq_of_perm _ _
    (List.permutations_perm_permutations' counterPositions)]
  decide

private theorem joint21_table :
    ∀ xs ∈ orders counterPositions (Finset.univ : Finset (Fin 3)),
      (((xs.filter (fun a => decide (a ∈ conditionSubset))).head? = some 0 ∧
        xs.filter (fun a => decide (a ∈ outsideSubset)) = [2, 1]) ↔
        xs = [0, 2, 1] ∨ xs = [2, 0, 1]) := by
  simp only [orders, Finset.mem_univ, decide_true, List.filter_true]
  rw [List.toFinset_eq_of_perm _ _
    (List.permutations_perm_permutations' counterPositions)]
  decide

private theorem counter_joint12 :
    counterFirst ∩ {π | restrictedOrder counterPositions outsideSubset π = [1, 2]} =
      {π | restrictedOrder counterPositions Finset.univ π = [0, 1, 2]} := by
  ext π
  change ((restrictedOrder counterPositions conditionSubset π).head? = some 0 ∧
    restrictedOrder counterPositions outsideSubset π = [1, 2]) ↔
    restrictedOrder counterPositions Finset.univ π = [0, 1, 2]
  rw [← filter_restrictedOrder_of_subset counterPositions Finset.univ conditionSubset π
    (Finset.subset_univ _),
    ← filter_restrictedOrder_of_subset counterPositions Finset.univ outsideSubset π
      (Finset.subset_univ _)]
  exact joint12_table _
    (restrictedOrder_mem_orders counterPositions counterPositions_nodup
      counterPositions_complete Finset.univ π)

private theorem counter_joint21 :
    counterFirst ∩ {π | restrictedOrder counterPositions outsideSubset π = [2, 1]} =
      {π | restrictedOrder counterPositions Finset.univ π = [0, 2, 1]} ∪
        {π | restrictedOrder counterPositions Finset.univ π = [2, 0, 1]} := by
  ext π
  change ((restrictedOrder counterPositions conditionSubset π).head? = some 0 ∧
    restrictedOrder counterPositions outsideSubset π = [2, 1]) ↔
    (restrictedOrder counterPositions Finset.univ π = [0, 2, 1] ∨
      restrictedOrder counterPositions Finset.univ π = [2, 0, 1])
  rw [← filter_restrictedOrder_of_subset counterPositions Finset.univ conditionSubset π
    (Finset.subset_univ _),
    ← filter_restrictedOrder_of_subset counterPositions Finset.univ outsideSubset π
      (Finset.subset_univ _)]
  exact joint21_table _
    (restrictedOrder_mem_orders counterPositions counterPositions_nodup
      counterPositions_complete Finset.univ π)

private theorem full_fibers_disjoint :
    Disjoint
      {π | restrictedOrder counterPositions Finset.univ π = [0, 2, 1]}
      {π | restrictedOrder counterPositions Finset.univ π = [2, 0, 1]} := by
  rw [Set.disjoint_left]
  intro π h021 h201
  have hbad : ([0, 2, 1] : List (Fin 3)) = [2, 0, 1] := h021.symm.trans h201
  exact (by decide : ([0, 2, 1] : List (Fin 3)) ≠ [2, 0, 1]) hbad

private theorem counter_joint12_mass :
    counterLaw
      (counterFirst ∩ {π | restrictedOrder counterPositions outsideSubset π = [1, 2]}) =
      1 / 6 := by
  rw [counter_joint12]
  exact counter_full_mass [0, 1, 2] (by
    simp only [orders, Finset.mem_univ, decide_true, List.filter_true]
    rw [List.toFinset_eq_of_perm _ _
      (List.permutations_perm_permutations' counterPositions)]
    decide)

private theorem counter_joint21_mass :
    counterLaw
      (counterFirst ∩ {π | restrictedOrder counterPositions outsideSubset π = [2, 1]}) =
      1 / 3 := by
  rw [counter_joint21, measure_union full_fibers_disjoint (by trivial)]
  rw [counter_full_mass [0, 2, 1] (by
      simp only [orders, Finset.mem_univ, decide_true, List.filter_true]
      rw [List.toFinset_eq_of_perm _ _
        (List.permutations_perm_permutations' counterPositions)]
      decide),
    counter_full_mass [2, 0, 1] (by
      simp only [orders, Finset.mem_univ, decide_true, List.filter_true]
      rw [List.toFinset_eq_of_perm _ _
        (List.permutations_perm_permutations' counterPositions)]
      decide)]
  have h : (1 / 6 : NNReal) + 1 / 6 = 1 / 3 := by norm_num
  have h6 : (6 : NNReal) ≠ 0 := by norm_num
  have h3 : (3 : NNReal) ≠ 0 := by norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_div (p := 1) h6,
    ENNReal.coe_div (p := 1) h3, ENNReal.coe_one, ENNReal.coe_ofNat] using
    congrArg (fun x : NNReal => (x : ENNReal)) h

/-- The actual outside projection has conditional mass one-third for [1,2]. -/
theorem outside_order_12_mass :
    outsideConditional {π | restrictedOrder counterPositions outsideSubset π = [1, 2]} =
      1 / 3 := by
  have hhalf : (1 / 2 : ℝ≥0∞)⁻¹ = 2 := by simp [one_div]
  rw [outsideConditional, cond_apply (s := counterFirst) (by trivial) counterLaw,
    counter_first_mass, counter_joint12_mass, hhalf]
  have h : (2 : NNReal) * (1 / 6) = 1 / 3 := by norm_num
  have h6 : (6 : NNReal) ≠ 0 := by norm_num
  have h3 : (3 : NNReal) ≠ 0 := by norm_num
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (p := 1) h6,
    ENNReal.coe_div (p := 1) h3, ENNReal.coe_one, ENNReal.coe_ofNat] using
    congrArg (fun x : NNReal => (x : ENNReal)) h

/-- Its reversed order has conditional mass two-thirds under the same measure. -/
theorem outside_order_21_mass :
    outsideConditional {π | restrictedOrder counterPositions outsideSubset π = [2, 1]} =
      2 / 3 := by
  have hhalf : (1 / 2 : ℝ≥0∞)⁻¹ = 2 := by simp [one_div]
  rw [outsideConditional, cond_apply (s := counterFirst) (by trivial) counterLaw,
    counter_first_mass, counter_joint21_mass, hhalf]
  have h : (2 : NNReal) * (1 / 3) = 2 / 3 := by norm_num
  have h3 : (3 : NNReal) ≠ 0 := by norm_num
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (p := 1) h3,
    ENNReal.coe_div (p := 2) h3, ENNReal.coe_one, ENNReal.coe_ofNat] using
    congrArg (fun x : NNReal => (x : ENNReal)) h

/-- Excluding the exposed key alone cannot replace containment in its selected remainder. -/
theorem outside_order_not_uniform :
    outsideConditional {π | restrictedOrder counterPositions outsideSubset π = [1, 2]} ≠
      1 / 2 := by
  rw [outside_order_12_mass]
  norm_num [← ENNReal.coe_div]

end Examples.PermutationTailBoundary
