import Applications.Probability.PermutationOrder
import Examples.PermutationMinimum
import Mathlib.Tactic

/-!
# Empty and enumeration boundaries for restricted permutation orders

The empty-subset and empty-index probabilities instantiate the public whole-output
law. The remaining cases inspect the actual inverse-map/filter observation:
its orientation, its relation to numeric priorities, and the distinct roles of
completeness and absence of repeated labels in its support theorem.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationOrderBoundary

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationOrder
open Examples.PermutationMinimum (spacedPriority)
open scoped ENNReal

local instance : MeasurableSpace (Equiv.Perm Empty) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm Empty) :=
  ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 3)) :=
  ⟨fun _ => trivial⟩

/-- An empty subset always produces the empty list. -/
theorem empty_subset_output (π : Equiv.Perm (Fin 3)) :
    restrictedOrder [0, 1, 2] ∅ π = [] := by
  simp [restrictedOrder]

/-- Its target is a singleton, rather than an empty probability support. -/
theorem empty_subset_orders :
    orders ([0, 1, 2] : List (Fin 3)) ∅ = {[]} := by
  simp [orders]

/-- The new generic fiber law supplies the empty subset's mass one. -/
theorem empty_subset_mass :
    uniformOn Set.univ
      {π : Equiv.Perm (Fin 3) | restrictedOrder [0, 1, 2] ∅ π = []} = 1 := by
  simpa [orders] using
    (uniformOn_restrictedOrder_eq ([0, 1, 2] : List (Fin 3))
      (by decide) (by intro a; fin_cases a <;> simp)
      (∅ : Finset (Fin 3)) [])

/-- The same generic law applies to an empty index universe with its one permutation. -/
theorem empty_index_mass :
    uniformOn (Set.univ : Set (Equiv.Perm Empty))
      {π | restrictedOrder ([] : List Empty) ∅ π = []} = 1 := by
  simpa [orders] using
    (uniformOn_restrictedOrder_eq ([] : List Empty)
      (by simp) (by intro a; cases a) (∅ : Finset Empty) [])

/-- Key-to-label cycle: 0 maps to 1, 1 to 2, and 2 to 0. -/
def cycle : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

theorem cycle_values : cycle 0 = 1 ∧ cycle 1 = 2 ∧ cycle 2 = 0 := by
  decide

/-- Reading labels in order requires the inverse permutation. -/
theorem cycle_inverse_order :
    ([0, 1, 2] : List (Fin 3)).map cycle.symm = [2, 0, 1] := by
  decide

theorem cycle_restricted_order :
    restrictedOrder ([0, 1, 2] : List (Fin 3)) {0, 1} cycle = [0, 1] := by
  decide

/-- The mistaken direct-map expression has the opposite order on this subset. -/
theorem cycle_direct_order :
    (([0, 1, 2] : List (Fin 3)).map cycle).filter
      (fun a => decide (a ∈ ({0, 1} : Finset (Fin 3)))) = [1, 0] := by
  decide

theorem inverse_and_direct_orders_differ :
    restrictedOrder ([0, 1, 2] : List (Fin 3)) {0, 1} cycle ≠
      (([0, 1, 2] : List (Fin 3)).map cycle).filter
        (fun a => decide (a ∈ ({0, 1} : Finset (Fin 3)))) := by
  rw [cycle_restricted_order, cycle_direct_order]
  decide

/-- The enumeration 0, 2, 1 matches the existing priorities -7, 4, 100. -/
theorem numeric_enumeration_values :
    (restrictedOrder ([0, 2, 1] : List (Fin 3)) Finset.univ
      (Equiv.refl (Fin 3))).map spacedPriority = [-7, 4, 100] := by
  decide

theorem numeric_enumeration_increasing :
    List.Pairwise (fun a b : Int => a < b)
      ((restrictedOrder ([0, 2, 1] : List (Fin 3)) Finset.univ
        (Equiv.refl (Fin 3))).map spacedPriority) := by
  rw [numeric_enumeration_values]
  decide

/-- Ordinary label order need not agree with increasing numeric priority. -/
theorem ordinary_enumeration_not_increasing :
    ¬ List.Pairwise (fun a b : Int => a < b)
      ((restrictedOrder ([0, 1, 2] : List (Fin 3)) Finset.univ
        (Equiv.refl (Fin 3))).map spacedPriority) := by
  decide

theorem numeric_and_ordinary_orders_differ :
    restrictedOrder ([0, 2, 1] : List (Fin 3)) Finset.univ (Equiv.refl (Fin 3)) ≠
      restrictedOrder ([0, 1, 2] : List (Fin 3)) Finset.univ (Equiv.refl (Fin 3)) := by
  decide

/-- An incomplete label enumeration can miss the selected key after relabeling. -/
theorem incomplete_output :
    restrictedOrder ([0] : List (Fin 2)) {0} (Equiv.swap 0 1) = [] := by
  decide

/-- Nodup alone does not ensure that the projection belongs to the claimed support. -/
theorem incomplete_support_counterexample :
    ([0] : List (Fin 2)).Nodup ∧
      restrictedOrder ([0] : List (Fin 2)) {0} (Equiv.swap 0 1) ∉
        orders ([0] : List (Fin 2)) {0} := by
  constructor
  · decide
  · rw [incomplete_output]
    intro h
    have hlength := ((mem_orders _ _ _).mp h).length_eq
    norm_num at hlength

/-- Repeated labels change key multiplicities under the inverse permutation. -/
theorem repeated_output :
    restrictedOrder ([0, 0, 1] : List (Fin 2)) Finset.univ (Equiv.swap 0 1) =
      [1, 1, 0] := by
  decide

/-- Completeness alone does not ensure that the output is a permutation of the base list. -/
theorem repeated_support_counterexample :
    (∀ a : Fin 2, a ∈ ([0, 0, 1] : List (Fin 2))) ∧
      restrictedOrder ([0, 0, 1] : List (Fin 2)) Finset.univ (Equiv.swap 0 1) ∉
        orders ([0, 0, 1] : List (Fin 2)) Finset.univ := by
  constructor
  · intro a
    fin_cases a <;> simp
  · rw [repeated_output]
    intro h
    have hcount := ((mem_orders _ _ _).mp h).count_eq (0 : Fin 2)
    norm_num at hcount

end Examples.PermutationOrderBoundary
