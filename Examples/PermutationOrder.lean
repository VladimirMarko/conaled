import Applications.Probability.PermutationOrder
import Examples.PermutationOrderBoundary
import Mathlib.Tactic

/-!
# Whole output orders and composed restrictions

One uniformly sampled key-to-label permutation on four indices supplies all
observations below. Restricting its inverse list to `{0, 2, 3}` gives six
complete three-element orders, each with mass `1/6`. Two different orders
with the same first member exercise information beyond a minimum event.

One mass is obtained from the public fiber formula, and another through the
public equality of the mapped measure. Filtering this actual output again
to `{0, 3}` uses the deterministic composition law and the same sample.
It does not condition the law or replace the shared environment by a new draw.

These are list observations and probability laws. No sorting/treap execution,
sampling implementation, resource tariff or conditional-history law is supplied.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationOrder

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationOrder
open scoped ENNReal

local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤
local instance : MeasurableSpace (List (Fin 4)) := ⊤

def positions : List (Fin 4) := [0, 1, 2, 3]
def selected : Finset (Fin 4) := {0, 2, 3}
def smaller : Finset (Fin 4) := {0, 3}

theorem positions_nodup : positions.Nodup := by decide

theorem positions_complete (a : Fin 4) : a ∈ positions := by
  fin_cases a <;> decide

noncomputable def law : Measure (Equiv.Perm (Fin 4)) := uniformOn Set.univ

/-- Value, support and order contracts concern the actual returned list. -/
theorem selected_structure (π : Equiv.Perm (Fin 4)) :
    (restrictedOrder positions selected π).Nodup ∧
      (restrictedOrder positions selected π).toFinset = selected ∧
      (restrictedOrder positions selected π).length = 3 ∧
      (restrictedOrder positions selected π).map π <+ positions := by
  refine ⟨restrictedOrder_nodup positions positions_nodup selected π,
    restrictedOrder_toFinset positions positions_complete selected π, ?_,
    map_restrictedOrder_sublist positions selected π⟩
  calc
    _ = selected.card :=
      restrictedOrder_length positions positions_nodup positions_complete selected π
    _ = 3 := by decide

theorem selected_permutation (π : Equiv.Perm (Fin 4)) :
    (restrictedOrder positions selected π).Perm [0, 2, 3] := by
  have hbase : positions.filter (fun a => decide (a ∈ selected)) = [0, 2, 3] := by
    decide
  simpa only [hbase] using
    restrictedOrder_perm positions positions_nodup positions_complete selected π

theorem selected_orders_card : (orders positions selected).card = 6 := by
  calc
    _ = Nat.factorial selected.card :=
      orders_card positions positions_nodup positions_complete selected
    _ = 6 := by decide

private theorem fiber_mass_of_mem (S : Finset (Fin 4)) (xs : List (Fin 4))
    (hxs : xs ∈ orders positions S) :
    law {π | restrictedOrder positions S π = xs} =
      (Nat.factorial S.card : ℝ≥0∞)⁻¹ := by
  unfold law
  rw [uniformOn_restrictedOrder_eq positions positions_nodup positions_complete S xs,
    if_pos hxs]

/-- This first complete-list mass uses the public output-fiber formula. -/
theorem order_023_mass :
    law {π | restrictedOrder positions selected π = [0, 2, 3]} = 1 / 6 := by
  calc
    _ = (Nat.factorial selected.card : ℝ≥0∞)⁻¹ :=
      fiber_mass_of_mem selected [0, 2, 3] (by decide)
    _ = 1 / 6 := by norm_num [selected, one_div]

/-- The actual list observation has the existing finite uniform measure. -/
theorem observed_law :
    law.map (restrictedOrder positions selected) =
      uniformOn (orders positions selected : Set (List (Fin 4))) := by
  unfold law
  exact map_restrictedOrder_uniformOn positions positions_nodup positions_complete selected

/-- A different order with the same first key, derived through mapped meaning. -/
theorem order_032_mass_via_map :
    law {π | restrictedOrder positions selected π = [0, 3, 2]} = 1 / 6 := by
  have hmem : ([0, 3, 2] : List (Fin 4)) ∈ orders positions selected := by decide
  calc
    _ = law.map (restrictedOrder positions selected) {([0, 3, 2] : List (Fin 4))} := by
      rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
    _ = uniformOn (orders positions selected : Set (List (Fin 4)))
        {([0, 3, 2] : List (Fin 4))} := by rw [observed_law]
    _ = 1 / (orders positions selected).card := by
      simpa [Finset.inter_singleton_of_mem hmem] using
        (uniformOn_apply_finset (s := orders positions selected)
          (t := {([0, 3, 2] : List (Fin 4))}))
    _ = 1 / 6 := by rw [selected_orders_card]

/-- A repeated output is outside the support, even though its length is three. -/
theorem repeated_order_mass_zero :
    law {π | restrictedOrder positions selected π = [0, 0, 2]} = 0 := by
  have hbad : ([0, 0, 2] : List (Fin 4)) ∉ orders positions selected := by decide
  unfold law
  rw [uniformOn_restrictedOrder_eq positions positions_nodup positions_complete
    selected [0, 0, 2], if_neg hbad]

/-- The second observation filters the first result under the same permutation. -/
def nestedObservation (π : Equiv.Perm (Fin 4)) : List (Fin 4) :=
  (restrictedOrder positions selected π).filter (fun a => decide (a ∈ smaller))

theorem nestedObservation_eq (π : Equiv.Perm (Fin 4)) :
    nestedObservation π = restrictedOrder positions smaller π := by
  exact filter_restrictedOrder_of_subset positions selected smaller π (by decide)

/-- Composing restrictions preserves the ordered-pair law through its value bridge. -/
theorem nested_order_30_mass :
    law {π | nestedObservation π = [3, 0]} = 1 / 2 := by
  simp_rw [nestedObservation_eq]
  calc
    _ = (Nat.factorial smaller.card : ℝ≥0∞)⁻¹ :=
      fiber_mass_of_mem smaller [3, 0] (by decide)
    _ = 1 / 2 := by norm_num [smaller, one_div]

theorem singleton_order_mass :
    law {π | restrictedOrder positions {2} π = [2]} = 1 := by
  simpa using fiber_mass_of_mem {2} [2] (by decide)

theorem full_order_mass :
    law {π | restrictedOrder positions Finset.univ π = [3, 1, 0, 2]} = 1 / 24 := by
  calc
    _ = (Nat.factorial (Finset.univ : Finset (Fin 4)).card : ℝ≥0∞)⁻¹ :=
      fiber_mass_of_mem Finset.univ [3, 1, 0, 2] (by decide)
    _ = 1 / 24 := by norm_num [one_div]

end Examples.PermutationOrder
