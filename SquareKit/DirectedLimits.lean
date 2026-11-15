import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Bounds.Image

/-!
# Directed limits using standard order structures

The function-space construction uses the existing pointwise order, bottom and
`Pi.supSet`. Its scoped instance supplies full directed completeness, including
empty families. Scott-continuous maps preserve nonempty directed limits.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.DirectedLimits

universe u v w

/-- Full pointwise directed completeness with the existing Pi supremum data. -/
@[instance_reducible] def piCompletePartialOrder {ι : Type u} {X : ι → Type v}
    [∀ i, CompletePartialOrder (X i)] : CompletePartialOrder (∀ i, X i) where
  __ := (inferInstance : PartialOrder (∀ i, X i))
  __ := (inferInstance : OrderBot (∀ i, X i))
  __ := (Pi.supSet : SupSet (∀ i, X i))
  lubOfDirected S directed := by
    apply isLUB_pi.mpr
    intro i
    rw [sSup_apply_eq_sSup_image]
    exact (directed.mono_comp (fun _ _ h => h i)).isLUB_sSup

scoped instance {ι : Type u} {X : ι → Type v} [∀ i, CompletePartialOrder (X i)] :
    CompletePartialOrder (∀ i, X i) := piCompletePartialOrder

/-- Evaluation preserves any existing directed lub, without a countability restriction. -/
theorem scottContinuous_eval {ι : Type u} {X : ι → Type v} [∀ i, Preorder (X i)]
    (i : ι) : ScottContinuous (Function.eval i : (∀ j, X j) → X i) := by
  intro S _ _ f lub
  exact (isLUB_pi.mp lub) i

/-- CPO-level limit transport; no complete lattice or empty-limit preservation is assumed. -/
theorem map_sSup {B : Type u} {C : Type v} [CompletePartialOrder B] [CompletePartialOrder C]
    {h : B → C} (continuous : ScottContinuous h) {S : Set B}
    (nonempty : S.Nonempty) (directed : DirectedOn (· ≤ ·) S) :
    h (sSup S) = sSup (h '' S) :=
  (continuous nonempty directed directed.isLUB_sSup).unique
    (directed.mono_comp continuous.monotone).isLUB_sSup

end SquareKit.DirectedLimits
