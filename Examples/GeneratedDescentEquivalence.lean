import Examples.GeneratedComparisonRestriction
import SquareKit.SmoothQuotientGeneratedDescentEquivalence

/-! Generated equivalence closure at a dependent caller, and its fixed-cover
specialization. These examples do not assert parameter-compatible gluing. -/
noncomputable section
namespace Examples.GeneratedDescentEquivalence
open CategoryTheory SquareKit SquareKit.Internal.PathTransport
open GroupoidModel Comparison Typed SignatureInterpretationMaps.DependentTail
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (S : Comparison.Signature.{0}) [S.base.map.IsEquivalence]
    (hF : ∀ c, Function.Bijective (S.fiberMap.app c))

example := generatedContextEquivalence S hF withFiber
example := generatedFamilyMap_equivalences S hF withFiber command.motive.typing
example := GeneratedEquivalence.generatedTel S hF tail
example := GeneratedEquivalence.generatedTel S hF (.pathReindex context (.base context)
  point.deriv tail weakening)

/-- The unchanged dependent J term is compared by its entire interpreted section. -/
example := GeneratedComparisonRestriction.j_restriction S

/-- The generated forward functor reflects every selected arrow. -/
theorem selected_arrow_injective :
    ∀ x y, Function.Injective ((generatedContextEquivalence S hF withFiber).functor.map
      (X := x) (Y := y)) := by
  intro x y
  exact (generatedContextEquivalence S hF withFiber).functor.map_injective

/-- Collapsing the fixture's two primitive values does not meet the hypotheses. -/
theorem collapse_rejected : ¬ ∀ c, Function.Bijective (GroupoidComparison.signature.fiberMap.app c) := by
  intro h
  have e := (h (Discrete.mk false, FamilyMapElimination.p)).1 (a₁ := false) (a₂ := true) rfl
  cases e

/-- A concrete C4 signature satisfies the conditional theorem; no action on
fibers is used to identify its distinct loop labels. -/
def c4Signature : Comparison.Signature.{0} := Signature.diagonal
  (@Grpd.of FamilyMapElimination.G Groupoid.ofIsGroupoid)
  ((CategoryTheory.Functor.const _).obj PUnit)

instance : c4Signature.base.map.IsEquivalence :=
  inferInstanceAs (Functor.IsEquivalence (𝟭 _))

theorem c4FiberBijective : ∀ c, Function.Bijective (c4Signature.fiberMap.app c) :=
  fun _ => Function.bijective_id

example := selected_arrow_injective c4Signature c4FiberBijective
example := generatedContextEquivalence c4Signature c4FiberBijective
  (.telescope paths tail)

section Smooth
open SheafActionQuotient SmoothOpenSite SmoothQuotientDeformations
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

example := SmoothQuotientGeneratedDescent.contextEquivalence a A withFiber
example := SmoothQuotientGeneratedDescent.familyEquivalences a A withFiber command.motive.typing

/-- The local proof interpretation uses the same source-derived J section. -/
example := generatedTerm_commutes (SmoothQuotientGeneratedDescent.signature a A)
  withFiber command.motive.typing generic

end Smooth
end Examples.GeneratedDescentEquivalence
