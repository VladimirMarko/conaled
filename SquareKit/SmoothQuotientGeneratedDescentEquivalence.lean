import SquareKit.SmoothQuotientDescentExtension
import SquareKit.SmoothQuotientSource
import SquareKit.Internal.PathTransport.GeneratedEquivalenceMaps

/-! Fixed-cover equivalences for generated interpretations over actual quotient
cocycles and compatible deformation fibers. Parameter gluing is separate. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedDescent
open CategoryTheory SheafActionQuotient SmoothOpenSite SmoothQuotientDeformations
open Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
local instance : Groupoid (Descent.Datum (a := a) A) := Groupoid.ofIsGroupoid

def signature := GroupoidModel.Comparison.alignedUniverseSignature
  (Descent.descentFunctor a A) (CocycleDatum.fiberFamily (a := a) (A := A))
  (family a X) (CocycleDatum.fiberComparison (a := a) (A := A)).inv

abbrev localModel := GroupoidModel.Instance.universeModel
  (Descent.Datum (a := a) A) (CocycleDatum.fiberFamily (a := a) (A := A))

instance signature_base_equivalence : (signature a A).base.map.IsEquivalence := by
  change (AsSmall.down ⋙ Descent.descentFunctor a A ⋙ AsSmall.up).IsEquivalence
  exact ((AsSmall.equiv (C := Descent.Datum (a := a) A)).symm.trans
    ((Descent.quotientDescentEquivalence a A).trans (AsSmall.equiv (C := Object a X)))).isEquivalence_functor

theorem signature_fiber_bijective : ∀ c, Function.Bijective ((signature a A).fiberMap.app c) := by
  intro c
  let e := (Equiv.ulift : ULift _ ≃ _).trans
    ((CocycleDatum.fiberEquivalence (ULift.down c)).symm.trans Equiv.ulift.symm)
  exact e.bijective

/-- The forward functor is precisely the previously extracted generated map. -/
def contextEquivalence (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (show Grpd.{1,1} from γ (localModel a A)) ≌
      (show Grpd.{1,1} from γ (SmoothQuotientSource.model a X)) :=
  GroupoidModel.Comparison.generatedContextEquivalence (signature a A)
    (signature_fiber_bijective a A) hΓ

theorem familyEquivalences (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (hB : Typed.TyDeriv.{2} Γ γ B b) :
    ∀ c, ((GroupoidModel.Comparison.generatedFamilyMap (signature a A) hΓ hB).app c).IsEquivalence :=
  GroupoidModel.Comparison.generatedFamilyMap_equivalences (signature a A)
    (signature_fiber_bijective a A) hΓ hB

@[simp] theorem contextEquivalence_functor (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (contextEquivalence a A hΓ).functor =
      GroupoidModel.Comparison.generatedContextMap (signature a A) hΓ := rfl

end SquareKit.SmoothQuotientGeneratedDescent
