import SquareKit.SmoothQuotientComparisonCoherence
import SquareKit.Internal.PathTransport.GeneratedComparisonIdentity

/-! Identity restriction on generated contexts and families of the unchanged
smooth quotient interpretation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.SmoothQuotientComparison
open CategoryTheory SheafActionQuotient SmoothOpenSite SmoothQuotientDeformations
open Internal.PathTransport GroupoidModel
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)

theorem generatedContextMap_id (h : Typed.CtxDeriv.{2} Γ γ) :
    Comparison.generatedContextMap (signature (a := a) (𝟙 X)) h =
      𝟭 (show Grpd.{1,1} from γ (SmoothQuotientSource.model a X)) :=
  Comparison.generatedContextMap_identity (Grpd.of (AsSmall (Object a X)))
    (Instance.liftedFamily (Object a X) (family a X)) h

theorem generatedFamilyMap_id (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (hA : Typed.TyDeriv.{2} Γ γ A b) :
    HEq (Comparison.generatedFamilyMap (signature (a := a) (𝟙 X)) hΓ hA)
      (𝟙 (show (show Grpd.{1,1} from γ (SmoothQuotientSource.model a X)) ⥤ Grpd.{1,1}
        from b (SmoothQuotientSource.model a X))) :=
  Comparison.generatedFamilyMap_identity (Grpd.of (AsSmall (Object a X)))
    (Instance.liftedFamily (Object a X) (family a X)) hΓ hA

end SquareKit.SmoothQuotientComparison
