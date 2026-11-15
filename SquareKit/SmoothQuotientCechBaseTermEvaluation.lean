import SquareKit.SmoothQuotientPrimitiveCoefficientValues
import SquareKit.SmoothQuotientCechGeneratedCone

/-! Recovery of the primitive datum selected by a generated base term. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ x ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ)

def sourceBaseTerm (_hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ) :
    (show Grpd.{1,1} from γ (model a A)) ⥤ SheafActionQuotient.Cech.Datum (a := a) A :=
  baseFunctor (ξ (model a A)).down ⋙ AsSmall.down

def evaluatedBaseTerm : (show Grpd.{1,1} from γ (model a A)) ⥤
    SheafActionQuotient.Cech.Datum (a := a) A :=
  matchingEvaluation a A hΓ ⋙ (baseTermDiagram a hΓ hx A).functor ⋙ coefficientDatumFunctor a A

theorem evaluatedBaseTerm_local :
    evaluatedBaseTerm a A hΓ hx ⋙ SheafActionQuotient.Cech.localFunctor =
      sourceBaseTerm a A hx ⋙ SheafActionQuotient.Cech.localFunctor := by
  have hh := congrArg (fun F => F ⋙ AsSmall.down)
    (generatedBaseTerm_commutes (signature a A) hΓ hx)
  exact hh.symm

end SquareKit.SmoothQuotientCechLocal
