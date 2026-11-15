import SquareKit.SmoothQuotientGeneratedBaseMatching
import SquareKit.Internal.PathTransport.GeneratedPrimitiveFiber

/-! A generated base term defines an actual map of the three restriction levels. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ x ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ)

def baseTermDiagram (A : SplitSheaf.Ty X) :
    CechMatching.StrictMap (strictDiagram a hΓ A) (baseDiagram a A) where
  localMap := baseFunctor (ξ (SmoothQuotientSource.model a (SplitSheaf.Ext A))).down
  doubleMap := baseFunctor (ξ (SmoothQuotientSource.model a (SplitSheaf.Cech.double A))).down
  tripleMap := baseFunctor (ξ (SmoothQuotientSource.model a (SplitSheaf.Cech.triple A))).down
  first := generatedBaseTerm_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.first A)) hΓ hx
  second := generatedBaseTerm_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.second A)) hΓ hx
  diagonal := generatedBaseTerm_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.diagonal A)) hΓ hx
  firstSecond := generatedBaseTerm_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.firstSecond A)) hΓ hx
  firstThird := generatedBaseTerm_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.firstThird A)) hΓ hx
  secondThird := generatedBaseTerm_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.secondThird A)) hΓ hx

end SquareKit.SmoothQuotientGeneratedMatching
