import SquareKit.SmoothQuotientGeneratedMatching
import SquareKit.Internal.PathTransport.CechMatchingMap

/-! Generated substitutions act on independent matching data. This includes
comprehension projections, dependent-tail maps and path reindexing. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ Δ δ σ s} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
variable (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s)

/-- All six squares follow from generated substitution preservation at the
actual parameter maps. No matching-data functor is an assumed field. -/
def substitutionDiagram (A : SplitSheaf.Ty X) :
    CechMatching.StrictMap (strictDiagram a hΔ A) (strictDiagram a hΓ A) where
  localMap := (s (SmoothQuotientSource.model a (SplitSheaf.Ext A))).down
  doubleMap := (s (SmoothQuotientSource.model a (SplitSheaf.Cech.double A))).down
  tripleMap := (s (SmoothQuotientSource.model a (SplitSheaf.Cech.triple A))).down
  first := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SplitSheaf.Cech.first A)) hΓ hΔ hs
  second := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SplitSheaf.Cech.second A)) hΓ hΔ hs
  diagonal := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SplitSheaf.Cech.diagonal A)) hΓ hΔ hs
  firstSecond := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SplitSheaf.Cech.firstSecond A)) hΓ hΔ hs
  firstThird := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SplitSheaf.Cech.firstThird A)) hΓ hΔ hs
  secondThird := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SplitSheaf.Cech.secondThird A)) hΓ hΔ hs

/-- Independent local data are mapped through the generated substitution. -/
def substitution (A : SplitSheaf.Ty X) : Datum a hΔ A ⥤ Datum a hΓ A :=
  (substitutionDiagram a hΓ hΔ hs A).functor

/-- The complete local functor, including its arrow action, is retained. -/
theorem substitution_local (A : SplitSheaf.Ty X) :
    substitution a hΓ hΔ hs A ⋙ CechMatching.Datum.localFunctor =
      CechMatching.Datum.localFunctor ⋙
        (s (SmoothQuotientSource.model a (SplitSheaf.Ext A))).down := rfl

/-- The base projection of matching comprehension is the actual generated
weakening functor applied to the independently supplied local datum. -/
def projection {B b} (hB : Typed.TyDeriv.{2} Γ γ B b) (A : SplitSheaf.Ty X) :
    Datum a (.ext hΓ hB) A ⥤ Datum a hΓ A :=
  substitution a hΓ (.ext hΓ hB) (.weaken hΓ hB) A

end SquareKit.SmoothQuotientGeneratedMatching
