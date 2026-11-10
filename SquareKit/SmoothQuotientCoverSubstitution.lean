import SquareKit.SmoothQuotientCoverMatching
import SquareKit.Internal.PathTransport.CechMatchingMap

/-! Generated substitutions act on independent matching data. This includes
comprehension projections, dependent-tail maps and path reindexing. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel Comparison SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ Δ δ σ s} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
variable (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s)

/-- All six squares follow from generated substitution preservation at the
actual parameter maps. No matching-data functor is an assumed field. -/
def substitutionDiagram (f : Y ⟶ X) :
    CechMatching.StrictMap (strictDiagram a hΔ f) (strictDiagram a hΓ f) where
  localMap := (s (SmoothQuotientSource.model a Y)).down
  doubleMap := (s (SmoothQuotientSource.model a (SheafCoverCech.double f))).down
  tripleMap := (s (SmoothQuotientSource.model a (SheafCoverCech.triple f))).down
  first := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SheafCoverCech.first f)) hΓ hΔ hs
  second := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SheafCoverCech.second f)) hΓ hΔ hs
  diagonal := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SheafCoverCech.diagonal f)) hΓ hΔ hs
  firstSecond := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SheafCoverCech.firstSecond f)) hΓ hΔ hs
  firstThird := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SheafCoverCech.firstThird f)) hΓ hΔ hs
  secondThird := generatedSubstitution_commutes
    (SmoothQuotientComparison.signature (a := a) (SheafCoverCech.secondThird f)) hΓ hΔ hs

/-- Independent local data are mapped through the generated substitution. -/
def substitution (f : Y ⟶ X) : Datum a hΔ f ⥤ Datum a hΓ f :=
  (substitutionDiagram a hΓ hΔ hs f).functor

/-- The complete local functor, including its arrow action, is retained. -/
theorem substitution_local (f : Y ⟶ X) :
    substitution a hΓ hΔ hs f ⋙ CechMatching.Datum.localFunctor =
      CechMatching.Datum.localFunctor ⋙
        (s (SmoothQuotientSource.model a Y)).down := rfl

/-- The base projection of matching comprehension is the actual generated
weakening functor applied to the independently supplied local datum. -/
def projection {B b} (hB : Typed.TyDeriv.{2} Γ γ B b) (f : Y ⟶ X) :
    Datum a (.ext hΓ hB) f ⥤ Datum a hΓ f :=
  substitution a hΓ (.ext hΓ hB) (.weaken hΓ hB) f

end SquareKit.SmoothQuotientCoverMatching
