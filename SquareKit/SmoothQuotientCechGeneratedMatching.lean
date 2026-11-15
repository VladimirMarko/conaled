import SquareKit.SmoothQuotientCechGeneratedOverlap
import SquareKit.Internal.PathTransport.SelectedIsoTransport

/-! Normalization of generated selected overlaps into the actual restriction
Čech diagram. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y Z : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

theorem localMap_twice (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (f : Y ⟶ SplitSheaf.Ext A) (g : Z ⟶ Y) :
    (localMap a A hΓ ⋙ SmoothQuotientGeneratedMatching.restriction a hΓ f) ⋙
      SmoothQuotientGeneratedMatching.restriction a hΓ g =
    parameterMap a A hΓ (g ≫ f) := by
  rw [Functor.assoc, SmoothQuotientGeneratedMatching.restriction_comp]
  exact localMap_restriction a A hΓ (g ≫ f)

theorem generatedOverlap_restrict (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (f : Y ⟶ SplitSheaf.Cech.double A) :
    isoWhiskerRight (generatedOverlap a A hΓ)
      (SmoothQuotientGeneratedMatching.restriction a hΓ f) =
    eqToIso (localMap_twice a A hΓ (SplitSheaf.Cech.first A) f) ≪≫
      restrictedComparison a A hΓ f ≪≫
      (eqToIso (localMap_twice a A hΓ (SplitSheaf.Cech.second A) f)).symm := by
  rw [restrictedComparison_formula]
  exact whiskerRelabel _ (localMap_restriction a A hΓ (SplitSheaf.Cech.first A))
    (localMap_restriction a A hΓ (SplitSheaf.Cech.second A)) _ _ _ _ _

theorem generatedOverlap_diagonal (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    isoWhiskerRight (generatedOverlap a A hΓ)
      (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.diagonal A)) =
    isoWhiskerLeft (localMap a A hΓ)
      (eqToIso (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).diagonalFirst) ≪≫
    (isoWhiskerLeft (localMap a A hΓ)
      (eqToIso (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).diagonalSecond)).symm := by
  rw [generatedOverlap_restrict, restrictedComparison_diagonal]
  exact diagonalRelabel _ _ _ _ _ _

end SquareKit.SmoothQuotientCechLocal
