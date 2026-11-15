import SquareKit.SmoothQuotientCoverGeneratedSections
import SquareKit.SmoothQuotientCoverFamilyNaturality

/-! Chosen gluing of whole matching-section lifts commutes with arbitrary
parameter cover squares and retains supplied section comparisons. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y X' Y' : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
variable (f : Y ⟶ X) [Presheaf.IsLocallySurjective topology f.hom]

/-- Gluing before normalization of the matching base; it retains the full section lift. -/
def gluedSectionLift (s : Section (relativeMatchingFamily a hΓ hB f)) :=
  s.lift ⋙ (dependentComprehensionEquivalence a hΓ hB f).functor ⋙
    (descentEquivalence a (.ext hΓ hB) f).inverse

variable (k : Y' ⟶ X') [Presheaf.IsLocallySurjective topology k.hom]
variable (u : X' ⟶ X) (v : Y' ⟶ Y) (square : v ≫ f = k ≫ u)

/-- Compatibility of supplied local sections gives compatibility of complete
chosen gluings, naturally on all matching arrows. The input comparison lives
entirely on local matching data, before either global gluing is constructed. -/
def gluedSectionLift_natural
    (s : Section (relativeMatchingFamily a hΓ hB f))
    (t : Section (relativeMatchingFamily a hΓ hB k))
    (localComparison :
      s.lift ⋙ (dependentComprehensionEquivalence a hΓ hB f).functor ⋙
          squareFunctor a (.ext hΓ hB) u v square ≅
        squareFunctor a hΓ u v square ⋙ t.lift ⋙
          (dependentComprehensionEquivalence a hΓ hB k).functor) :
    gluedSectionLift a hΓ hB f s ⋙ SmoothQuotientGeneratedMatching.restriction a (.ext hΓ hB) u ≅
      squareFunctor a hΓ u v square ⋙ gluedSectionLift a hΓ hB k t :=
  isoWhiskerLeft (s.lift ⋙ (dependentComprehensionEquivalence a hΓ hB f).functor)
    (descentSquare a (.ext hΓ hB) f k u v square) ≪≫
  isoWhiskerRight localComparison (descentEquivalence a (.ext hΓ hB) k).inverse

end SquareKit.SmoothQuotientCoverMatching
