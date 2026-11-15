import SquareKit.SmoothQuotientCoverMatchingNaturality
import SquareKit.SmoothQuotientCechContextEffectivity

/-! Actual generated restriction is effective for arbitrary locally surjective covers. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory SmoothOpenSite SheafActionQuotient Internal.PathTransport
open SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (hΓ : Typed.CtxDeriv.{2} Γ γ) (f : Y ⟶ X)
variable [Presheaf.IsLocallySurjective topology f.hom]

theorem restriction_isEquivalence : (restrictionFunctor a hΓ f).IsEquivalence := by
  let : (SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ (SplitSheaf.ofDisplay f)).IsEquivalence :=
    SmoothQuotientGeneratedMatching.restriction_isEquivalence a (SplitSheaf.ofDisplay f) hΓ
  let : (restrictionFunctor a hΓ f ⋙ (matchingEquivalence a hΓ f).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso (eqToIso (restriction_toSplit a hΓ f)).symm
  exact Functor.isEquivalence_of_comp_right _ (matchingEquivalence a hΓ f).functor

def descentEquivalence : context a hΓ X ≌ Datum a hΓ f := by
  let := restriction_isEquivalence a hΓ f
  exact (restrictionFunctor a hΓ f).asEquivalence

/-- Recovery is natural in every supplied matching arrow. -/
theorem descentRecovery_natural {d e : Datum a hΓ f} (p : d ⟶ e) :
    (restrictionFunctor a hΓ f).map ((descentEquivalence a hΓ f).inverse.map p) ≫
        ((descentEquivalence a hΓ f).counitIso.app e).hom =
      ((descentEquivalence a hΓ f).counitIso.app d).hom ≫ p :=
  (descentEquivalence a hΓ f).counitIso.hom.naturality p

variable {X' Y' : Sheaf topology Type} (k : Y' ⟶ X')
variable [Presheaf.IsLocallySurjective topology k.hom]
variable (u : X' ⟶ X) (v : Y' ⟶ Y) (square : v ≫ f = k ≫ u)

/-- Chosen descent commutes with every cover square by a selected isomorphism. -/
def descentSquare :
    (descentEquivalence a hΓ f).inverse ⋙ restriction a hΓ u ≅
      squareFunctor a hΓ u v square ⋙ (descentEquivalence a hΓ k).inverse := by
  let E := descentEquivalence a hΓ f
  let K := descentEquivalence a hΓ k
  let i : E.functor ⋙ squareFunctor a hΓ u v square ≅ restriction a hΓ u ⋙ K.functor :=
    eqToIso (restriction_square a hΓ u v square)
  exact ((Functor.associator E.inverse (restriction a hΓ u) K.functor) ≪≫
    Iso.inverseCompIso (G := E) i.symm).isoCompInverse (H := K)

end SquareKit.SmoothQuotientCoverMatching
