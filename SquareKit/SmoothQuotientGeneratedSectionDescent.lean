import SquareKit.SmoothQuotientCechContextEffectivity
import SquareKit.SmoothQuotientCechFamilyTransport
import SquareKit.Internal.PathTransport.SectionDescentResult
import SquareKit.Internal.PathTransport.CechMatchingComprehensionInverseProjection
import SquareKit.Internal.PathTransport.CechMatchingCanonicalSquare

/-! Full section descent with recovery through actual canonical restriction. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ Δ δ σ s} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
variable (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s)

theorem restriction_substitution :
    restrictionFunctor a hΔ A ⋙ substitution a hΓ hΔ hs A =
      (s (SmoothQuotientSource.model a X)).down ⋙ restrictionFunctor a hΓ A :=
  CechMatching.canonical_square (substitutionDiagram a hΓ hΔ hs A)
    (restriction a hΔ (SplitSheaf.p A)) (s (SmoothQuotientSource.model a X)).down
    (restriction a hΓ (SplitSheaf.p A)) (restrictionOverlap_eq a hΔ A)
    (restrictionOverlap_eq a hΓ A)
    (generatedSubstitution_commutes (SmoothQuotientComparison.signature (a := a) (SplitSheaf.p A))
      hΓ hΔ hs).symm

variable {B b} (hB : Typed.TyDeriv.{2} Γ γ B b)

def totalRestriction := restrictionFunctor a (.ext hΓ hB) A ⋙
  (generatedToRelative a hΓ hB A).functor

theorem totalRestriction_projection :
    totalRestriction a A hΓ hB ⋙
      ((relativeFamilyData a hΓ hB A).projection (relativeFamilyCoherence a hΓ hB A)).functor =
    weaken (b (SmoothQuotientSource.model a X)) ⋙ restrictionFunctor a hΓ A := by
  have hp : (generatedToRelative a hΓ hB A).functor ⋙
      ((relativeFamilyData a hΓ hB A).projection (relativeFamilyCoherence a hΓ hB A)).functor =
      projection a hΓ hB A := by
    rw [← CechMatching.StrictMap.functor_comp]
    congr 1
  dsimp only [totalRestriction]
  rw [Functor.assoc, hp]
  exact restriction_substitution a A hΓ (.ext hΓ hB) (.weaken hΓ hB)

variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

def sectionTotalEquivalence :
    Extend (b (SmoothQuotientSource.model a X)) ≌ Extend (relativeMatchingFamily a hΓ hB A) :=
  (descentEquivalence a A (.ext hΓ hB)).trans
    ((relativeMatchingEquivalence a hΓ hB A).symm.trans
      (CechMatching.Comprehension.equivalence (relativeFamilyData a hΓ hB A)
        (relativeFamilyCoherence a hΓ hB A)).symm)

def sectionTotalProjection :
    (sectionTotalEquivalence a A hΓ hB).functor ⋙ weaken (relativeMatchingFamily a hΓ hB A) ≅
      weaken (b (SmoothQuotientSource.model a X)) ⋙ (descentEquivalence a A hΓ).functor :=
  isoWhiskerLeft (totalRestriction a A hΓ hB)
    (CechMatching.Comprehension.inverseProjectionComparison
      (relativeFamilyData a hΓ hB A) (relativeFamilyCoherence a hΓ hB A)) ≪≫
    eqToIso (totalRestriction_projection a A hΓ hB)

/-- Reconstruction and all vertical comparisons for independently supplied matching sections. -/
def sectionDescent :
    SectionDescent.Result (descentEquivalence a A hΓ)
      (sectionTotalEquivalence a A hΓ hB) (sectionTotalProjection a A hΓ hB) :=
  SectionDescent.result _ _ _

end SquareKit.SmoothQuotientGeneratedMatching
