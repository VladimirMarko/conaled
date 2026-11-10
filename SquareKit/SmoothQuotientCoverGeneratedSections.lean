import SquareKit.SmoothQuotientCoverEffectivity
import SquareKit.SmoothQuotientCoverRelativeMatching
import SquareKit.SmoothQuotientCechFamilyTransport
import SquareKit.Internal.PathTransport.SectionDescentResult
import SquareKit.Internal.PathTransport.CechMatchingComprehensionInverseProjection
import SquareKit.Internal.PathTransport.CechMatchingCanonicalSquare

/-! Full section descent with recovery through actual canonical restriction. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (f : Y ⟶ X)
variable {Γ γ Δ δ σ s} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
variable (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s)

theorem restriction_substitution :
    restrictionFunctor a hΔ f ⋙ substitution a hΓ hΔ hs f =
      (s (SmoothQuotientSource.model a X)).down ⋙ restrictionFunctor a hΓ f :=
  CechMatching.canonical_square (substitutionDiagram a hΓ hΔ hs f)
    (restriction a hΔ f) (s (SmoothQuotientSource.model a X)).down
    (restriction a hΓ f) (restrictionOverlap_eq a hΔ f)
    (restrictionOverlap_eq a hΓ f)
    (generatedSubstitution_commutes (SmoothQuotientComparison.signature (a := a) f)
      hΓ hΔ hs).symm

variable {B b} (hB : Typed.TyDeriv.{2} Γ γ B b)

def totalRestriction := restrictionFunctor a (.ext hΓ hB) f ⋙
  (generatedToRelative a hΓ hB f).functor

theorem totalRestriction_projection :
    totalRestriction a f hΓ hB ⋙
      ((relativeFamilyData a hΓ hB f).projection (relativeFamilyCoherence a hΓ hB f)).functor =
    weaken (b (SmoothQuotientSource.model a X)) ⋙ restrictionFunctor a hΓ f := by
  have hp : (generatedToRelative a hΓ hB f).functor ⋙
      ((relativeFamilyData a hΓ hB f).projection (relativeFamilyCoherence a hΓ hB f)).functor =
      projection a hΓ hB f := by
    rw [← CechMatching.StrictMap.functor_comp]
    congr 1
  dsimp only [totalRestriction]
  rw [Functor.assoc, hp]
  exact restriction_substitution a f hΓ (.ext hΓ hB) (.weaken hΓ hB)

variable [Presheaf.IsLocallySurjective topology f.hom]

def sectionTotalEquivalence :
    Extend (b (SmoothQuotientSource.model a X)) ≌ Extend (relativeMatchingFamily a hΓ hB f) :=
  (descentEquivalence a (.ext hΓ hB) f).trans
    ((relativeMatchingEquivalence a hΓ hB f).symm.trans
      (CechMatching.Comprehension.equivalence (relativeFamilyData a hΓ hB f)
        (relativeFamilyCoherence a hΓ hB f)).symm)

def sectionTotalProjection :
    (sectionTotalEquivalence a f hΓ hB).functor ⋙ weaken (relativeMatchingFamily a hΓ hB f) ≅
      weaken (b (SmoothQuotientSource.model a X)) ⋙ (descentEquivalence a hΓ f).functor :=
  isoWhiskerLeft (totalRestriction a f hΓ hB)
    (CechMatching.Comprehension.inverseProjectionComparison
      (relativeFamilyData a hΓ hB f) (relativeFamilyCoherence a hΓ hB f)) ≪≫
    eqToIso (totalRestriction_projection a f hΓ hB)

/-- Reconstruction and all vertical comparisons for independently supplied matching sections. -/
def sectionDescent :
    SectionDescent.Result (descentEquivalence a hΓ f)
      (sectionTotalEquivalence a f hΓ hB) (sectionTotalProjection a f hΓ hB) :=
  SectionDescent.result _ _ _

end SquareKit.SmoothQuotientCoverMatching
