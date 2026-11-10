import SquareKit.SmoothQuotientCoverGeneratedSections
import SquareKit.SmoothQuotientCoverPresentationSubstitution
import SquareKit.SmoothQuotientGeneratedRelativeMatching

/-! Full dependent matching sections transfer between the original cover and its
split presentation, retaining selected vertical comparisons. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
private def inverseProjection {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) (p : D ⥤ E) (q : C ⥤ E) (α : e.functor ⋙ p ≅ q) :
    e.inverse ⋙ q ≅ p :=
  isoWhiskerLeft e.inverse α.symm ≪≫ isoWhiskerRight e.counitIso p

private def inverseSquare {C D E F : Type*} [Category C] [Category D]
    [Category E] [Category F] (e : C ≌ D) (t : E ≌ F)
    (p : E ⥤ C) (q : F ⥤ D) (α : t.functor ⋙ q ≅ p ⋙ e.functor) :
    t.inverse ⋙ p ≅ q ⋙ e.inverse :=
  ((Functor.associator t.inverse p e.functor) ≪≫
    Iso.inverseCompIso (G := t) α.symm).isoCompInverse (H := e)

variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (f : Y ⟶ X)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)

def presentationTotalEquivalence :
    Extend (relativeMatchingFamily a hΓ hB f) ≌
      Extend (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB
        (SplitSheaf.ofDisplay f)) :=
  (dependentComprehensionEquivalence a hΓ hB f).trans
    ((matchingEquivalence a (.ext hΓ hB) f).trans
      (SmoothQuotientGeneratedMatching.dependentComprehensionEquivalence a hΓ hB
        (SplitSheaf.ofDisplay f)).symm)

def splitInverseProjection :
    (SmoothQuotientGeneratedMatching.dependentComprehensionEquivalence a hΓ hB
      (SplitSheaf.ofDisplay f)).inverse ⋙
      weaken (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB
        (SplitSheaf.ofDisplay f)) ≅
    SmoothQuotientGeneratedMatching.projection a hΓ hB (SplitSheaf.ofDisplay f) :=
  inverseProjection (SmoothQuotientGeneratedMatching.dependentComprehensionEquivalence
    a hΓ hB (SplitSheaf.ofDisplay f))
    (SmoothQuotientGeneratedMatching.projection a hΓ hB (SplitSheaf.ofDisplay f))
    (weaken (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB (SplitSheaf.ofDisplay f)))
    (SmoothQuotientGeneratedMatching.dependentComprehensionProjection a hΓ hB (SplitSheaf.ofDisplay f))


def presentationTotalProjection :
    (presentationTotalEquivalence a f hΓ hB).functor ⋙
      weaken (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB
        (SplitSheaf.ofDisplay f)) ≅
    weaken (relativeMatchingFamily a hΓ hB f) ⋙ (matchingEquivalence a hΓ f).functor :=
  isoWhiskerLeft ((dependentComprehensionEquivalence a hΓ hB f).functor ⋙
      (matchingEquivalence a (.ext hΓ hB) f).functor)
    (splitInverseProjection a f hΓ hB) ≪≫
  isoWhiskerLeft (dependentComprehensionEquivalence a hΓ hB f).functor
    (eqToIso (toSplit_substitution a f hΓ (.ext hΓ hB) (.weaken hΓ hB))) ≪≫
  isoWhiskerRight (dependentComprehensionProjection a hΓ hB f)
    (matchingEquivalence a hΓ f).functor

/-- Split matching sections reconstruct original matching sections without a
cover-surjectivity assumption; the presentation itself is an equivalence. -/
def presentationSections :
    SectionDescent.Result (matchingEquivalence a hΓ f)
      (presentationTotalEquivalence a f hΓ hB) (presentationTotalProjection a f hΓ hB) :=
  SectionDescent.result _ _ _

def presentationInverseProjection :
    (presentationTotalEquivalence a f hΓ hB).inverse ⋙
      weaken (relativeMatchingFamily a hΓ hB f) ≅
    weaken (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB
      (SplitSheaf.ofDisplay f)) ⋙ (matchingEquivalence a hΓ f).inverse :=
  inverseSquare (matchingEquivalence a hΓ f) (presentationTotalEquivalence a f hΓ hB)
    (weaken (relativeMatchingFamily a hΓ hB f))
    (weaken (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB (SplitSheaf.ofDisplay f)))
    (presentationTotalProjection a f hΓ hB)

/-- The reverse transfer also retains all section arrows and its recovery base. -/
def inversePresentationSections :
    SectionDescent.Result (matchingEquivalence a hΓ f).symm
      (presentationTotalEquivalence a f hΓ hB).symm
      (presentationInverseProjection a f hΓ hB) :=
  SectionDescent.result _ _ _

end SquareKit.SmoothQuotientCoverMatching
