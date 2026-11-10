import SquareKit.SmoothQuotientCoverRelativeDiagram
import SquareKit.SmoothQuotientCoverSubstitution
import SquareKit.Internal.PathTransport.CechMatchingComprehensionEquivalence

/-! Independent dependent matching for the actual generated families. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
variable (f : Y ⟶ X)

/-- The fiber specifies a local fiber object, an actual total overlap arrow,
its Čech laws, and its prescribed base overlap. Morphisms retain vertical arrows. -/
def relativeMatchingFamily : Datum a hΓ f ⥤ Grpd.{1,1} :=
  CechMatching.Comprehension.family (relativeFamilyData a hΓ hB f)
    (relativeFamilyCoherence a hΓ hB f)

/-- Independent family matching reconstructs all extended-context matching. -/
def dependentComprehensionEquivalence :
    Grothendieck (relativeMatchingFamily a hΓ hB f ⋙ Grpd.forgetToCat) ≌
      Datum a (.ext hΓ hB) f :=
  (CechMatching.Comprehension.equivalence (relativeFamilyData a hΓ hB f)
    (relativeFamilyCoherence a hΓ hB f)).trans (relativeMatchingEquivalence a hΓ hB f)

theorem relativeProjection_eq :
    (relativeToGenerated a hΓ hB f).functor ⋙ projection a hΓ hB f =
      ((relativeFamilyData a hΓ hB f).projection
        (relativeFamilyCoherence a hΓ hB f)).functor := by
  change (relativeToGenerated a hΓ hB f).functor ⋙
    (substitutionDiagram a hΓ (.ext hΓ hB) (.weaken hΓ hB) f).functor = _
  rw [← CechMatching.StrictMap.functor_comp]
  congr 1

/-- Recovery retains the supplied base datum naturally on all total arrows. -/
def dependentComprehensionProjection :
    (dependentComprehensionEquivalence a hΓ hB f).functor ⋙ projection a hΓ hB f ≅
      Grothendieck.forget (relativeMatchingFamily a hΓ hB f ⋙ Grpd.forgetToCat) := by
  change (CechMatching.Comprehension.totalFunctor _ _ ⋙
    (relativeToGenerated a hΓ hB f).functor) ⋙ projection a hΓ hB f ≅ _
  rw [Functor.assoc, relativeProjection_eq]
  exact CechMatching.Comprehension.projectionComparison _ _

end SquareKit.SmoothQuotientCoverMatching
