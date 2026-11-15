import SquareKit.SmoothQuotientGeneratedRelativeDiagram
import SquareKit.SmoothQuotientGeneratedMatchingSubstitution
import SquareKit.Internal.PathTransport.CechMatchingComprehensionEquivalence

/-! Independent dependent matching for the actual generated families. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
variable (A : SplitSheaf.Ty X)

/-- The fiber specifies a local fiber object, an actual total overlap arrow,
its Čech laws, and its prescribed base overlap. Morphisms retain vertical arrows. -/
def relativeMatchingFamily : Datum a hΓ A ⥤ Grpd.{1,1} :=
  CechMatching.Comprehension.family (relativeFamilyData a hΓ hB A)
    (relativeFamilyCoherence a hΓ hB A)

/-- Independent family matching reconstructs all extended-context matching. -/
def dependentComprehensionEquivalence :
    Grothendieck (relativeMatchingFamily a hΓ hB A ⋙ Grpd.forgetToCat) ≌
      Datum a (.ext hΓ hB) A :=
  (CechMatching.Comprehension.equivalence (relativeFamilyData a hΓ hB A)
    (relativeFamilyCoherence a hΓ hB A)).trans (relativeMatchingEquivalence a hΓ hB A)

theorem relativeProjection_eq :
    (relativeToGenerated a hΓ hB A).functor ⋙ projection a hΓ hB A =
      ((relativeFamilyData a hΓ hB A).projection
        (relativeFamilyCoherence a hΓ hB A)).functor := by
  change (relativeToGenerated a hΓ hB A).functor ⋙
    (substitutionDiagram a hΓ (.ext hΓ hB) (.weaken hΓ hB) A).functor = _
  rw [← CechMatching.StrictMap.functor_comp]
  congr 1

/-- Recovery retains the supplied base datum naturally on all total arrows. -/
def dependentComprehensionProjection :
    (dependentComprehensionEquivalence a hΓ hB A).functor ⋙ projection a hΓ hB A ≅
      Grothendieck.forget (relativeMatchingFamily a hΓ hB A ⋙ Grpd.forgetToCat) := by
  change (CechMatching.Comprehension.totalFunctor _ _ ⋙
    (relativeToGenerated a hΓ hB A).functor) ⋙ projection a hΓ hB A ≅ _
  rw [Functor.assoc, relativeProjection_eq]
  exact CechMatching.Comprehension.projectionComparison _ _

end SquareKit.SmoothQuotientGeneratedMatching
