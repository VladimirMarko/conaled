import SquareKit.SmoothQuotientCoverPresentationSections
import Examples.OriginalCoverMatching
import SquareKit.SmoothQuotientCoverFamilyNaturality
import SquareKit.SmoothQuotientCoverSourceSection
import Examples.SmoothSelectedComparison

/-! Complete generated sections on the actual two-sheet sheaf cover. -/
noncomputable section
namespace Examples.OriginalCoverGeneratedSections
open CategoryTheory SquareKit SmoothOpenSite SheafActionQuotient
open Internal.PathTransport GroupoidModel SmoothQuotientCoverMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)

/-- Arbitrary matching data, without a supplied global extension, are recovered. -/
example (d : Datum a hΓ (ArbitraryCoverSections.twoSheet X)) :
    (restrictionFunctor a hΓ (ArbitraryCoverSections.twoSheet X)).obj
      ((descentEquivalence a hΓ (ArbitraryCoverSections.twoSheet X)).inverse.obj d) ≅ d :=
  (descentEquivalence a hΓ (ArbitraryCoverSections.twoSheet X)).counitIso.app d

/-- A full independent matching section gives a global section for every typed family. -/
example (s : Section (relativeMatchingFamily a hΓ hB (ArbitraryCoverSections.twoSheet X))) :
    Section (b (SmoothQuotientSource.model a X)) :=
  (sectionDescent a (ArbitraryCoverSections.twoSheet X) hΓ hB).reconstruct s

/-- Recovery is an isomorphism of whole lifted sections, not just objectwise equality. -/
example (s : Section (relativeMatchingFamily a hΓ hB (ArbitraryCoverSections.twoSheet X))) :
    ((sectionDescent a (ArbitraryCoverSections.twoSheet X) hΓ hB).reconstruct s).lift ⋙
        (sectionTotalEquivalence a (ArbitraryCoverSections.twoSheet X) hΓ hB).functor ≅
      (descentEquivalence a hΓ (ArbitraryCoverSections.twoSheet X)).functor ⋙ s.lift :=
  (sectionDescent a (ArbitraryCoverSections.twoSheet X) hΓ hB).recovery s

/-- Every selected vertical transformation is recovered uniquely. -/
example (s t : Section (relativeMatchingFamily a hΓ hB (ArbitraryCoverSections.twoSheet X))) :
    {η : ((sectionDescent a (ArbitraryCoverSections.twoSheet X) hΓ hB).reconstruct s).lift ⟶
        ((sectionDescent a (ArbitraryCoverSections.twoSheet X) hΓ hB).reconstruct t).lift //
      ∀ c, (η.app c).base = 𝟙 c} ≃
    {η : s.lift ⟶ t.lift // ∀ d, (η.app d).base = 𝟙 d} :=
  (sectionDescent a (ArbitraryCoverSections.twoSheet X) hΓ hB).verticalEquiv s t

/-- The split-to-original presentation transfer accepts independent split sections. -/
example (s : Section (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB
    (SplitSheaf.ofDisplay (ArbitraryCoverSections.twoSheet X)))) :
    Section (relativeMatchingFamily a hΓ hB (ArbitraryCoverSections.twoSheet X)) :=
  (presentationSections a (ArbitraryCoverSections.twoSheet X) hΓ hB).reconstruct s

/-- Presentation recovery keeps the chosen base arrow of each lifted component. -/
example (s : Section (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB
    (SplitSheaf.ofDisplay (ArbitraryCoverSections.twoSheet X))))
    (d : Datum a hΓ (ArbitraryCoverSections.twoSheet X)) :
    (((presentationSections a (ArbitraryCoverSections.twoSheet X) hΓ hB).recovery s).hom.app d).base =
      (presentationTotalProjection a (ArbitraryCoverSections.twoSheet X) hΓ hB).hom.app
        (((presentationSections a (ArbitraryCoverSections.twoSheet X) hΓ hB).reconstruct s).lift.obj d) :=
  (presentationSections a (ArbitraryCoverSections.twoSheet X) hΓ hB).recovery_base s d

/-- Arbitrary parameter pullback acts on independently supplied matching fibers. -/
example {Z : Sheaf topology Type} (u : Z ⟶ X)
    (d : Datum a hΓ (ArbitraryCoverSections.twoSheet X)) :
    (relativeMatchingFamily a hΓ hB (ArbitraryCoverSections.twoSheet X)).obj d ⥤
      (relativeMatchingFamily a hΓ hB (Limits.pullback.snd
        (ArbitraryCoverSections.twoSheet X) u)).obj
        ((squareFunctor a hΓ u (Limits.pullback.fst (ArbitraryCoverSections.twoSheet X) u)
          Limits.pullback.condition).obj d) :=
  familySquare a hΓ hB u _ Limits.pullback.condition d

/-- The classical consumer's exact source proof restricts through the original cover. -/
example := universalTransfer_restriction SmoothQuarterTurnQuotient.diskRepresentation.action
  (ArbitraryCoverSections.twoSheet SmoothQuarterTurnQuotient.realBase)

/-- The same original-cover equation covers the retained dependent-tail J caller. -/
example := sourceSection_totalRestriction a (ArbitraryCoverSections.twoSheet X)
  SignatureInterpretationMaps.DependentTail.withFiber
  SignatureInterpretationMaps.DependentTail.command.motive.typing
  SignatureInterpretationMaps.DependentTail.generic

end Examples.OriginalCoverGeneratedSections
