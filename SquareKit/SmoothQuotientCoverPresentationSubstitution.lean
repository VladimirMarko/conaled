import SquareKit.SmoothQuotientCoverSubstitution
import SquareKit.SmoothQuotientGeneratedMatchingSubstitution

/-! Presentation transfer retains every generated substitution and projection. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (f : Y ⟶ X)
variable (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
variable (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s)

theorem toSplit_substitutionMap :
    (toSplitMap a hΔ f).comp
        (SmoothQuotientGeneratedMatching.substitutionDiagram a hΓ hΔ hs (SplitSheaf.ofDisplay f)) =
      (substitutionDiagram a hΓ hΔ hs f).comp (toSplitMap a hΓ f) := by
  apply CechMatching.StrictMap.ext
  · exact (generatedSubstitution_commutes
      (SmoothQuotientComparison.signature (a := a) (SplitSheaf.displayIso f).hom) hΓ hΔ hs).symm
  · exact (generatedSubstitution_commutes
      (SmoothQuotientComparison.signature (a := a) (SheafCoverCech.splitDoubleIso f).hom) hΓ hΔ hs).symm
  · exact (generatedSubstitution_commutes
      (SmoothQuotientComparison.signature (a := a) (SheafCoverCech.splitTripleIso f).hom) hΓ hΔ hs).symm

theorem toSplit_substitution :
    (matchingEquivalence a hΔ f).functor ⋙
        SmoothQuotientGeneratedMatching.substitution a hΓ hΔ hs (SplitSheaf.ofDisplay f) =
      substitution a hΓ hΔ hs f ⋙ (matchingEquivalence a hΓ f).functor := by
  change (toSplitMap a hΔ f).functor ⋙
    (SmoothQuotientGeneratedMatching.substitutionDiagram a hΓ hΔ hs (SplitSheaf.ofDisplay f)).functor =
    (substitutionDiagram a hΓ hΔ hs f).functor ⋙ (toSplitMap a hΓ f).functor
  rw [← CechMatching.StrictMap.functor_comp, toSplit_substitutionMap,
    CechMatching.StrictMap.functor_comp]

end SquareKit.SmoothQuotientCoverMatching
