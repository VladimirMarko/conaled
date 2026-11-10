import SquareKit.SmoothQuotientCechGeneratedCone
import SquareKit.Internal.PathTransport.CechMatchingConeMap
import SquareKit.Internal.PathTransport.AlignedSignatureSubstitution
import SquareKit.SmoothQuotientGeneratedMatchingSubstitution

/-! The selected local evaluation cone commutes with generated substitutions. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
variable (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s)
include hs

theorem localMap_substitution :
    (s (model a A)).down ⋙ localMap a A hΓ =
      localMap a A hΔ ⋙ (s (SmoothQuotientSource.model a (SplitSheaf.Ext A))).down :=
  generatedSubstitution_commutes (signature a A) hΓ hΔ hs

theorem parameterMap_substitution (f : Y ⟶ SplitSheaf.Ext A) :
    (s (model a A)).down ⋙ parameterMap a A hΓ f =
      parameterMap a A hΔ f ⋙ (s (SmoothQuotientSource.model a Y)).down :=
  generatedSubstitution_commutes (parameterSignature a A f) hΓ hΔ hs

theorem localComposite_substitution (f : Y ⟶ SplitSheaf.Ext A) :
    (s (model a A)).down ⋙
        (localMap a A hΓ ⋙ SmoothQuotientGeneratedMatching.restriction a hΓ f) =
      (localMap a A hΔ ⋙ SmoothQuotientGeneratedMatching.restriction a hΔ f) ⋙
        (s (SmoothQuotientSource.model a Y)).down := by
  rw [localMap_restriction, localMap_restriction]
  exact parameterMap_substitution a A hΓ hΔ hs f

theorem generatedOverlap_substitution :
    isoWhiskerLeft (s (model a A)).down (generatedOverlap a A hΓ) ≪≫
      eqToIso (localComposite_substitution a A hΓ hΔ hs (SplitSheaf.Cech.second A)) =
    eqToIso (localComposite_substitution a A hΓ hΔ hs (SplitSheaf.Cech.first A)) ≪≫
      isoWhiskerRight (generatedOverlap a A hΔ)
        (s (SmoothQuotientSource.model a (SplitSheaf.Cech.double A))).down := by
  have h := alignedContextComparison_substitution (overlap a A)
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
    (family a (SplitSheaf.Cech.double A)) (firstFiber a A) (secondFiber a A)
    (overlap_square a A) hΓ hΔ hs
  exact isoSquare_relabel (s (model a A)).down
    (s (SmoothQuotientSource.model a (SplitSheaf.Cech.double A))).down
    _ _
    (localMap_restriction a A hΓ (SplitSheaf.Cech.first A)).symm
    (localMap_restriction a A hΓ (SplitSheaf.Cech.second A)).symm
    (localMap_restriction a A hΔ (SplitSheaf.Cech.first A)).symm
    (localMap_restriction a A hΔ (SplitSheaf.Cech.second A)).symm
    (parameterMap_substitution a A hΓ hΔ hs (SplitSheaf.Cech.first A))
    (parameterMap_substitution a A hΓ hΔ hs (SplitSheaf.Cech.second A))
    (localComposite_substitution a A hΓ hΔ hs (SplitSheaf.Cech.first A))
    (localComposite_substitution a A hΓ hΔ hs (SplitSheaf.Cech.second A)) h

/-- Complete matching evaluation, including its overlap, commutes with substitution. -/
theorem matchingEvaluation_substitution :
    matchingEvaluation a A hΔ ⋙
      SmoothQuotientGeneratedMatching.substitution a hΓ hΔ hs A =
    (s (model a A)).down ⋙ matchingEvaluation a A hΓ := by
  apply CechMatching.ConeMap.coneFunctor_map
    (SmoothQuotientGeneratedMatching.substitutionDiagram a hΓ hΔ hs A)
    (localMap a A hΔ) (localMap a A hΓ) (s (model a A)).down
    (generatedOverlap a A hΔ) (generatedOverlap a A hΓ)
    (generatedConeLaws a A hΔ) (generatedConeLaws a A hΓ)
    (localMap_substitution a A hΓ hΔ hs).symm
  exact CechMatching.ConeMap.transportedOverlap_of_square
    (SmoothQuotientGeneratedMatching.substitutionDiagram a hΓ hΔ hs A)
    (localMap a A hΔ) (localMap a A hΓ) (s (model a A)).down
    (generatedOverlap a A hΔ) (generatedOverlap a A hΓ)
    (localMap_substitution a A hΓ hΔ hs).symm
    (localComposite_substitution a A hΓ hΔ hs (SplitSheaf.Cech.first A))
    (localComposite_substitution a A hΓ hΔ hs (SplitSheaf.Cech.second A))
    (generatedOverlap_substitution a A hΓ hΔ hs)

end SquareKit.SmoothQuotientCechLocal
