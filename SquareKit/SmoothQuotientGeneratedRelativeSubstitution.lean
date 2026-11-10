import SquareKit.SmoothQuotientGeneratedRelativeMatching
import SquareKit.SmoothQuotientGeneratedMatchingSubstitution
import SquareKit.Internal.PathTransport.CechMatchingComprehensionPullFull
import SquareKit.Internal.PathTransport.GeneratedFamilyReindex
import SquareKit.Internal.PathTransport.Binding

/-! Substituted families are actual pullbacks of their relative matching diagrams. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ Δ δ B b σ s} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
variable (hB : Typed.TyDeriv.{2} Γ γ B b) (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s)

theorem relativeFamilyData_sub (A : SplitSheaf.Ty X) :
    relativeFamilyData a hΔ (.sub hB hs) A =
      CechMatching.Comprehension.Pull.data (substitutionDiagram a hΓ hΔ hs A)
        (relativeFamilyData a hΓ hB A) := by
  unfold relativeFamilyData familyRestriction interpretedFamily
  congr 1 <;> exact generatedFamilyMap_sub _ hΓ hΔ hB hs

def relativeSubstitution (A : SplitSheaf.Ty X) :
    CechMatching.StrictMap
      ((relativeFamilyData a hΔ (.sub hB hs) A).total (relativeFamilyCoherence a hΔ (.sub hB hs) A))
      ((relativeFamilyData a hΓ hB A).total (relativeFamilyCoherence a hΓ hB A)) :=
  ((relativeToGenerated a hΔ (.sub hB hs) A).comp
    (substitutionDiagram a (.ext hΓ hB) (.ext hΔ (.sub hB hs))
      (Typed.Authoring.liftSubstitution hΔ hB hs) A)).comp
    (generatedToRelative a hΓ hB A)

theorem relativeSubstitution_projection (A : SplitSheaf.Ty X) :
    (relativeSubstitution a hΓ hΔ hB hs A).comp
        ((relativeFamilyData a hΓ hB A).projection (relativeFamilyCoherence a hΓ hB A)) =
      ((relativeFamilyData a hΔ (.sub hB hs) A).projection
        (relativeFamilyCoherence a hΔ (.sub hB hs) A)).comp
          (substitutionDiagram a hΓ hΔ hs A) :=
  CechMatching.StrictMap.ext _ _ rfl rfl rfl

theorem relativeSubstitution_fiber_full (A : SplitSheaf.Ty X)
    (d : CechMatching.Datum (strictDiagram a hΔ A).toDiagram) :
    (CechMatching.Comprehension.fiberMap (substitutionDiagram a hΓ hΔ hs A)
      (relativeSubstitution a hΓ hΔ hB hs A)
      (relativeSubstitution_projection a hΓ hΔ hB hs A) d).Full ∧
    (CechMatching.Comprehension.fiberMap (substitutionDiagram a hΓ hΔ hs A)
      (relativeSubstitution a hΓ hΔ hB hs A)
      (relativeSubstitution_projection a hΓ hΔ hB hs A) d).Faithful :=
  CechMatching.Comprehension.fiberMap_full_of_pull _ _ _ _ _
    (relativeFamilyData_sub a hΓ hΔ hB hs A) _ _ HEq.rfl HEq.rfl HEq.rfl d

end SquareKit.SmoothQuotientGeneratedMatching
