import SquareKit.Internal.PathTransport.GeneratedCylinder
import SquareKit.Internal.PathTransport.SelectedSectionIso

/-! Selected cylinder components commute with every generated substitution,
including root, path-tail, and comprehension substitutions. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} (F : C ⥤ D) (P : C ⥤ Type u)
variable {G : C ⥤ D} (η : F ≅ G)
local notation "L" => Instance.fullModel C P
local notation "M" => Instance.fullModel (Grpd.of (Cylinder F)) (projection F ⋙ P)

theorem generatedEndpointIso_substitution (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hΔ : Typed.CtxDeriv.{u+1} Δ δ) (hs : Typed.SubDeriv.{u+1} Δ δ Γ γ σ s) :
    isoWhiskerLeft (s L).down (generatedEndpointIso F P η hΓ) ≪≫
        eqToIso (generatedSubstitution_commutes (endpointSignature F P η) hΓ hΔ hs) =
      eqToIso (generatedSubstitution_commutes (inclusionSignature F P) hΓ hΔ hs) ≪≫
        isoWhiskerRight (generatedEndpointIso F P η hΔ) (s M).down := by
  let : (projectionSignature F P).base.map.IsEquivalence :=
    inferInstanceAs (projection F).IsEquivalence
  let := generatedContextMap_equivalence (projectionSignature F P)
    (fun _ => Function.bijective_id) hΓ
  let := generatedContextMap_equivalence (projectionSignature F P)
    (fun _ => Function.bijective_id) hΔ
  exact selectedSectionIso_square
    (generatedContextMap (projectionSignature F P) hΓ)
    (generatedContextMap (projectionSignature F P) hΔ) _ _ _ _
    (generatedInclusion_projection F P hΓ) (generatedEndpoint_projection F P η hΓ)
    (generatedInclusion_projection F P hΔ) (generatedEndpoint_projection F P η hΔ)
    (s L).down (s M).down
    (generatedSubstitution_commutes (projectionSignature F P) hΓ hΔ hs)
    (generatedSubstitution_commutes (inclusionSignature F P) hΓ hΔ hs)
    (generatedSubstitution_commutes (endpointSignature F P η) hΓ hΔ hs)

variable (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q)
local notation "R" => Instance.fullModel D Q

private theorem evaluatedInclusion_substitution (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hΔ : Typed.CtxDeriv.{u+1} Δ δ) (hs : Typed.SubDeriv.{u+1} Δ δ Γ γ σ s) :
    (s L).down ⋙ (generatedContextMap (inclusionSignature F P) hΓ ⋙
      generatedContextMap (evaluationSignature F P Q α) hΓ) =
      (generatedContextMap (inclusionSignature F P) hΔ ⋙
        generatedContextMap (evaluationSignature F P Q α) hΔ) ⋙ (s R).down := by
  rw [generatedInclusion_evaluation, generatedInclusion_evaluation]
  exact generatedSubstitution_commutes ⟨⟨C, D, F⟩, P, Q, α⟩ hΓ hΔ hs

private theorem evaluatedEndpoint_substitution (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hΔ : Typed.CtxDeriv.{u+1} Δ δ) (hs : Typed.SubDeriv.{u+1} Δ δ Γ γ σ s) :
    (s L).down ⋙ (generatedContextMap (endpointSignature F P η) hΓ ⋙
      generatedContextMap (evaluationSignature F P Q α) hΓ) =
      (generatedContextMap (endpointSignature F P η) hΔ ⋙
        generatedContextMap (evaluationSignature F P Q α) hΔ) ⋙ (s R).down := by
  rw [generatedEndpoint_evaluation, generatedEndpoint_evaluation]
  exact generatedSubstitution_commutes ⟨⟨C, D, G⟩, P, Q, α ≫ whiskerRight η.hom Q⟩ hΓ hΔ hs

theorem generatedComparison_substitution (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hΔ : Typed.CtxDeriv.{u+1} Δ δ) (hs : Typed.SubDeriv.{u+1} Δ δ Γ γ σ s) :
    isoWhiskerLeft (s L).down (generatedComparison F P η Q α hΓ) ≪≫
        eqToIso (evaluatedEndpoint_substitution F P η Q α hΓ hΔ hs) =
      eqToIso (evaluatedInclusion_substitution F P Q α hΓ hΔ hs) ≪≫
        isoWhiskerRight (generatedComparison F P η Q α hΔ) (s R).down :=
  isoSquare_postcompose (s L).down (s M).down (s R).down _ _
    (generatedSubstitution_commutes (evaluationSignature F P Q α) hΓ hΔ hs)
    (generatedSubstitution_commutes (inclusionSignature F P) hΓ hΔ hs)
    (generatedSubstitution_commutes (endpointSignature F P η) hΓ hΔ hs)
    _ _ (generatedEndpointIso_substitution F P η hΓ hΔ hs) _ _

/-- The original endpoint comparisons commute with every generated substitution,
with the selected components and the existing strict substitution squares. -/
theorem contextComparison_substitution (β : P ⟶ G ⋙ Q)
    (h : α ≫ whiskerRight η.hom Q = β)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) (hΔ : Typed.CtxDeriv.{u+1} Δ δ)
    (hs : Typed.SubDeriv.{u+1} Δ δ Γ γ σ s) :
    isoWhiskerLeft (s L).down (contextComparison F P η Q α β h hΓ) ≪≫
        eqToIso (generatedSubstitution_commutes ⟨⟨C, D, G⟩, P, Q, β⟩ hΓ hΔ hs) =
      eqToIso (generatedSubstitution_commutes ⟨⟨C, D, F⟩, P, Q, α⟩ hΓ hΔ hs) ≪≫
        isoWhiskerRight (contextComparison F P η Q α β h hΔ) (s R).down := by
  cases h
  exact isoSquare_relabel (s L).down (s R).down
    (generatedComparison F P η Q α hΓ) (generatedComparison F P η Q α hΔ)
    (generatedInclusion_evaluation F P Q α hΓ)
    (generatedEndpoint_evaluation F P η Q α hΓ)
    (generatedInclusion_evaluation F P Q α hΔ)
    (generatedEndpoint_evaluation F P η Q α hΔ)
    _ _ _ _ (generatedComparison_substitution F P η Q α hΓ hΔ hs)

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
