import SquareKit.Internal.PathTransport.GeneratedCylinderCoherence
import SquareKit.Internal.PathTransport.GeneratedPrimitiveFiber

/-! Selected context comparisons retain the square of a generated base term. -/
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

theorem endpointIso_selected : endpointIso F η =
    selectedSectionIso (projection F) (inclusion F) (endpoint F η) rfl rfl := by
  apply Iso.ext
  apply NatTrans.ext
  funext c
  apply (projection F).map_injective
  rw [selectedSectionIso_map]
  simp [endpointIso, projection, inclusion]

theorem generatedEndpointIso_baseTerm (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hx : Typed.TmDeriv.{u+1} Γ γ .base (Typed.baseCode γ) x ξ) :
    isoWhiskerLeft (baseFunctor (ξ L).down) (endpointIso F η) ≪≫
        eqToIso (generatedBaseTerm_commutes (endpointSignature F P η) hΓ hx) =
      eqToIso (generatedBaseTerm_commutes (inclusionSignature F P) hΓ hx) ≪≫
        isoWhiskerRight (generatedEndpointIso F P η hΓ) (baseFunctor (ξ M).down) := by
  let : (projectionSignature F P).base.map.IsEquivalence :=
    inferInstanceAs (projection F).IsEquivalence
  let := generatedContextMap_equivalence (projectionSignature F P)
    (fun _ => Function.bijective_id) hΓ
  rw [endpointIso_selected]
  exact selectedSectionIso_square (projection F)
    (generatedContextMap (projectionSignature F P) hΓ) _ _ _ _ rfl rfl
    (generatedInclusion_projection F P hΓ) (generatedEndpoint_projection F P η hΓ)
    (baseFunctor (ξ L).down) (baseFunctor (ξ M).down)
    (generatedBaseTerm_commutes (projectionSignature F P) hΓ hx)
    (generatedBaseTerm_commutes (inclusionSignature F P) hΓ hx)
    (generatedBaseTerm_commutes (endpointSignature F P η) hΓ hx)

variable (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q)
local notation "R" => Instance.fullModel D Q

private theorem evaluatedInclusion_baseTerm (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hx : Typed.TmDeriv.{u+1} Γ γ .base (Typed.baseCode γ) x ξ) :
    baseFunctor (ξ L).down ⋙ (inclusion F ⋙ evaluation F) =
      (generatedContextMap (inclusionSignature F P) hΓ ⋙
        generatedContextMap (evaluationSignature F P Q α) hΓ) ⋙
          baseFunctor (ξ R).down := by
  rw [inclusion_evaluation, generatedInclusion_evaluation]
  exact generatedBaseTerm_commutes ⟨⟨C, D, F⟩, P, Q, α⟩ hΓ hx

private theorem evaluatedEndpoint_baseTerm (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hx : Typed.TmDeriv.{u+1} Γ γ .base (Typed.baseCode γ) x ξ) :
    baseFunctor (ξ L).down ⋙ (endpoint F η ⋙ evaluation F) =
      (generatedContextMap (endpointSignature F P η) hΓ ⋙
        generatedContextMap (evaluationSignature F P Q α) hΓ) ⋙
          baseFunctor (ξ R).down := by
  rw [endpoint_evaluation, generatedEndpoint_evaluation]
  exact generatedBaseTerm_commutes
    ⟨⟨C, D, G⟩, P, Q, α ≫ whiskerRight η.hom Q⟩ hΓ hx

theorem generatedComparison_baseTerm (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hx : Typed.TmDeriv.{u+1} Γ γ .base (Typed.baseCode γ) x ξ) :
    isoWhiskerLeft (baseFunctor (ξ L).down)
        (isoWhiskerRight (endpointIso F η) (evaluation F)) ≪≫
        eqToIso (evaluatedEndpoint_baseTerm F P η Q α hΓ hx) =
      eqToIso (evaluatedInclusion_baseTerm F P Q α hΓ hx) ≪≫
        isoWhiskerRight (generatedComparison F P η Q α hΓ)
          (baseFunctor (ξ R).down) :=
  isoSquare_postcompose (baseFunctor (ξ L).down) (baseFunctor (ξ M).down)
    (baseFunctor (ξ R).down) _ _
    (generatedBaseTerm_commutes (evaluationSignature F P Q α) hΓ hx)
    (generatedBaseTerm_commutes (inclusionSignature F P) hΓ hx)
    (generatedBaseTerm_commutes (endpointSignature F P η) hΓ hx)
    _ _ (generatedEndpointIso_baseTerm F P η hΓ hx) _ _

theorem normalizedEndpointIso :
    (eqToIso (inclusion_evaluation F)).symm ≪≫
      isoWhiskerRight (endpointIso F η) (evaluation F) ≪≫
        eqToIso (endpoint_evaluation F η) = η := by
  ext c
  simp [endpointIso_evaluation]

/-- The actual generated base-term square commutes with the chosen comparison,
including its morphism components. Neither endpoint map must be invertible. -/
theorem contextComparison_baseTerm (β : P ⟶ G ⋙ Q)
    (h : α ≫ whiskerRight η.hom Q = β)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hx : Typed.TmDeriv.{u+1} Γ γ .base (Typed.baseCode γ) x ξ) :
    isoWhiskerLeft (baseFunctor (ξ L).down) η ≪≫
        eqToIso (generatedBaseTerm_commutes ⟨⟨C, D, G⟩, P, Q, β⟩ hΓ hx) =
      eqToIso (generatedBaseTerm_commutes ⟨⟨C, D, F⟩, P, Q, α⟩ hΓ hx) ≪≫
        isoWhiskerRight (contextComparison F P η Q α β h hΓ)
          (baseFunctor (ξ R).down) := by
  cases h
  have hh := isoSquare_relabel (baseFunctor (ξ L).down) (baseFunctor (ξ R).down)
    (isoWhiskerRight (endpointIso F η) (evaluation F))
    (generatedComparison F P η Q α hΓ)
    (inclusion_evaluation F) (endpoint_evaluation F η)
    (generatedInclusion_evaluation F P Q α hΓ)
    (generatedEndpoint_evaluation F P η Q α hΓ)
    _ _ (generatedBaseTerm_commutes ⟨⟨C, D, F⟩, P, Q, α⟩ hΓ hx)
    (generatedBaseTerm_commutes ⟨⟨C, D, G⟩, P, Q, α ≫ whiskerRight η.hom Q⟩ hΓ hx)
    (generatedComparison_baseTerm F P η Q α hΓ hx)
  rw [normalizedEndpointIso] at hh
  exact hh

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
