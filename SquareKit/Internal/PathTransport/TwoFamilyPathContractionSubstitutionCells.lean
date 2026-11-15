import SquareKit.Internal.PathTransport.TwoFamilyPathContractionSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyPathSubstitutionLaws
import SquareKit.Internal.PathTransport.TwoFunctorComposition
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
/-- Retraction to reflexivity commutes with the constructed path substitution. -/
theorem pathReindex_retract :
    (contractionRetract (reindex σ F)).comp (pathReindex F σ) =
      (pathReindex F σ).comp (contractionRetract F) := by
  calc
    (contractionRetract (reindex σ F)).comp (pathReindex F σ) =
        (pathFirst (reindex σ F)).comp ((pathReflexivity (reindex σ F)).comp (pathReindex F σ)) :=
      strictFunctor_comp_assoc _ _ _
    _ = (pathFirst (reindex σ F)).comp ((reindexHigher F σ).comp (pathReflexivity F)) :=
      congrArg (fun H => (pathFirst (reindex σ F)).comp H) (pathReindex_reflexivity F σ)
    _ = ((pathFirst (reindex σ F)).comp (reindexHigher F σ)).comp (pathReflexivity F) :=
      (strictFunctor_comp_assoc _ _ _).symm
    _ = ((pathReindex F σ).comp (pathFirst F)).comp (pathReflexivity F) :=
      congrArg (fun H => H.comp (pathReflexivity F)) (pathReindex_first F σ).symm
    _ = (pathReindex F σ).comp (contractionRetract F) := strictFunctor_comp_assoc _ _ _
/-- The left boundary of the contraction comparison is preserved by substitution. -/
theorem contractionLeft_reindex {x y : PathContext (reindex σ F)} (p : x ⟶ y) :
    (pathReindex F σ).map ((contractionRetract (reindex σ F)).map p ≫
      contractionComponent (reindex σ F) y) =
    (contractionRetract F).map ((pathReindex F σ).map p) ≫
      contractionComponent F ((pathReindex F σ).obj y) := by
  have h := congr_arg_heq (fun H => H.map p) (pathReindex_retract F σ)
  exact ((pathReindex F σ).map_comp _ _).trans
    (congrArg₂ (fun a b => a ≫ b) (eq_of_heq h) (contractionComponent_reindex F σ y))
/-- The right boundary of the contraction comparison is preserved by substitution. -/
theorem contractionRight_reindex {x y : PathContext (reindex σ F)} (p : x ⟶ y) :
    (pathReindex F σ).map (contractionComponent (reindex σ F) x ≫ p) =
      contractionComponent F ((pathReindex F σ).obj x) ≫ (pathReindex F σ).map p := by
  exact ((pathReindex F σ).map_comp _ _).trans
    (congrArg (fun a => a ≫ (pathReindex F σ).map p) (contractionComponent_reindex F σ x))
end SquareKit.Internal.PathTransport.TwoFamily
