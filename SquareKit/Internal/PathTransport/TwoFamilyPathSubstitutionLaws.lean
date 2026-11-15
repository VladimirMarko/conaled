import SquareKit.Internal.PathTransport.TwoFamilyPathSubstitution
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Reflexivity is stable under the constructed substitution of higher path contexts. -/
theorem pathReindex_reflexivity :
    (pathReflexivity (reindex σ F)).comp (pathReindex F σ) =
      (reindexHigher F σ).comp (pathReflexivity F) := by
  apply strictFunctorData_ext
  apply prelaxData_ext
  · intro x
    rfl
  · intro x y p
    rfl
  · intro x y p q α
    apply heq_of_eq
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
    · refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
      · rfl
      · apply eq_of_heq
        refine HEq.trans ?_ (comp_eqToHom_heq _ _).symm
        apply heq_of_eq
        apply Prod.ext
        · apply eq_of_heq
          exact (diagonal_cell_fst_heq (reindex σ F) α).trans
            (diagonal_cell_fst_heq F ((reindexHigher F σ).map₂ α)).symm
        · apply eq_of_heq
          exact (diagonal_cell_snd_heq (reindex σ F) α).trans
            (diagonal_cell_snd_heq F ((reindexHigher F σ).map₂ α)).symm
    · exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Substitution commutes with selecting the first dependent endpoint. -/
theorem pathReindex_first :
    (pathReindex F σ).comp (pathFirst F) =
      (pathFirst (reindex σ F)).comp (reindexHigher F σ) := by
  apply strictFunctorData_ext
  apply prelaxData_ext
  · intro x
    rfl
  · intro x y p
    apply heq_of_eq
    apply Pseudofunctor.CoGrothendieck.ext
    · rfl
    · exact heq_of_eq ((pathFirst_map_fiber F ((pathReindex F σ).map p)).trans
        (pathFirst_map_fiber (reindex σ F) p).symm)
  · intro x y p q α
    apply heq_of_eq
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
    · rfl
    · apply eq_of_heq
      exact HEq.trans
        ((pathFirst_cell_fiber_heq F ((pathReindex F σ).map₂ α)).trans
          (pathFirst_cell_fiber_heq (reindex σ F) α).symm)
        (comp_eqToHom_heq _ _).symm
end SquareKit.Internal.PathTransport.TwoFamily
