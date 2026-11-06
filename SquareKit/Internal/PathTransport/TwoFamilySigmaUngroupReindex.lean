import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupReindex
/-! Pair construction commutes with substitution by the constructed regrouping inverse equations. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
theorem sigmaUngroup_reindex :
    (reindexHigher B (reindexHigher F σ)).comp (sigmaUngroup F B) =
      (sigmaUngroup (reindex σ F) (reindex (reindexHigher F σ) B)).comp
        ((familyCast (sigmaFamily_reindex F σ B)).comp (reindexHigher (sigmaFamily F B) σ)) := by
  let A := reindex σ F
  let B' := reindex (reindexHigher F σ) B
  let T := reindexHigher B (reindexHigher F σ)
  calc
    T.comp (sigmaUngroup F B) =
        ((sigmaUngroup A B').comp (sigmaRegroup A B')).comp (T.comp (sigmaUngroup F B)) := by
      rw [sigmaUngroup_regroup, strictFunctor_id_comp]
    _ = (sigmaUngroup A B').comp (((sigmaRegroup A B').comp T).comp (sigmaUngroup F B)) := by
      simp only [strictFunctor_comp_assoc]
    _ = (sigmaUngroup A B').comp (((familyCast (sigmaFamily_reindex F σ B)).comp
        ((reindexHigher (sigmaFamily F B) σ).comp (sigmaRegroup F B))).comp (sigmaUngroup F B)) := by
      rw [sigmaRegroup_reindex]
    _ = _ := by
      simp only [strictFunctor_comp_assoc, sigmaRegroup_ungroup, strictFunctor_comp_id]
      rfl
end SquareKit.Internal.PathTransport.TwoFamily
