import SquareKit.Internal.PathTransport.TwoFamilyRootedInclusionSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyPathContractionReindex
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 150000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)]
variable (x : Section F)
variable {Δ : Type*} [Bicategory Δ] [Strict Δ] [IsLocallyGroupoid Δ]
variable (σ : StrictPseudofunctor Δ Γ)
theorem rootedSubstitution_retract :
    ((rootedRetraction (reindex σ F) (x.reindex F σ)).comp
      (rootedReflexivity (reindex σ F) (x.reindex F σ))).comp (rootedSubstitution F x σ) =
      (rootedSubstitution F x σ).comp ((rootedRetraction F x).comp (rootedReflexivity F x)) := by
  rw [strictFunctor_comp_assoc, rootedSubstitution_reflexivity, ← strictFunctor_comp_assoc,
    ← rootedSubstitution_retraction, strictFunctor_comp_assoc]

theorem rootedContraction_reindex_mapped :
    HEq (strongPostcomp (strongPostcomp (rootedContraction (reindex σ F) (x.reindex F σ))
        (rootedSubstitution F x σ)) (rootedPathEmbedding F x))
      (strongPostcomp (strongPrecomp (rootedContraction F x) (rootedSubstitution F x σ)) (rootedPathEmbedding F x)) := by
  let F' := reindex σ F
  let x' := x.reindex F σ
  let S := rootedSubstitution F x σ
  let H := rootedPathEmbedding F x
  let H' := rootedPathEmbedding F' x'
  let P := pathReindex F σ
  have h1 := strongPostcomp_comp (rootedContraction F' x') S H
  have h2 := strongPostcomp_functor_heq (rootedContraction F' x') (rootedSubstitution_embedding F x σ)
  have h3 := (strongPostcomp_comp (rootedContraction F' x') H' P).symm
  have h4 := strongPostcomp_heq (rootedContraction_embedding_source F' x')
    (rootedContraction_embedding_target F' x') _ _ (rootedContraction_embedding F' x') P
  have h5 := strongPostcomp_precomp (pathContraction F') H' P
  have h6 := strongPrecomp_heq (pathReindex_retract F σ)
    ((strictFunctor_id_comp P).trans (strictFunctor_comp_id P).symm)
    _ _ (pathContraction_reindex F σ) H'
  have h7 := strongPrecomp_comp (pathContraction F) P H'
  have h8 := strongPrecomp_functor_heq (pathContraction F) (rootedSubstitution_embedding F x σ).symm
  have h9 := (strongPrecomp_comp (pathContraction F) H S).symm
  have h10 := strongPrecomp_heq (rootedContraction_embedding_source F x).symm
    (rootedContraction_embedding_target F x).symm _ _ (rootedContraction_embedding F x).symm S
  have h11 := (strongPostcomp_precomp (rootedContraction F x) S H).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans (h10.trans h11)))))))))

theorem rootedContraction_reindex :
    HEq (strongPostcomp (rootedContraction (reindex σ F) (x.reindex F σ)) (rootedSubstitution F x σ))
      (strongPrecomp (rootedContraction F x) (rootedSubstitution F x σ)) :=
  strongPostcomp_heq_reflect (rootedPathEmbedding F x)
    (fun {_ _} => rootedPathEmbedding_map_injective F x)
    (fun {_ _ _ _} => rootedPathEmbedding_cell_injective F x)
    (rootedSubstitution_retract F x σ)
    ((strictFunctor_id_comp _).trans (strictFunctor_comp_id _).symm)
    _ _ (rootedContraction_reindex_mapped F x σ)
end SquareKit.Internal.PathTransport.TwoFamily
