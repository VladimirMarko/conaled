import SquareKit.Internal.PathTransport.TwoFamilyRootedContraction
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)]
variable (x : Section F)
theorem rootedEmbedding_cancel :
    (familyCast (rootedPathFamily_direct F x).symm).comp (rootedPathEmbedding F x) = rootedDirectEmbedding F x := by
  rw [← rootedPathEmbedding_direct, ← strictFunctor_comp_assoc, familyCast_comp]
  exact strictFunctor_id_comp _
theorem rootedReflexivity_embedding :
    (rootedReflexivity F x).comp (rootedPathEmbedding F x) = x.lift.comp (pathReflexivity F) := by
  unfold rootedReflexivity
  rw [strictFunctor_comp_assoc, rootedEmbedding_cancel, rootedReflexivityDirect_embedding]
theorem rootedContraction_embedding :
    HEq (strongPostcomp (rootedContraction F x) (rootedPathEmbedding F x))
      (strongPrecomp (pathContraction F) (rootedPathEmbedding F x)) := by
  let e := rootedPathFamily_direct F x
  have h1 := strongPostcomp_heq (rootedContraction_source F x).symm (rootedContraction_target F x).symm
    _ _ (rootedContraction_heq F x) (rootedPathEmbedding F x)
  have h2 := strongPostcomp_comp (strongPrecomp (rootedContractionDirect F x) (familyCast e))
    (familyCast e.symm) (rootedPathEmbedding F x)
  have h3 := strongPostcomp_functor_heq (strongPrecomp (rootedContractionDirect F x) (familyCast e)) (rootedEmbedding_cancel F x)
  have h4 := strongPostcomp_precomp (rootedContractionDirect F x) (familyCast e) (rootedDirectEmbedding F x)
  have h5 := heq_of_eq (congrArg (fun θ => strongPrecomp θ (familyCast e)) (rootedContractionDirect_embedding F x))
  have h6 := strongPrecomp_heq (rootedContractionMapped_source F x).symm
    (rootedContractionMapped_target F x).symm _ _ (rootedContractionMapped_heq F x) (familyCast e)
  have h7 := strongPrecomp_comp (pathContraction F) (rootedDirectEmbedding F x) (familyCast e)
  have h8 := strongPrecomp_functor_heq (pathContraction F) (rootedPathEmbedding_direct F x)
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8))))))
end SquareKit.Internal.PathTransport.TwoFamily
