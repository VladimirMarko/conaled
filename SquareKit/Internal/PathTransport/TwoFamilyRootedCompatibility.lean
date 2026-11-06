import SquareKit.Internal.PathTransport.TwoFamilyRootedMappedContraction
import SquareKit.Internal.PathTransport.TwoFamilyEndpointStrong
import SquareKit.Internal.PathTransport.TwoFamilyContractionNormalization
import SquareKit.Internal.PathTransport.TwoFamilyReindexStrong
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)]
variable (x : Section F)
private theorem strongId_heq {A B : Type*} [Bicategory A] [Bicategory B]
    {H K : StrictPseudofunctor A B} (e : H = K) :
    HEq (Pseudofunctor.StrongTrans.id H.toPseudofunctor) (Pseudofunctor.StrongTrans.id K.toPseudofunctor) := by cases e; rfl

theorem pathContraction_first_source : (contractionRetract F).comp (pathFirst F) = pathFirst F := by
  change ((pathFirst F).comp (pathReflexivity F)).comp (pathFirst F) = _
  rw [strictFunctor_comp_assoc, pathReflexivity_first, strictFunctor_comp_id]

theorem rootedMappedFirst_source :
    ((rootedDirectRetract F x).comp (rootedDirectEmbedding F x)).comp (pathFirst F) =
      (rootedDirectEmbedding F x).comp (pathFirst F) := by
  rw [← rootedContractionMapped_source, strictFunctor_comp_assoc, pathContraction_first_source]
theorem rootedMappedFirst_target :
    ((StrictPseudofunctor.id (Total (rootedDirectFamily F x))).comp (rootedDirectEmbedding F x)).comp (pathFirst F) =
      (rootedDirectEmbedding F x).comp (pathFirst F) := by
  rw [strictFunctor_id_comp]

theorem rootedContractionMapped_first :
    HEq (strongPostcomp (rootedContractionMapped F x) (pathFirst F))
      (Pseudofunctor.StrongTrans.id ((rootedDirectEmbedding F x).comp (pathFirst F)).toPseudofunctor) := by
  have h1 := strongPostcomp_heq (rootedContractionMapped_source F x).symm
    (rootedContractionMapped_target F x).symm _ _ (rootedContractionMapped_heq F x) (pathFirst F)
  have h2 := strongPostcomp_precomp (pathContraction F) (rootedDirectEmbedding F x) (pathFirst F)
  have h3 := strongPrecomp_heq (pathContraction_first_source F)
    (StrictTwoTransformation.functor_id_comp (pathFirst F)) _ _ (pathContraction_first F) (rootedDirectEmbedding F x)
  have h4 : strongPrecomp (Pseudofunctor.StrongTrans.id (pathFirst F).toPseudofunctor) (rootedDirectEmbedding F x) =
      Pseudofunctor.StrongTrans.id ((rootedDirectEmbedding F x).comp (pathFirst F)).toPseudofunctor := rfl
  exact h1.trans (h2.trans (h3.trans (heq_of_eq h4)))

theorem pathEndpoints_same_base :
    (pathSecond F).comp (projectionHigher F) = (pathFirst F).comp (projectionHigher F) := by
  unfold pathSecond pathFirst
  rw [strictFunctor_comp_assoc, strictFunctor_comp_assoc,
    StrongMap.toHigher_projection, StrongMap.toHigher_projection]

theorem rootedMappedFirst_section :
    ((rootedDirectEmbedding F x).comp (pathFirst F)).comp ((projectionHigher F).comp x.lift) =
      (rootedDirectEmbedding F x).comp (pathFirst F) := by
  rw [rootedDirectEmbedding_first, strictFunctor_comp_assoc, ← strictFunctor_comp_assoc x.lift,
    x.over, strictFunctor_id_comp]

theorem rootedBaseContraction_first :
    HEq (strongPostcomp (rootedBaseContraction F x) ((projectionHigher F).comp x.lift))
      (strongPostcomp (rootedContractionMapped F x) (pathFirst F)) := by
  let M := (projectionHigher F).comp x.lift
  let K := (rootedDirectEmbedding F x).comp (pathFirst F)
  have h1 := strongPostcomp_heq (rootedBaseContraction_source F x).symm
    (rootedBaseContraction_target F x).symm _ _ (rootedBaseContraction_heq F x) M
  have h2 := strongPostcomp_comp (rootedContractionMapped F x) (pathSecond F) M
  have e : (pathSecond F).comp M = (pathFirst F).comp M := by
    unfold M
    rw [← strictFunctor_comp_assoc, pathEndpoints_same_base, strictFunctor_comp_assoc]
  have h3 := strongPostcomp_functor_heq (rootedContractionMapped F x) e
  have h4 := (strongPostcomp_comp (rootedContractionMapped F x) (pathFirst F) M).symm
  have h5 := strongPostcomp_heq (rootedMappedFirst_source F x) (rootedMappedFirst_target F x)
    _ _ (rootedContractionMapped_first F x) M
  have h6 := heq_of_eq (strongPostcomp_id K M)
  have h7 := strongId_heq (rootedMappedFirst_section F x)
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (rootedContractionMapped_first F x).symm))))))

private theorem strongPostcomp_right_id {A B : Type*} [Bicategory A] [Bicategory B] [Strict A] [Strict B]
    {F G : StrictPseudofunctor A B} (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) :
    HEq (strongPostcomp θ (StrictPseudofunctor.id B)) θ := by
  apply strongTrans_hext (congrArg (fun H => H.toPseudofunctor) (StrictTwoTransformation.functor_comp_id F))
    (congrArg (fun H => H.toPseudofunctor) (StrictTwoTransformation.functor_comp_id G))
  · intro a; rfl
  · intro a b p
    exact strongPostcomp_naturality_heq θ (StrictPseudofunctor.id B) p

theorem rootedContraction_compatibility :
    HEq (strongPostcomp (rootedBaseContraction F x) (rootedEndpoint F x))
      (strongPostcomp (rootedContractionMapped F x) (projectionHigher (openIdHigher F))) := by
  apply endpointStrong_hext F
    (reindexStrongBoundary (openIdHigher F) (rootedEndpoint F x) (rootedDirectRetract F x))
    (reindexStrongBoundary (openIdHigher F) (rootedEndpoint F x) (StrictPseudofunctor.id _))
  · have h1 := strongPostcomp_comp (rootedBaseContraction F x) (rootedEndpoint F x) (endpointProjection F true)
    have h2 := strongPostcomp_functor_heq (rootedBaseContraction F x) (rootedEndpoint_first F x)
    have h3 := rootedBaseContraction_first F x
    have h4 := (strongPostcomp_functor_heq (rootedContractionMapped F x) (pathFirst_normal F).symm).symm
    have h5 := (strongPostcomp_comp (rootedContractionMapped F x) (projectionHigher (openIdHigher F)) (endpointProjection F true)).symm
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  · have h1 := strongPostcomp_comp (rootedBaseContraction F x) (rootedEndpoint F x) (endpointProjection F false)
    have h2 := strongPostcomp_functor_heq (rootedBaseContraction F x) (rootedEndpoint_second F x)
    have h3 := strongPostcomp_right_id (rootedBaseContraction F x)
    have h4 := rootedBaseContraction_heq F x
    have h5 := (strongPostcomp_functor_heq (rootedContractionMapped F x) (pathSecond_normal F).symm).symm
    have h6 := (strongPostcomp_comp (rootedContractionMapped F x) (projectionHigher (openIdHigher F)) (endpointProjection F false)).symm
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
end SquareKit.Internal.PathTransport.TwoFamily
