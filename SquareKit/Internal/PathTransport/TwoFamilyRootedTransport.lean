import SquareKit.Internal.PathTransport.TwoFamilyRootedReflexivity
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)]
private theorem totalCast_familyCast {A : Type*} [Bicategory A] [Strict A]
    {E G : Family A} (e : E = G) : totalCast e = familyCast e := by cases e; rfl
theorem pathReindex_familySubstitution {Δ : Type*} [Bicategory Δ] [Strict Δ]
    (σ : StrictPseudofunctor Δ Γ) :
    pathReindex F σ = familySubstitution (openIdHigher F) (endpointReindex F σ) (openIdHigher_reindex F σ) := by
  unfold pathReindex reindexOfData
  rw [strictFunctorOfEqualData_eq]
  unfold reindexFromEqualFamily familySubstitution
  rw [totalCast_familyCast]

theorem rootedPathEmbedding_direct (x : Section F) :
    (familyCast (rootedPathFamily_direct F x)).comp (reindexHigher (openIdHigher F) (rootedEndpoint F x)) =
      rootedPathEmbedding F x := by
  symm
  unfold rootedPathEmbedding closedPathEmbedding
  rw [pathReindex_familySubstitution, ← familySubstitution_reindex, familySubstitution_comp]
  rfl

noncomputable def rootedReflexivity (x : Section F) : StrictPseudofunctor Γ (Total (rootedPathFamily F x)) :=
  (rootedReflexivityDirect F x).comp (familyCast (rootedPathFamily_direct F x).symm)
noncomputable def rootedRetraction (x : Section F) : StrictPseudofunctor (Total (rootedPathFamily F x)) Γ :=
  (projectionHigher (rootedPathFamily F x)).comp (projectionHigher F)

theorem rootedReflexivity_projection (x : Section F) :
    (rootedReflexivity F x).comp (projectionHigher (rootedPathFamily F x)) = x.lift := by
  unfold rootedReflexivity
  rw [strictFunctor_comp_assoc, familyCast_projection, rootedReflexivityDirect_projection]
theorem rootedReflexivity_retraction (x : Section F) :
    (rootedReflexivity F x).comp (rootedRetraction F x) = StrictPseudofunctor.id Γ := by
  unfold rootedRetraction
  rw [← strictFunctor_comp_assoc, rootedReflexivity_projection]
  exact x.over
end SquareKit.Internal.PathTransport.TwoFamily
