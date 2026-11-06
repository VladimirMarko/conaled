import SquareKit.Internal.PathTransport.TwoFamilyRootedPath
/-! The fixed-endpoint path family is an actual pullback of the open identity
family along an endpoint map with identity second projection. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
noncomputable def rootedEndpoint (x : Section F) :
    StrictPseudofunctor (Total F) (Total (endpointFamily F)) :=
  (endpointPair (reindex (projectionHigher F) F)
    (x.reindex F (projectionHigher F)) (variableSection F)).lift.comp
      (endpointReindex F (projectionHigher F))

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
theorem rootedEndpoint_first (x : Section F) :
    (rootedEndpoint F x).comp (endpointProjection F true) = (projectionHigher F).comp x.lift := by
  unfold rootedEndpoint
  rw [strictFunctor_comp_assoc, endpointReindex_projection, ← strictFunctor_comp_assoc,
    endpointPair_first, Section.reindex_lift]

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
theorem rootedEndpoint_second (x : Section F) :
    (rootedEndpoint F x).comp (endpointProjection F false) = StrictPseudofunctor.id (Total F) := by
  unfold rootedEndpoint
  rw [strictFunctor_comp_assoc, endpointReindex_projection, ← strictFunctor_comp_assoc,
    endpointPair_second, variableLift_recombined]

theorem rootedPathFamily_direct (x : Section F) :
    rootedPathFamily F x = reindex (rootedEndpoint F x) (openIdHigher F) := by
  change (endpointPair (reindex (projectionHigher F) F)
    (x.reindex F (projectionHigher F)) (variableSection F)).lift.comp
      (openIdHigher (reindex (projectionHigher F) F)) = _
  have h := congrArg
    (fun H => (endpointPair (reindex (projectionHigher F) F)
      (x.reindex F (projectionHigher F)) (variableSection F)).lift.comp H)
    (openIdHigher_reindex F (projectionHigher F))
  exact h.trans (strictFunctor_comp_assoc _ _ _).symm
end SquareKit.Internal.PathTransport.TwoFamily
