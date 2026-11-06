import SquareKit.Internal.PathTransport.TwoFamilyClosedIdentity
import SquareKit.Internal.PathTransport.TwoFamilySectionReindexLift
/-! Substitution of closed identity families through both endpoint projections. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable {Δ : Type*} [Bicategory Δ] [Strict Δ] (σ : StrictPseudofunctor Δ Γ)
def endpointReindexData : PrelaxFunctorStruct
    (Total (endpointFamily (reindex σ F))) (Total (endpointFamily F)) where
  obj x := ⟨σ.obj x.base,x.fiber⟩
  map p := ⟨σ.map p.base,p.fiber⟩
  map₂ α := ⟨σ.map₂ α.base,α.fiber⟩

def endpointReindex := strictFunctorOfJointReflection (endpointReindexData F σ)
  (endpointProjection F true) (endpointProjection F false)
  ((endpointProjection (reindex σ F) true).comp (reindexHigher F σ))
  ((endpointProjection (reindex σ F) false).comp (reindexHigher F σ))
  rfl rfl (endpoint_hom_ext F) (endpoint_cell_ext F)

theorem endpointReindex_projection (side : Bool) :
    (endpointReindex F σ).comp (endpointProjection F side) =
      (endpointProjection (reindex σ F) side).comp (reindexHigher F σ) := by
  cases side <;> exact strictFunctorData_ext rfl

variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
theorem openIdHigher_reindex : openIdHigher (reindex σ F) =
    (endpointReindex F σ).comp (openIdHigher F) := by
  exact StrictTwoTransformation.functor_ext rfl

private theorem higher_comp_assoc {A B C D : Type*} [Bicategory A] [Bicategory B]
    [Bicategory C] [Bicategory D] (H : StrictPseudofunctor A B)
    (K : StrictPseudofunctor B C) (L : StrictPseudofunctor C D) :
    (H.comp K).comp L = H.comp (K.comp L) := StrictTwoTransformation.functor_ext rfl

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
theorem endpointPair_lift_reindex (s t : Section F) :
    (endpointPair (reindex σ F) (s.reindex F σ) (t.reindex F σ)).lift.comp
      (endpointReindex F σ) = σ.comp (endpointPair F s t).lift := by
  apply endpoint_functor_ext F
  · rw [higher_comp_assoc, endpointReindex_projection, ← higher_comp_assoc,
      endpointPair_first, Section.reindex_lift, higher_comp_assoc, endpointPair_first]
  · rw [higher_comp_assoc, endpointReindex_projection, ← higher_comp_assoc,
      endpointPair_second, Section.reindex_lift, higher_comp_assoc, endpointPair_second]

theorem closedId_reindex (s t : Section F) :
    reindex σ (closedId F s t) = closedId (reindex σ F) (s.reindex F σ) (t.reindex F σ) := by
  change σ.comp ((endpointPair F s t).lift.comp (openIdHigher F)) =
    (endpointPair (reindex σ F) (s.reindex F σ) (t.reindex F σ)).lift.comp (openIdHigher (reindex σ F))
  calc
    σ.comp ((endpointPair F s t).lift.comp (openIdHigher F)) =
        (σ.comp (endpointPair F s t).lift).comp (openIdHigher F) :=
      (higher_comp_assoc _ _ _).symm
    _ = ((endpointPair (reindex σ F) (s.reindex F σ) (t.reindex F σ)).lift.comp
        (endpointReindex F σ)).comp (openIdHigher F) :=
      congrArg (fun H => H.comp (openIdHigher F)) (endpointPair_lift_reindex F σ s t).symm
    _ = (endpointPair (reindex σ F) (s.reindex F σ) (t.reindex F σ)).lift.comp
        ((endpointReindex F σ).comp (openIdHigher F)) := higher_comp_assoc _ _ _
    _ = _ := by rw [← openIdHigher_reindex]
end SquareKit.Internal.PathTransport.TwoFamily
