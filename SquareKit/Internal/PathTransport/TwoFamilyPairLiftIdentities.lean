import SquareKit.Internal.PathTransport.TwoFamilyComprehension
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
theorem sectionOfLift_pairLift_heq (σ : StrictPseudofunctor Δ Γ)
    (s : Section (reindex σ F)) : HEq (sectionOfLift F (pairLift F σ s)) s := by
  apply Section.hext_family (congrArg (fun k => reindex k F) (pairLift_projection F σ s))
  · intro x; rfl
  · intro x y p; rfl
  · intro x y p q α; rfl

theorem pairLift_cast_base {σ τ : StrictPseudofunctor Δ Γ} (e : σ = τ)
    (s : Section (reindex σ F)) :
    pairLift F τ (Section.cast (congrArg (fun k => reindex k F) e) s) = pairLift F σ s := by
  cases e
  rfl
end SquareKit.Internal.PathTransport.TwoFamily
