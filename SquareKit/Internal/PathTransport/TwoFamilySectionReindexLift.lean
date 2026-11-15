import SquareKit.Internal.PathTransport.TwoFamilySectionLaws
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w u' v' w' uΔ vΔ wΔ
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable (F : Family.{u,v,w,u',v',w'} Γ)
private theorem cast_reindex_lift {σ τ : StrictPseudofunctor Δ Γ} (e : σ = τ)
    (s : Section (TwoFamily.reindex σ F)) :
    (Section.cast (congrArg (fun H => reindex H F) e) s).lift.comp (reindexHigher F τ) =
      s.lift.comp (reindexHigher F σ) := by
  cases e
  rfl
/-- The substituted section lifts exactly the substituted original lift in every dimension. -/
theorem Section.reindex_lift (s : Section F) (σ : StrictPseudofunctor Δ Γ) :
    (s.reindex F σ).lift.comp (reindexHigher F σ) = σ.comp s.lift := by
  exact (cast_reindex_lift F (s.reindex_base F σ) (sectionOfLift F (σ.comp s.lift))).trans
    (factorHigher_reindex F (σ.comp s.lift))
/-- For sections of a fixed pullback, the lifted substitution retains all fiber data. -/
theorem Section.reindex_lift_injective (σ : StrictPseudofunctor Δ Γ)
    (s t : Section (TwoFamily.reindex σ F))
    (h : s.lift.comp (reindexHigher F σ) = t.lift.comp (reindexHigher F σ)) : s = t := by
  apply Section.ext_fiber
  · intro x
    exact congr_arg_heq (fun H => (H.obj x).fiber) h
  · intro x y p
    exact congr_arg_heq (fun H => (H.map p).fiber) h
  · intro x y p q α
    exact congr_arg_heq (fun H => (H.map₂ α).fiber) h
end SquareKit.Internal.PathTransport.TwoFamily
