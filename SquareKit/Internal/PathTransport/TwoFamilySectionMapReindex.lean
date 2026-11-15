import SquareKit.Internal.PathTransport.TwoStrongPrecomp
import SquareKit.Internal.PathTransport.TwoFamilySectionReindexLift
import SquareKit.Internal.PathTransport.TwoFunctorData
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w u' v' w' uΔ vΔ wΔ
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable {F G : Family.{u,v,w,u',v',w'} Γ}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
variable (σ : StrictPseudofunctor Δ Γ)
/-- Reindexing a coherent family map commutes with the actual total substitutions. -/
theorem StrongMap.reindex_square :
    (StrongMap.toHigher (strongPrecomp η σ)).comp (reindexHigher G σ) =
      (reindexHigher F σ).comp (StrongMap.toHigher η) :=
  strictFunctorData_ext rfl
/-- Coherent transport of a section commutes with arbitrary context substitution. -/
theorem Section.map_reindex (s : Section F) :
    (s.map η).reindex G σ = (s.reindex F σ).map (strongPrecomp η σ) := by
  apply Section.reindex_lift_injective G σ
  calc
    ((s.map η).reindex G σ).lift.comp (reindexHigher G σ) = σ.comp (s.map η).lift :=
      (s.map η).reindex_lift G σ
    _ = (σ.comp s.lift).comp (StrongMap.toHigher η) := strictFunctorData_ext rfl
    _ = ((s.reindex F σ).lift.comp (reindexHigher F σ)).comp (StrongMap.toHigher η) :=
      congrArg (fun H => H.comp (StrongMap.toHigher η)) (s.reindex_lift F σ).symm
    _ = (s.reindex F σ).lift.comp ((reindexHigher F σ).comp (StrongMap.toHigher η)) :=
      strictFunctorData_ext rfl
    _ = (s.reindex F σ).lift.comp
        ((StrongMap.toHigher (strongPrecomp η σ)).comp (reindexHigher G σ)) :=
      congrArg (fun H => (s.reindex F σ).lift.comp H) (StrongMap.reindex_square η σ).symm
    _ = ((s.reindex F σ).map (strongPrecomp η σ)).lift.comp (reindexHigher G σ) :=
      strictFunctorData_ext rfl
end SquareKit.Internal.PathTransport.TwoFamily
