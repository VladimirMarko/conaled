import SquareKit.Internal.PathTransport.TwoFamilyPathContractionSubstitutionNaturality
import SquareKit.Internal.PathTransport.TwoStrongCongr
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
variable [IsLocallyGroupoid Γ] [IsLocallyGroupoid Δ]
/-- The full constructed coherent path contraction is stable under context substitution. -/
theorem pathContraction_reindex :
    HEq (strongPostcomp (pathContraction (reindex σ F)) (pathReindex F σ))
      (strongPrecomp (pathContraction F) (pathReindex F σ)) := by
  apply strongTrans_hext
    (congrArg (fun H : StrictPseudofunctor (PathContext (reindex σ F)) (PathContext F) =>
      H.toPseudofunctor) (pathReindex_retract F σ))
    (congrArg (fun H : StrictPseudofunctor (PathContext (reindex σ F)) (PathContext F) =>
      H.toPseudofunctor) ((strictFunctor_id_comp (pathReindex F σ)).trans
        (strictFunctor_comp_id (pathReindex F σ)).symm))
  · intro x
    exact heq_of_eq (contractionComponent_reindex F σ x)
  · intro x y p
    have h1 := strongPostcomp_naturality_heq (pathContraction (reindex σ F)) (pathReindex F σ) p
    have h2 := contractionNaturalityCell_reindex F σ p
    run_tac Lean.Elab.Tactic.withMainContext do
      let h1 ← Lean.Meta.getLocalDeclFromUserName `h1
      let h2 ← Lean.Meta.getLocalDeclFromUserName `h2
      let t1 ← Lean.instantiateMVars h1.type
      let t2 ← Lean.instantiateMVars h2.type
      let a := t1.getAppArgs
      let b := t2.getAppArgs
      let proof := Lean.mkAppN (Lean.mkConst ``HEq.trans t1.getAppFn.constLevels!)
        #[a[0]!, a[2]!, b[2]!, a[1]!, a[3]!, b[3]!, h1.toExpr, h2.toExpr]
      Lean.Elab.Tactic.closeMainGoal `exact proof
end SquareKit.Internal.PathTransport.TwoFamily
