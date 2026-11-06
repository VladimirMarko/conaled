import SquareKit.Internal.PathTransport.TwoFamilyPathJSubstitution
import SquareKit.Internal.PathTransport.TwoFamilySectionHEq
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ uE vE wE
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
variable (E : Family.{_,_,_,uE,vE,wE} (PathContext F))
/-- The supplied reflexive branch pulled back along the first endpoint, as used by J. -/
noncomputable def pathJInput (d : Section (reindex (pathReflexivity F) E)) :
    Section (reindex (contractionRetract F) E) :=
  Section.cast (reindex_comp E (pathReflexivity F) (pathFirst F))
    (d.reindex (reindex (pathReflexivity F) E) (pathFirst F))
variable (σ : StrictPseudofunctor Δ Γ)
/-- Pulling the selected branch back for J commutes with context substitution. -/
theorem pathJInput_reindex (d : Section (reindex (pathReflexivity F) E)) :
    HEq (pathJInput (reindex σ F) (reindex (pathReindex F σ) E) (pathBranchReindex F σ E d))
      ((pathJInput F E d).reindex _ (pathReindex F σ)) := by
  have h1 := Section.cast_heq
    (reindex_comp (reindex (pathReindex F σ) E) (pathReflexivity (reindex σ F)) (pathFirst (reindex σ F)))
    ((pathBranchReindex F σ E d).reindex _ (pathFirst (reindex σ F)))
  have h2 := Section.reindex_heq (pathMotive_reindex F σ E).symm
    (pathBranchReindex F σ E d) (d.reindex _ (reindexHigher F σ))
    (Section.cast_heq (pathMotive_reindex F σ E) (d.reindex _ (reindexHigher F σ)))
    (pathFirst (reindex σ F))
  have h3 := d.reindex_comp_heq (reindexHigher F σ) (pathFirst (reindex σ F))
  have h4 := d.reindex_functor_heq (pathReindex_first F σ).symm
  have h5 := (d.reindex_comp_heq (pathFirst F) (pathReindex F σ)).symm
  have h6 := Section.reindex_heq (reindex_comp E (pathReflexivity F) (pathFirst F))
    (d.reindex _ (pathFirst F)) (pathJInput F E d)
    (Section.cast_heq (reindex_comp E (pathReflexivity F) (pathFirst F))
      (d.reindex _ (pathFirst F))).symm (pathReindex F σ)
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut terms := #[]
    let mut types := #[]
    for name in [`h1, `h2, `h3, `h4, `h5, `h6] do
      let d ← Lean.Meta.getLocalDeclFromUserName name
      let t ← Lean.instantiateMVars d.type
      unless t.isAppOfArity ``HEq 4 do throwError "Expected an HEq proof"
      terms := terms.push d.toExpr
      types := types.push t
    let final := types[5]!.getAppArgs
    let mut proof := terms[5]!
    for i in [0:5] do
      let j := 4 - i
      let a := types[j]!.getAppArgs
      proof := Lean.mkAppN (Lean.mkConst ``HEq.trans types[j]!.getAppFn.constLevels!)
        #[a[0]!, a[2]!, final[2]!, a[1]!, a[3]!, final[3]!, terms[j]!, proof]
    Lean.Elab.Tactic.closeMainGoal `exact proof
end SquareKit.Internal.PathTransport.TwoFamily
