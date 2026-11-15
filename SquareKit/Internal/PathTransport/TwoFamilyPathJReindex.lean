import SquareKit.Internal.PathTransport.TwoFamilyPathJMotiveSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyPathJInputSubstitution
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ uE vE wE
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
variable [IsLocallyGroupoid Γ] [IsLocallyGroupoid Δ]
variable (E : Family.{_,_,_,uE,vE,wE} (PathContext F))
/-- Arbitrary-motive J commutes with context substitution as a whole higher section. -/
theorem pathJ_reindex (d : Section (reindex (pathReflexivity F) E)) :
    (pathJ F E d).reindex E (pathReindex F σ) =
      pathJ (reindex σ F) (reindex (pathReindex F σ) E) (pathBranchReindex F σ E d) := by
  let E' := reindex (pathReindex F σ) E
  let s := pathJInput F E d
  let s' := pathJInput (reindex σ F) E' (pathBranchReindex F σ E d)
  let η := strongPostcomp (pathContraction F) E
  let η' := strongPostcomp (pathContraction (reindex σ F)) E'
  have h1 := Section.cast_heq (reindex_id E') (s'.map η')
  have h2 := Section.map_heq (pathJSource_reindex F σ E) (pathJTarget_reindex F σ E)
    η' (strongPrecomp η (pathReindex F σ)) (pathJMotive_reindex F σ E)
    s' (s.reindex _ (pathReindex F σ)) (pathJInput_reindex F E σ d)
  have h3 := (heq_of_eq (Section.map_reindex η (pathReindex F σ) s)).symm
  have h4 := Section.reindex_heq (reindex_id E) (s.map η) (pathJ F E d)
    (Section.cast_heq (reindex_id E) (s.map η)).symm (pathReindex F σ)
  apply Eq.symm
  apply eq_of_heq
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut terms := #[]
    let mut types := #[]
    for name in [`h1, `h2, `h3, `h4] do
      let d ← Lean.Meta.getLocalDeclFromUserName name
      let t ← Lean.instantiateMVars d.type
      unless t.isAppOfArity ``HEq 4 do throwError "Expected an HEq proof"
      terms := terms.push d.toExpr
      types := types.push t
    let final := types[3]!.getAppArgs
    let mut proof := terms[3]!
    for i in [0:3] do
      let j := 2 - i
      let a := types[j]!.getAppArgs
      proof := Lean.mkAppN (Lean.mkConst ``HEq.trans types[j]!.getAppFn.constLevels!)
        #[a[0]!, a[2]!, final[2]!, a[1]!, a[3]!, final[3]!, terms[j]!, proof]
    Lean.Elab.Tactic.closeMainGoal `exact proof
end SquareKit.Internal.PathTransport.TwoFamily
