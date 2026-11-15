import SquareKit.Internal.PathTransport.TwoFamilyPathSubstitutionLaws
import SquareKit.Internal.PathTransport.TwoFamilyPathJCells
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ uE vE wE
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
variable (E : Family.{_,_,_,uE,vE,wE} (PathContext F))
/-- The reflexive motive commutes with the constructed path substitution. -/
theorem pathMotive_reindex :
    reindex (reindexHigher F σ) (reindex (pathReflexivity F) E) =
      reindex (pathReflexivity (reindex σ F)) (reindex (pathReindex F σ) E) := by
  rw [reindex_comp, reindex_comp, pathReindex_reflexivity]
/-- Substitute an arbitrary supplied reflexive branch, with its full higher action. -/
noncomputable def pathBranchReindex (d : Section (reindex (pathReflexivity F) E)) :
    Section (reindex (pathReflexivity (reindex σ F)) (reindex (pathReindex F σ) E)) :=
  Section.cast (pathMotive_reindex F σ E) (d.reindex _ (reindexHigher F σ))
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Substituting a branch preserves its chosen fiber object. -/
theorem pathBranchReindex_obj (d : Section (reindex (pathReflexivity F) E))
    (x : Total (reindex σ F)) :
    HEq ((pathBranchReindex F σ E d).lift.obj x).fiber
      (d.lift.obj ((reindexHigher F σ).obj x)).fiber := by
  have h1 := Section.cast_obj_fiber (pathMotive_reindex F σ E)
    (d.reindex (reindex (pathReflexivity F) E) (reindexHigher F σ)) x
  have h2 := d.reindex_obj_fiber (reindex (pathReflexivity F) E) (reindexHigher F σ) x
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
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Substituting a branch preserves its chosen fiber arrow. -/
theorem pathBranchReindex_map (d : Section (reindex (pathReflexivity F) E))
    {x y : Total (reindex σ F)} (p : x ⟶ y) :
    HEq ((pathBranchReindex F σ E d).lift.map p).fiber
      (d.lift.map ((reindexHigher F σ).map p)).fiber := by
  have h1 := Section.cast_map_fiber (pathMotive_reindex F σ E)
    (d.reindex (reindex (pathReflexivity F) E) (reindexHigher F σ)) p
  have h2 := d.reindex_map_fiber (reindex (pathReflexivity F) E) (reindexHigher F σ) p
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
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Substituting a branch preserves its chosen genuine fiber cell. -/
theorem pathBranchReindex_cell (d : Section (reindex (pathReflexivity F) E))
    {x y : Total (reindex σ F)} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq ((pathBranchReindex F σ E d).lift.map₂ α).fiber
      (d.lift.map₂ ((reindexHigher F σ).map₂ α)).fiber := by
  have h1 := Section.cast_cell_fiber (pathMotive_reindex F σ E)
    (d.reindex (reindex (pathReflexivity F) E) (reindexHigher F σ)) α
  have h2 := d.reindex_cell_fiber (reindex (pathReflexivity F) E) (reindexHigher F σ) α
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
