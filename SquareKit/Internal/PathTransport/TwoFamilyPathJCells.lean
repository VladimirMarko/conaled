import SquareKit.Internal.PathTransport.TwoFamilyPathJArrows
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uE vE wE
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
variable [IsLocallyGroupoid Γ]
variable (E : Family.{_,_,_,uE,vE,wE} (PathContext F))
private theorem comparison_at {x y : Total F} (p : x ⟶ y)
    (bx byctx : PathContext F)
    (hx : bx = (pathReflexivity F).obj x) (hy : byctx = (pathReflexivity F).obj y)
    (r : bx ⟶ byctx) (hr : HEq r ((pathReflexivity F).map p)) :
    ∃ e, ((strongPostcomp (pathContraction F) E).naturality r).inv = eqToHom e := by
  subst bx
  subst byctx
  cases eq_of_heq hr
  exact contractionTransport_comparison_refl F E p
private theorem cell_at (y : Total F) (byctx : PathContext F)
    (hy : byctx = (pathReflexivity F).obj y)
    {a b : E.obj ((contractionRetract F).obj byctx)} {f g : a ⟶ b} (α : f ⟶ g) :
    HEq ((E.map ((pathContraction F).app byctx)).map₂ α) α := by
  subst byctx
  exact congr_arg_heq (fun H => H.map₂ α) (contractionTransport_functor_refl F E y)
/-- Transport retains every genuine 2-cell of an arbitrary motive section at reflexivity. -/
theorem transport_cell_refl (s : Section (reindex (contractionRetract F) E))
    {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (((Section.transport E (pathContraction F) s).lift.map₂
      ((pathReflexivity F).map₂ α)).fiber)
      ((s.lift.map₂ ((pathReflexivity F).map₂ α)).fiber) := by
  have hb (x : Total F) :
      (s.lift.obj ((pathReflexivity F).obj x)).base = (pathReflexivity F).obj x :=
    congrArg (fun H => H.obj ((pathReflexivity F).obj x)) s.over
  have hp : HEq (s.lift.map ((pathReflexivity F).map p)).base ((pathReflexivity F).map p) :=
    congr_arg_heq (fun H => H.map ((pathReflexivity F).map p)) s.over
  obtain ⟨e, he⟩ := comparison_at F E p _ _ (hb x) (hb y) _ hp
  change HEq ((_ ◁ _) ≫ eqToHom _) _
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  rw [he, StrongMap.classifier_eqToHom_app]
  refine HEq.trans (eqToHom_left_heq _ _) ?_
  exact cell_at F E y _ (hb y) _
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The eliminator retains every supplied genuine 2-cell at reflexivity. -/
theorem pathJ_cell_beta (d : Section (reindex (pathReflexivity F) E))
    {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (((pathJ F E d).lift.map₂ ((pathReflexivity F).map₂ α)).fiber)
      ((d.lift.map₂ α).fiber) := by
  let r := d.reindex (reindex (pathReflexivity F) E) (pathFirst F)
  let s := Section.cast (reindex_comp E (pathReflexivity F) (pathFirst F)) r
  have h1 := Section.cast_cell_fiber (reindex_id E)
    (Section.transport E (pathContraction F) s) ((pathReflexivity F).map₂ α)
  have h2 := transport_cell_refl F E s α
  have h3 := Section.cast_cell_fiber (reindex_comp E (pathReflexivity F) (pathFirst F))
    r ((pathReflexivity F).map₂ α)
  have h4 := d.reindex_cell_fiber (reindex (pathReflexivity F) E)
    (pathFirst F) ((pathReflexivity F).map₂ α)
  have h5 := congr_arg_heq
    (fun H : StrictPseudofunctor (Total F) (Total F) => (d.lift.map₂ (H.map₂ α)).fiber)
    (pathReflexivity_first F)
  -- Supply the chain's dependent types explicitly, as for section substitution.
  -- The resulting ordinary HEq proof is checked by the kernel.
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut terms := #[]
    let mut types := #[]
    for name in [`h1, `h2, `h3, `h4, `h5] do
      let d ← Lean.Meta.getLocalDeclFromUserName name
      let t ← Lean.instantiateMVars d.type
      unless t.isAppOfArity ``HEq 4 do throwError "Expected an HEq proof"
      terms := terms.push d.toExpr
      types := types.push t
    let final := types[4]!.getAppArgs
    let mut proof := terms[4]!
    for i in [0:4] do
      let j := 3 - i
      let a := types[j]!.getAppArgs
      proof := Lean.mkAppN (Lean.mkConst ``HEq.trans types[j]!.getAppFn.constLevels!)
        #[a[0]!, a[2]!, final[2]!, a[1]!, a[3]!, final[3]!, terms[j]!, proof]
    Lean.Elab.Tactic.closeMainGoal `exact proof

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Reflexive computation holds for the whole higher section, including its 2-cell data. -/
theorem pathJ_beta (d : Section (reindex (pathReflexivity F) E)) :
    (pathJ F E d).reindex E (pathReflexivity F) = d := by
  apply Section.ext_fiber (reindex (pathReflexivity F) E)
  · intro x
    exact ((pathJ F E d).reindex_obj_fiber E (pathReflexivity F) x).trans
      (pathJ_obj_beta F E d x)
  · intro x y p
    have h1 := (pathJ F E d).reindex_map_fiber E (pathReflexivity F) p
    have h2 := pathJ_map_beta F E d p
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
  · intro x y p q α
    have h1 := (pathJ F E d).reindex_cell_fiber E (pathReflexivity F) α
    have h2 := pathJ_cell_beta F E d α
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
