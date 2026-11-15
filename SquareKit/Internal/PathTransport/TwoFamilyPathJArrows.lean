import SquareKit.Internal.PathTransport.TwoFamilyPathJObjects
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
/-- The transported component acts as the identity functor at reflexivity. -/
theorem contractionTransport_functor_refl (x : Total F) :
    E.map ((pathContraction F).app ((pathReflexivity F).obj x)) =
      𝟙 (E.obj ((pathReflexivity F).obj x)) := by
  exact (congrArg E.map (pathContraction_app_refl F x)).trans
    (E.map_id ((pathReflexivity F).obj x))

/-- The inverse comparison at a reflexive arrow is only its typed boundary. -/
theorem contractionTransport_comparison_refl {x y : Total F} (p : x ⟶ y) :
    ∃ e, ((strongPostcomp (pathContraction F) E).naturality
      ((pathReflexivity F).map p)).inv = eqToHom e := by
  dsimp only [strongPostcomp]
  simp only [Iso.trans_inv, Iso.symm_inv, PrelaxFunctor.map₂Iso, Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map,
    E.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv]
  have h := pathContraction_naturality_refl F p
  have hi : ((pathContraction F).naturality ((pathReflexivity F).map p)).inv =
      eqToHom ((contraction_refl_right F p).trans (contraction_refl_left F p).symm) := by
    apply (cancel_mono ((pathContraction F).naturality ((pathReflexivity F).map p)).hom).mp
    rw [Iso.inv_hom_id, h, eqToHom_trans]
    rfl
  rw [hi, PrelaxFunctor.map₂_eqToHom, eqToHom_trans, eqToHom_trans]
  refine ⟨?_, ?_⟩
  · change E.map ((pathContraction F).app ((pathReflexivity F).obj x)) ≫
      E.map ((pathReflexivity F).map p) =
      E.map ((contractionRetract F).map ((pathReflexivity F).map p)) ≫
        E.map ((pathContraction F).app ((pathReflexivity F).obj y))
    rw [← E.map_comp, ← E.map_comp]
    exact congrArg E.map ((contraction_refl_right F p).trans (contraction_refl_left F p).symm)
  · rfl
/-- Transport retains an arbitrary motive arrow over a reflexive path arrow. -/
theorem contractionTransport_map_refl {x y : Total F} (p : x ⟶ y)
    (a : E.obj ((contractionRetract F).obj ((pathReflexivity F).obj x)))
    (b : E.obj ((contractionRetract F).obj ((pathReflexivity F).obj y)))
    (q : (E.map ((contractionRetract F).map ((pathReflexivity F).map p))).obj a ⟶ b) :
    HEq (((strongPostcomp (pathContraction F) E).naturality
      ((pathReflexivity F).map p)).inv.app a ≫
      (E.map ((pathContraction F).app ((pathReflexivity F).obj y))).map q) q := by
  obtain ⟨e, he⟩ := contractionTransport_comparison_refl F E p
  rw [he, StrongMap.classifier_eqToHom_app]
  refine HEq.trans (eqToHom_comp_heq _ _) ?_
  exact congr_arg_heq (fun H => H.map q) (contractionTransport_functor_refl F E y)
/-- Transport retains every arrow of a section along reflexivity. -/
theorem transport_map_refl (s : Section (reindex (contractionRetract F) E))
    {x y : Total F} (p : x ⟶ y) :
    HEq (((Section.transport E (pathContraction F) s).lift.map
      ((pathReflexivity F).map p)).fiber)
      ((s.lift.map ((pathReflexivity F).map p)).fiber) := by
  have hb (x : Total F) :
      (s.lift.obj ((pathReflexivity F).obj x)).base = (pathReflexivity F).obj x :=
    congrArg (fun H => H.obj ((pathReflexivity F).obj x)) s.over
  have hp : HEq (s.lift.map ((pathReflexivity F).map p)).base ((pathReflexivity F).map p) :=
    congr_arg_heq (fun H => H.map ((pathReflexivity F).map p)) s.over
  have h (bx byctx : PathContext F)
      (hx : bx = (pathReflexivity F).obj x) (hy : byctx = (pathReflexivity F).obj y)
      (a : E.obj ((contractionRetract F).obj bx))
      (b : E.obj ((contractionRetract F).obj byctx))
      (r : bx ⟶ byctx) (hr : HEq r ((pathReflexivity F).map p))
      (q : (E.map ((contractionRetract F).map r)).obj a ⟶ b) :
      HEq (((strongPostcomp (pathContraction F) E).naturality r).inv.app a ≫
        (E.map ((pathContraction F).app byctx)).map q) q := by
    subst bx
    subst byctx
    cases eq_of_heq hr
    exact contractionTransport_map_refl F E p a b q
  exact h _ _ (hb x) (hb y) _ _ _ hp _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The constructed eliminator recovers each supplied motive arrow at reflexivity. -/
theorem pathJ_map_beta (d : Section (reindex (pathReflexivity F) E))
    {x y : Total F} (p : x ⟶ y) :
    HEq (((pathJ F E d).lift.map ((pathReflexivity F).map p)).fiber)
      ((d.lift.map p).fiber) := by
  let r := d.reindex (reindex (pathReflexivity F) E) (pathFirst F)
  let s := Section.cast (reindex_comp E (pathReflexivity F) (pathFirst F)) r
  have h1 := Section.cast_map_fiber (reindex_id E)
    (Section.transport E (pathContraction F) s) ((pathReflexivity F).map p)
  have h2 := transport_map_refl F E s p
  have h3 := Section.cast_map_fiber (reindex_comp E (pathReflexivity F) (pathFirst F))
    r ((pathReflexivity F).map p)
  have h4 := d.reindex_map_fiber (reindex (pathReflexivity F) E)
    (pathFirst F) ((pathReflexivity F).map p)
  have h5 := congr_arg_heq (fun q => (d.lift.map q).fiber) (pathFirst_reflexivity_map F p)
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

end SquareKit.Internal.PathTransport.TwoFamily
