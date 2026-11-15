import SquareKit.Internal.PathTransport.TwoFamilyClosedIdentitySubstitution
import SquareKit.Internal.PathTransport.TwoFamilyThinSection
/-! Reflexivity commutes with substitution as a whole higher section.
Identity-fiber arrows remain observable; only their 2-cells are locally thin. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
private theorem discrete_eqToHom_heq_id {C : Type*} [Category C] {a b : C} (e : a = b) :
    HEq (Discrete.mk (eqToHom e)) (Discrete.mk (𝟙 b)) := by cases e; rfl

private theorem sectionOfLift_comp_map_fiber {A B C : Type*}
    [Bicategory A] [Strict A] [Bicategory B] [Strict B] [Bicategory C] [Strict C]
    (G : Family C) (H : StrictPseudofunctor A B) (K : StrictPseudofunctor B (Total G))
    {x y : A} (p : x ⟶ y) :
    HEq ((sectionOfLift G (H.comp K)).lift.map p).fiber ((K.map (H.map p)).fiber) := HEq.rfl

theorem pathReflexivity_map_fiber {x y : Total F} (p : x ⟶ y) :
    ((pathReflexivity F).map p).fiber = Discrete.mk (eqToHom (diagonal_identity F p)) := rfl

set_option backward.defeqAttrib.useBackward false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem closedReflexivity_map_fiber (s : Section F) {x y : Γ} (p : x ⟶ y) :
    HEq ((closedReflexivity F s).lift.map p).fiber
      (Discrete.mk (𝟙 (𝟙 (s.lift.obj y).fiber))) := by
  have h := Section.cast_map_fiber
    (congrArg (fun H => reindex H (openIdHigher F)) (closedReflexivity_base F s))
    (sectionOfLift (openIdHigher F) (s.lift.comp (pathReflexivity F))) p
  have k := sectionOfLift_comp_map_fiber (openIdHigher F) s.lift (pathReflexivity F) p
  rw [pathReflexivity_map_fiber] at k
  have k2 := @discrete_eqToHom_heq_id
    ((s.lift.obj y).fiber ⟶ (s.lift.obj y).fiber) _
    ((openIdMap F ((diagonalTotal F).map (s.lift.map p))).obj (𝟙 (s.lift.obj x).fiber))
    (𝟙 (s.lift.obj y).fiber) (diagonal_identity F (s.lift.map p))
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut terms := #[]
    let mut types := #[]
    for name in [`h, `k, `k2] do
      let d ← Lean.Meta.getLocalDeclFromUserName name
      let t ← Lean.instantiateMVars d.type
      unless t.isAppOfArity ``HEq 4 do throwError "Expected an HEq proof"
      terms := terms.push d.toExpr
      types := types.push t
    let final := types[2]!.getAppArgs
    let mut proof := terms[2]!
    for i in [0:2] do
      let j := 1 - i
      let a := types[j]!.getAppArgs
      proof := Lean.mkAppN (Lean.mkConst ``HEq.trans types[j]!.getAppFn.constLevels!)
        #[a[0]!, a[2]!, final[2]!, a[1]!, a[3]!, final[3]!, terms[j]!, proof]
    Lean.Elab.Tactic.closeMainGoal `exact proof

omit [Strict Γ] [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
private theorem identity_obj_heq {γ δ : Γ} (e : γ = δ) {a : F.obj γ} {b : F.obj δ}
    (h : HEq a b) : HEq (LocallyDiscrete.mk (𝟙 a)) (LocallyDiscrete.mk (𝟙 b)) := by
  cases e
  cases eq_of_heq h
  rfl
omit [Strict Γ] [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
private theorem identity_map_heq {γ δ : Γ} (e : γ = δ) {a : F.obj γ} {b : F.obj δ}
    (h : HEq a b) : HEq (Discrete.mk (𝟙 (𝟙 a))) (Discrete.mk (𝟙 (𝟙 b))) := by
  cases e
  cases eq_of_heq h
  rfl

variable {Δ : Type*} [Bicategory Δ] [Strict Δ] (σ : StrictPseudofunctor Δ Γ)
set_option backward.defeqAttrib.useBackward false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem closedReflexivity_reindex_heq (s : Section F) :
    HEq ((closedReflexivity F s).reindex (closedId F s s) σ)
      (closedReflexivity (reindex σ F) (s.reindex F σ)) := by
  have : ∀ γ (a b : (reindex σ (closedId F s s)).obj γ) (p q : a ⟶ b),
      Subsingleton (p ⟶ q) := by
    intro γ a b p q
    exact @Discrete.instSubsingletonDiscreteHom _ p q
  apply Section.hext_thin_fibers _ (closedId_reindex F σ s s)
  · intro γ
    have hb : σ.obj ((s.reindex F σ).lift.obj γ).base = (s.lift.obj (σ.obj γ)).base :=
      (congrArg σ.obj ((s.reindex F σ).objBase (reindex σ F) γ)).trans
        (s.objBase F (σ.obj γ)).symm
    have h1 := (closedReflexivity F s).reindex_obj_fiber (closedId F s s) σ γ
    have h2 := closedReflexivity_obj F s (σ.obj γ)
    have h3 := (closedReflexivity_obj (reindex σ F) (s.reindex F σ) γ).symm
    have h4 := (identity_obj_heq F hb (s.reindex_obj_fiber F σ γ)).symm
    run_tac Lean.Elab.Tactic.withMainContext do
      let mut terms := #[]
      let mut types := #[]
      for name in [`h1, `h2, `h4, `h3] do
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
  · intro x y p
    have hb : σ.obj ((s.reindex F σ).lift.obj y).base = (s.lift.obj (σ.obj y)).base :=
      (congrArg σ.obj ((s.reindex F σ).objBase (reindex σ F) y)).trans
        (s.objBase F (σ.obj y)).symm
    have h1 := (closedReflexivity F s).reindex_map_fiber (closedId F s s) σ p
    have h2 := closedReflexivity_map_fiber F s (σ.map p)
    have h3 := (closedReflexivity_map_fiber (reindex σ F) (s.reindex F σ) p).symm
    have h4 := (identity_map_heq F hb (s.reindex_obj_fiber F σ y)).symm
    run_tac Lean.Elab.Tactic.withMainContext do
      let mut terms := #[]
      let mut types := #[]
      for name in [`h1, `h2, `h4, `h3] do
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
