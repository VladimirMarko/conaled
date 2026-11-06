import SquareKit.Internal.PathTransport.TwoFamilyPathContractionSubstitutionCells
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
private theorem map₂_heq {A B : Type*} [Bicategory A] [Bicategory B]
    (H : PrelaxFunctor A B) {x y : A} {p q p' q' : x ⟶ y}
    (hp : p = p') (hq : q = q') (α : p ⟶ q) (β : p' ⟶ q')
    (h : HEq α β) : HEq (H.map₂ α) (H.map₂ β) := by
  cases hp
  cases hq
  cases eq_of_heq h
  rfl
private theorem pathFirst_reflects_heq {x y : PathContext F}
    {p q p' q' : x ⟶ y} (hp : p = p') (hq : q = q')
    (α : p ⟶ q) (β : p' ⟶ q')
    (h : HEq ((pathFirst F).map₂ α) ((pathFirst F).map₂ β)) : HEq α β := by
  cases hp
  cases hq
  exact heq_of_eq (pathFirst_cell_injective F α β (eq_of_heq h))
/-- Context substitution preserves the full contraction comparison cell. -/
theorem contractionNaturalityCell_reindex {x y : PathContext (reindex σ F)} (p : x ⟶ y) :
    HEq ((pathReindex F σ).map₂ (contractionNaturalityCell (reindex σ F) p))
      (contractionNaturalityCell F ((pathReindex F σ).map p)) := by
  apply pathFirst_reflects_heq F (contractionLeft_reindex F σ p)
    (contractionRight_reindex F σ p)
  have h1 := congr_arg_heq (fun H => H.map₂ (contractionNaturalityCell (reindex σ F) p))
    (pathReindex_first F σ)
  have h2 := map₂_heq (reindexHigher F σ).toPrelaxFunctor
    (contractionLeft_projection (reindex σ F) p) (contractionRight_projection (reindex σ F) p)
    _ _ (contractionNaturalityCell_first_heq (reindex σ F) p)
  have h3 := heq_of_eq ((reindexHigher F σ).map₂_id ((pathFirst (reindex σ F)).map p))
  have h4 := (congr_arg_heq (fun H => 𝟙 (H.map p)) (pathReindex_first F σ)).symm
  have h5 := (contractionNaturalityCell_first_heq F ((pathReindex F σ).map p)).symm
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
