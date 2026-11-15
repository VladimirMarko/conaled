import SquareKit.Internal.Cubical.ContextualActionComparison

/-! Evaluation of the pointwise action section recovers the whole marked identity map. -/
noncomputable section
namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => model Base Fiber
variable {Γ : Presheaf.Context.{u}} (A C : LawfulFamily Γ)
  (t : Term (reindex C.family (projection A.family))) (x y : Term A.family)
  (p : Term (normalizedIdentity A.family x y))

private theorem convert_reindex_heq {Γ Δ : Presheaf.Context.{u}} {A B : Family Γ}
    (e : A = B) (s : Term A) (σ : Δ ⟶ Γ) : HEq ((s.convert e).reindex σ) (s.reindex σ) := by
  cases e; rfl
private theorem cast_down {Δ : Presheaf.Context.{u}} {D E : LawfulFamily Δ}
    (h : D = E) (s : ULift.{u+1} (Term D.family)) :
    HEq ((cast (congrArg (fun F : LawfulFamily Δ => ULift.{u+1} (Term F.family)) h) s).down) s.down := by
  cases h; rfl

theorem pointwiseInput_endpoint : HEq
    ((pointwiseInput Base Fiber A x).reindex ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩).down) p :=
  (convert_reindex_heq _ (generic (actionPathFamily Base Fiber A x).family)
    ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩).down).trans
    (cast_down ((M).toStructuralModel.pathFamily_at A ⟨x⟩ ⟨y⟩).symm ⟨p⟩)

theorem pointwiseResult_endpoint : HEq
    ((pointwiseResult Base Fiber A C t x).reindex ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩).down)
    (p.map (normalizedIdentityMap (functionMap A C t) x y)) := by
  let σ := ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩).down
  have h := normalizedIdentityMap_reindex (pointwiseMap Base Fiber A C t x)
    (x.reindex (actionProjection Base Fiber A x))
    ((generic A.family).reindex (projection (actionPathFamily Base Fiber A x).family)) σ
    (pointwiseInput Base Fiber A x)
  have hc := Term.convert_heq
    (normalizedIdentity_reindex (reindex A.family (actionProjection Base Fiber A x))
      (x.reindex (actionProjection Base Fiber A x))
      ((generic A.family).reindex (projection (actionPathFamily Base Fiber A x).family)) σ)
    ((pointwiseInput Base Fiber A x).reindex σ)
  have hi := eq_of_heq (hc.trans (pointwiseInput_endpoint Base Fiber A x y p))
  rw [hi] at h
  exact (Term.convert_heq _ _).symm.trans (heq_of_eq h)

theorem pointwiseApValue_map : HEq (pointwiseApValue Base Fiber A C t x y p).down
    (p.map (normalizedIdentityMap (functionMap A C t) x y)) := by
  have h₁ := cast_down (ordinaryApMotive_endpoint M A C ⟨t⟩ ⟨x⟩ ⟨y⟩ ⟨p⟩)
    ((M).subTm (pointwiseApSection Base Fiber A C t x)
      ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩))
  have h₂ := convert_reindex_heq (pointwiseMotive_eq Base Fiber A C t x).symm
    (pointwiseResult Base Fiber A C t x) ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩).down
  have h₃ := pointwiseResult_endpoint Base Fiber A C t x y p
  run_tac Lean.Elab.Tactic.withMainContext do
    let h₁ ← Lean.Meta.getLocalDeclFromUserName `h₁
    let h₂ ← Lean.Meta.getLocalDeclFromUserName `h₂
    let h₃ ← Lean.Meta.getLocalDeclFromUserName `h₃
    let t₁ ← Lean.instantiateMVars h₁.type
    let t₂ ← Lean.instantiateMVars h₂.type
    let t₃ ← Lean.instantiateMVars h₃.type
    let a := t₁.getAppArgs
    let b := t₂.getAppArgs
    let c := t₃.getAppArgs
    let q := Lean.mkAppN (Lean.mkConst ``HEq.trans t₁.getAppFn.constLevels!)
      #[a[0]!,a[2]!,b[2]!,a[1]!,a[3]!,b[3]!,h₁.toExpr,h₂.toExpr]
    let proof := Lean.mkAppN (Lean.mkConst ``HEq.trans t₁.getAppFn.constLevels!)
      #[a[0]!,b[2]!,c[2]!,a[1]!,b[3]!,c[3]!,q,h₃.toExpr]
    Lean.Elab.Tactic.closeMainGoal `exact proof

end SquareKit.Cubical.Contextual
