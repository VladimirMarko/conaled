import SquareKit.Internal.PathTransport.TwoFamilyModelRootSub
import SquareKit.Internal.PathTransport.TwoFamilyRootedNaturality
import SquareKit.Internal.PathTransport.TwoFamilySourceContractionSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyModelPathSub
import SquareKit.Internal.PathTransport.TwoFamilySourceContraction
/-! The constructed rooted contraction inhabits the exact source path context.
Its normalization and substitution laws retain the original strong comparison. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
noncomputable def rawRootContraction {Γ : Context.{u}} (A : Family Γ) (x : ULift.{u+1} (TwoFamily.Section A.data)) :
    SourceContraction (Γ := (M).pathContext A x) (Δ := Γ)
      (TwoFamily.rootedReflexivity A.data x.down) :=
  ⟨TwoFamily.rootedRetraction A.data x.down, TwoFamily.rootedContraction A.data x.down⟩

private theorem normalized_of_laws {Γ Δ : Context.{u}} {i : StrictPseudofunctor Δ Γ}
    (c : SourceContraction i)
    (hi : i.comp c.retraction = StrictPseudofunctor.id Δ)
    (hη : HEq (strongPrecomp c.homotopy i) (Pseudofunctor.StrongTrans.id i.toPseudofunctor)) : c.Normalized :=
  ⟨hi,hη⟩
theorem rawRootContraction_normalized {Γ : Context.{u}} (A : Family Γ) (x : ULift.{u+1} (TwoFamily.Section A.data)) :
    (rawRootContraction C D A x).Normalized := by
  have h1 := TwoFamily.rootedReflexivity_retraction A.data x.down
  have h2 := TwoFamily.rootedContraction_reflexive A.data x.down
  apply normalized_of_laws
  · exact h1
  -- Reuse the checked proof term; repeated source-instance conversion is expensive.
  · run_tac Lean.Elab.Tactic.withMainContext do
      let d ← Lean.Meta.getLocalDeclFromUserName `h2
      let g ← Lean.Elab.Tactic.getMainGoal
      g.assign d.toExpr
      Lean.Elab.Tactic.replaceMainGoal []

private def normalized_cast {Γ Δ : Context.{u}} {i j : StrictPseudofunctor Δ Γ}
    (c : SourceContraction i) (hc : c.Normalized) (h : i = j) :
    {d : SourceContraction j // d.Normalized} :=
  ⟨c.cast h, SourceContraction.cast_normalized h c hc⟩
noncomputable def rootContraction {Γ : Context.{u}} (A : Family Γ) (x : ULift.{u+1} (TwoFamily.Section A.data)) :
    {c : SourceContraction ((M).rootSub A x).down // c.Normalized} :=
  normalized_cast (rawRootContraction C D A x) (rawRootContraction_normalized C D A x)
    (rootSub_down_eq C D A x).symm

theorem rawRootContraction_square {Γ Δ : Context.{u}} (A : Family Γ)
    (x : ULift.{u+1} (TwoFamily.Section A.data)) (σ : ULift.{u+1} (StrictPseudofunctor Δ Γ)) :
    SourceContraction.Square (rawRootContraction C D A x)
      (rawRootContraction C D ((M).subTy A σ) ((M).subTm x σ))
      ((M).pathSub A x σ).down σ.down := by
  rw [pathSub_down_eq]
  have h1 := TwoFamily.rootedSubstitution_reflexivity A.data x.down σ.down
  have h2 := (TwoFamily.rootedSubstitution_retraction A.data x.down σ.down).symm
  have h3 := TwoFamily.rootedContraction_reindex A.data x.down σ.down
  constructor
  · run_tac Lean.Elab.Tactic.withMainContext do
      let d ← Lean.Meta.getLocalDeclFromUserName `h1
      (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
      Lean.Elab.Tactic.replaceMainGoal []
  · run_tac Lean.Elab.Tactic.withMainContext do
      let d ← Lean.Meta.getLocalDeclFromUserName `h2
      (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
      Lean.Elab.Tactic.replaceMainGoal []
  · run_tac Lean.Elab.Tactic.withMainContext do
      let d ← Lean.Meta.getLocalDeclFromUserName `h3
      (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
      Lean.Elab.Tactic.replaceMainGoal []
theorem rootContraction_square {Γ Δ : Context.{u}} (A : Family Γ)
    (x : ULift.{u+1} (TwoFamily.Section A.data)) (σ : ULift.{u+1} (StrictPseudofunctor Δ Γ)) :
    SourceContraction.Square (rootContraction C D A x).val
      (rootContraction C D ((M).subTy A σ) ((M).subTm x σ)).val
      ((M).pathSub A x σ).down σ.down := by
  have h := (rawRootContraction_square C D A x σ).cast
    (σ' := ((M).pathSub A x σ).down) (τ' := σ.down) (rootSub_down_eq C D A x).symm
    (rootSub_down_eq C D ((M).subTy A σ) ((M).subTm x σ)).symm rfl rfl
  run_tac Lean.Elab.Tactic.withMainContext do
    let d ← Lean.Meta.getLocalDeclFromUserName `h
    (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
    Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
