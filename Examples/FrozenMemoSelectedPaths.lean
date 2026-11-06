import Examples.FrozenMemoStageEvaluation
/-! Explicit original frozen path operands and their source evaluations.
Reindexing retains the selected homotopy through all eight binders. -/
noncomputable section
namespace Examples.FrozenMemoStages
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.DependentJudgments.Contextual.Memo
open Examples.GuardedGroupoidMemo
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
private theorem identity_cast (M : StructuralModel.{u}) {Γ : M.Context}
 {A B : M.Family Γ} (e : A = B) (x y : M.Section Γ A) :
 M.identity A x y = M.identity B (cast (congrArg (M.Section Γ) e) x)
 (cast (congrArg (M.Section Γ) e) y) := by cases e; rfl
namespace Parallel
variable {M : StructuralModel.{u}} (R : Parallel M)
def reindex {Δ : M.Context} (σ : M.Substitution Δ R.context) : Parallel M where
 toOnePath := R.toOnePath.reindex σ
 p' := cast (congrArg (M.Section Δ) (M.identity_sub R.family R.x R.y σ)) (M.subTm R.p' σ)
theorem identity_reindex {Δ : M.Context} (σ : M.Substitution Δ R.context) :
 M.subTy R.identity σ = (R.reindex σ).identity := by
 dsimp [identity, reindex, OnePath.reindex]
 rw [M.identity_sub]
 exact identity_cast M (M.identity_sub R.family R.x R.y σ) _ _
end Parallel
structure SelectedPaths (M : StructuralModel.{u}) extends Parallel M where
 h : M.Section context toParallel.identity
namespace SelectedPaths
variable {M : StructuralModel.{u}} (R : SelectedPaths M)
def reindex {Δ : M.Context} (σ : M.Substitution Δ R.context) : SelectedPaths M where
 toParallel := R.toParallel.reindex σ
 h := cast (congrArg (M.Section Δ) (R.toParallel.identity_reindex σ)) (M.subTm R.h σ)
end SelectedPaths
def Parallel.addH {M : StructuralModel.{u}} (R : Parallel M) : SelectedPaths M where
 toParallel := R.reindex (M.weaken R.context R.identity)
 h := cast (congrArg (M.Section _) (R.identity_reindex (M.weaken R.context R.identity)))
   (M.genericVariable R.context R.identity)
variable (M : StructuralModel.{u}) (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
def inputPaths : SelectedPaths M :=
 ((parallel M A B).addH.reindex
   (M.weaken (homotopyPoints M A B).context (qFamily M A B))).reindex
   (M.weaken (qPoints M A B).context (uFamily M A B))
example : (inputPaths M A B).context = inputContext M A B := rfl
end Examples.FrozenMemoStages
namespace Examples.FrozenMemoStages
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.DependentJudgments.Contextual.Memo
open Examples.GuardedGroupoidMemo
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
private theorem selected_term_cast (M : Model.{u}) {Γ : M.Context} {A B : M.Family Γ}
 (e : A = B) (t : M.Section Γ A) :
 Value.term Γ A t = Value.term Γ B (cast (congrArg (M.Section Γ) e) t) := by cases e; rfl
variable {M : Model.{u}} {V : Type} {Ω : List (Contextual.Judgment V)}
variable {ρ : V → Value M.toStructuralModel}
theorem ParallelEvaluation.reindex {F : Frozen.Parallel Ω} {R : Parallel M.toStructuralModel}
 (E : ParallelEvaluation M ρ F R) {d s : Contextual.Expression V}
 (hs : Sub (Ω := Ω) d F.Γ s) (Δ : M.Context) (σ : M.Substitution Δ R.context)
 (hd : d.eval (Contextual.algebra M) ρ = .context Δ)
 (he : s.eval (Contextual.algebra M) ρ = .substitution Δ R.context σ) :
 ParallelEvaluation M ρ (F.reindex hs) (R.reindex σ) where
 toOnePathEvaluation := E.toOnePathEvaluation.reindex hs Δ σ hd he
 p'_eval := (subTm_eval M ρ F.p' s R.context Δ _ R.p' σ E.p'_eval he).trans
  (selected_term_cast M (M.identity_sub R.family R.x R.y σ) _)
structure SelectedPathsEvaluation (M : Model.{u}) {V : Type} {Ω : List (Contextual.Judgment V)}
 (ρ : V → Value M.toStructuralModel) (F : Frozen.Homotopy Ω) (R : SelectedPaths M.toStructuralModel)
 : Prop extends ParallelEvaluation M ρ F.toParallel R.toParallel where
 h_eval : F.h.eval (Contextual.algebra M) ρ = .term R.context R.toParallel.identity R.h
namespace SelectedPathsEvaluation
 theorem reindex {F : Frozen.Homotopy Ω} {R : SelectedPaths M.toStructuralModel}
 (E : SelectedPathsEvaluation M ρ F R) {d s : Contextual.Expression V}
 (hs : Sub (Ω := Ω) d F.Γ s) (Δ : M.Context) (σ : M.Substitution Δ R.context)
 (hd : d.eval (Contextual.algebra M) ρ = .context Δ)
 (he : s.eval (Contextual.algebra M) ρ = .substitution Δ R.context σ) :
 SelectedPathsEvaluation M ρ (F.reindex hs) (R.reindex σ) where
 toParallelEvaluation := E.toParallelEvaluation.reindex hs Δ σ hd he
 h_eval := (subTm_eval M ρ F.h s R.context Δ _ R.h σ E.h_eval he).trans
  (selected_term_cast M (R.toParallel.identity_reindex σ) _)
end SelectedPathsEvaluation
theorem ParallelEvaluation.addH {F : Frozen.Parallel Ω} {R : Parallel M.toStructuralModel}
 (E : ParallelEvaluation M ρ F R) : SelectedPathsEvaluation M ρ F.addH R.addH where
 toParallelEvaluation := E.reindex F.hIdentity.weaken _ _
  (extend_eval M ρ _ _ _ _ E.context_eval E.identity_eval)
  (weaken_eval M ρ _ _ _ _ E.context_eval E.identity_eval)
 h_eval := (generic_eval M ρ _ _ _ _ E.context_eval E.identity_eval).trans
  (selected_term_cast M (R.identity_reindex (M.weaken R.context R.identity)) _)
variable (M : Model.{u}) (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
theorem inputPaths_eval : SelectedPathsEvaluation M (Examples.FrozenMemoSignature.environment M A B)
 signature.input.toHomotopy (inputPaths M.toStructuralModel A B) :=
 (((parallel_eval M A B).addH).reindex signature.withH.hQ.weaken _ _
  (extend_eval M _ _ _ _ _ (homotopyPoints_eval M A B).context_eval (qFamily_eval M A B))
  (weaken_eval M _ _ _ _ _ (homotopyPoints_eval M A B).context_eval (qFamily_eval M A B))).reindex
 signature.withQ.hU.weaken _ _
 (extend_eval M _ _ _ _ _ (qPoints_eval M A B).context_eval (uFamily_eval M A B))
 (weaken_eval M _ _ _ _ _ (qPoints_eval M A B).context_eval (uFamily_eval M A B))
end Examples.FrozenMemoStages

namespace Examples.FrozenMemoStages
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments
open Examples.GuardedGroupoidMemo
universe u
variable (M : Model.{u}) (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
theorem inputPaths_h_heq : HEq (inputPaths M.toStructuralModel A B).h
 (selectedHomotopy M.toStructuralModel A B) :=
 (Value.term.inj ((inputPaths_eval M A B).h_eval.symm.trans (selectedHomotopy_eval M A B))).2.2
end Examples.FrozenMemoStages
