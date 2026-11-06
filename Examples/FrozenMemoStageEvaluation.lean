import Examples.FrozenMemoStages
import Examples.FrozenMemoSignature
noncomputable section
namespace Examples.FrozenMemoStages
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.DependentJudgments.Contextual.Memo
open Examples.GuardedGroupoidMemo
universe u
variable (M : Model.{u}) {V : Type} {Ω : List (Contextual.Judgment V)}
variable (ρ : V → Value M.toStructuralModel)
structure PointsEvaluation (F : Frozen.Points Ω) (R : Points M.toStructuralModel) : Prop where
  context_eval : F.Γ.eval (Contextual.algebra M) ρ = .context R.context
  family_eval : F.A.eval (Contextual.algebra M) ρ = .family R.context R.family
  fiber_eval : F.B.eval (Contextual.algebra M) ρ = .family (M.extend R.context R.family) R.fiber
  x_eval : F.x.eval (Contextual.algebra M) ρ = .term R.context R.family R.x
  y_eval : F.y.eval (Contextual.algebra M) ρ = .term R.context R.family R.y
  z_eval : F.z.eval (Contextual.algebra M) ρ = .term R.context R.family R.z
namespace PointsEvaluation
variable {M ρ} {F : Frozen.Points Ω} {R : Points M.toStructuralModel}
variable (E : PointsEvaluation M ρ F R)
include E
theorem reindex {d s : Contextual.Expression V} (hs : Sub (Ω := Ω) d F.Γ s)
    (Δ : M.Context) (σ : M.Substitution Δ R.context)
    (hd : d.eval (Contextual.algebra M) ρ = .context Δ)
    (he : s.eval (Contextual.algebra M) ρ = .substitution Δ R.context σ) :
    PointsEvaluation M ρ (F.reindex hs) (R.reindex σ) where
  context_eval := hd
  family_eval := subTy_eval M ρ F.A s R.context Δ R.family σ E.family_eval he
  fiber_eval := subTy_eval M ρ F.B (Contextual.lift d F.A s) _ _ R.fiber _ E.fiber_eval
    (lift_eval M ρ d F.A s R.context Δ R.family σ hd E.family_eval he)
  x_eval := subTm_eval M ρ F.x s R.context Δ R.family R.x σ E.x_eval he
  y_eval := subTm_eval M ρ F.y s R.context Δ R.family R.y σ E.y_eval he
  z_eval := subTm_eval M ρ F.z s R.context Δ R.family R.z σ E.z_eval he

theorem addY : PointsEvaluation M ρ F.addY R.addY :=
  { E.reindex F.hx.family.weaken _ (M.weaken R.context R.family)
      (extend_eval M ρ F.Γ F.A _ _ E.context_eval E.family_eval)
      (weaken_eval M ρ F.Γ F.A _ _ E.context_eval E.family_eval) with
    y_eval := generic_eval M ρ F.Γ F.A _ _ E.context_eval E.family_eval }
theorem addZ : PointsEvaluation M ρ F.addZ R.addZ :=
  { E.reindex F.hx.family.weaken _ (M.weaken R.context R.family)
      (extend_eval M ρ F.Γ F.A _ _ E.context_eval E.family_eval)
      (weaken_eval M ρ F.Γ F.A _ _ E.context_eval E.family_eval) with
    z_eval := generic_eval M ρ F.Γ F.A _ _ E.context_eval E.family_eval }

theorem path_eval : F.pathType.eval (Contextual.algebra M) ρ = .family R.context R.path :=
  identity_eval M ρ F.A F.x F.y _ _ _ _ E.family_eval E.x_eval E.y_eval
end PointsEvaluation

private theorem term_cast {Γ : M.Context} {A B : M.Family Γ} (e : A = B) (t : M.Section Γ A) :
    Value.term Γ A t = Value.term Γ B (cast (congrArg (M.Section Γ) e) t) := by cases e; rfl

structure OnePathEvaluation (F : Frozen.OnePath Ω) (R : OnePath M.toStructuralModel)
    : Prop extends PointsEvaluation M ρ F.toPoints R.toPoints where
  p_eval : F.p.eval (Contextual.algebra M) ρ = .term R.context (M.identity R.family R.x R.y) R.p
namespace OnePathEvaluation
variable {M ρ} {F : Frozen.OnePath Ω} {R : OnePath M.toStructuralModel}
variable (E : OnePathEvaluation M ρ F R)
include E
theorem reindex {d s : Contextual.Expression V} (hs : Sub (Ω := Ω) d F.Γ s)
    (Δ : M.Context) (σ : M.Substitution Δ R.context)
    (hd : d.eval (Contextual.algebra M) ρ = .context Δ)
    (he : s.eval (Contextual.algebra M) ρ = .substitution Δ R.context σ) :
    OnePathEvaluation M ρ (F.reindex hs) (R.reindex σ) where
  toPointsEvaluation := E.toPointsEvaluation.reindex hs Δ σ hd he
  p_eval := (subTm_eval M ρ F.p s R.context Δ _ R.p σ E.p_eval he).trans
    (term_cast M (M.identity_sub R.family R.x R.y σ) _)
end OnePathEvaluation

theorem PointsEvaluation.addP {M ρ} {F : Frozen.Points Ω} {R : Points M.toStructuralModel}
    (E : PointsEvaluation M ρ F R) : OnePathEvaluation M ρ F.addP R.addP where
  toPointsEvaluation := E.reindex F.hPath.weaken _ (M.weaken R.context R.path)
    (extend_eval M ρ F.Γ F.pathType _ _ E.context_eval E.path_eval)
    (weaken_eval M ρ F.Γ F.pathType _ _ E.context_eval E.path_eval)
  p_eval := (generic_eval M ρ F.Γ F.pathType _ _ E.context_eval E.path_eval).trans
    (term_cast M (M.identity_sub R.family R.x R.y (M.weaken R.context R.path)) _)

structure ParallelEvaluation (F : Frozen.Parallel Ω) (R : Parallel M.toStructuralModel) : Prop
    extends OnePathEvaluation M ρ F.toOnePath R.toOnePath where
  p'_eval : F.p'.eval (Contextual.algebra M) ρ = .term R.context (M.identity R.family R.x R.y) R.p'

theorem OnePathEvaluation.addParallel {M ρ} {F : Frozen.OnePath Ω} {R : OnePath M.toStructuralModel}
    (E : OnePathEvaluation M ρ F R) : ParallelEvaluation M ρ F.addParallel R.addParallel where
  toOnePathEvaluation := E.reindex F.toPoints.hPath.weaken _ (M.weaken R.context R.toPoints.path)
    (extend_eval M ρ F.Γ F.toPoints.pathType _ _ E.context_eval E.toPointsEvaluation.path_eval)
    (weaken_eval M ρ F.Γ F.toPoints.pathType _ _ E.context_eval E.toPointsEvaluation.path_eval)
  p'_eval := (generic_eval M ρ F.Γ F.toPoints.pathType _ _ E.context_eval E.toPointsEvaluation.path_eval).trans
    (term_cast M (M.identity_sub R.family R.x R.y (M.weaken R.context R.toPoints.path)) _)

theorem ParallelEvaluation.identity_eval {M ρ} {F : Frozen.Parallel Ω} {R : Parallel M.toStructuralModel}
    (E : ParallelEvaluation M ρ F R) :
    (Contextual.identity F.toPoints.pathType F.p F.p').eval (Contextual.algebra M) ρ =
      .family R.context R.identity :=
  SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics.identity_eval M ρ F.toPoints.pathType F.p F.p' _ _ _ _
    E.toPointsEvaluation.path_eval E.p_eval E.p'_eval

variable (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
local notation "env" => Examples.FrozenMemoSignature.environment M A B

theorem initial_eval : PointsEvaluation M env signature.point (Points.initial A B) := by
  have hg : Contextual.empty.eval (Contextual.algebra M) env = .context M.empty := rfl
  have ha : alpha.eval (Contextual.algebra M) env = .family M.empty A := rfl
  have hb : beta.eval (Contextual.algebra M) env = .family (M.extend M.empty A) B := rfl
  have hw := weaken_eval M env Contextual.empty alpha _ _ hg ha
  have hx := generic_eval M env Contextual.empty alpha _ _ hg ha
  have he := extend_eval M env Contextual.empty alpha _ _ hg ha
  exact {
    context_eval := he
    family_eval := subTy_eval M env alpha (Contextual.weaken Contextual.empty alpha) _ _ A _ ha hw
    fiber_eval := subTy_eval M env beta (Contextual.lift (Contextual.extend Contextual.empty alpha) alpha
      (Contextual.weaken Contextual.empty alpha)) _ _ B _ hb
      (lift_eval M env _ alpha _ _ _ A _ he ha hw)
    x_eval := hx
    y_eval := hx
    z_eval := hx }

theorem parallel_eval : ParallelEvaluation M env signature.withParallel (parallel M.toStructuralModel A B) :=
  (((initial_eval M A B).addY).addZ).addP.addParallel


theorem homotopyPoints_eval : PointsEvaluation M env signature.withH.toPoints
    (homotopyPoints M.toStructuralModel A B) :=
  (parallel_eval M A B).toPointsEvaluation.reindex signature.withParallel.hIdentity.weaken _ _
    (extend_eval M env _ _ _ _ (parallel_eval M A B).context_eval (parallel_eval M A B).identity_eval)
    (weaken_eval M env _ _ _ _ (parallel_eval M A B).context_eval (parallel_eval M A B).identity_eval)

theorem qFamily_eval : (Contextual.identity signature.withH.A signature.withH.y signature.withH.z).eval (Contextual.algebra M) env =
    .family (homotopyPoints M.toStructuralModel A B).context (qFamily M.toStructuralModel A B) :=
  identity_eval M env _ _ _ _ _ _ _ (homotopyPoints_eval M A B).family_eval
    (homotopyPoints_eval M A B).y_eval (homotopyPoints_eval M A B).z_eval

theorem qPoints_eval : PointsEvaluation M env signature.withQ.toPoints (qPoints M.toStructuralModel A B) :=
  (homotopyPoints_eval M A B).reindex signature.withH.hQ.weaken _ _
    (extend_eval M env _ _ _ _ (homotopyPoints_eval M A B).context_eval (qFamily_eval M A B))
    (weaken_eval M env _ _ _ _ (homotopyPoints_eval M A B).context_eval (qFamily_eval M A B))

theorem uFamily_eval : signature.withQ.uType.eval (Contextual.algebra M) env =
    .family (qPoints M.toStructuralModel A B).context (uFamily M.toStructuralModel A B) :=
  subTy_eval M env _ _ _ _ _ _ (qPoints_eval M A B).fiber_eval
    (sectionSub_eval M env _ _ _ _ _ _ (qPoints_eval M A B).context_eval
      (qPoints_eval M A B).family_eval (qPoints_eval M A B).x_eval)

theorem inputContext_eval : signature.input.Γ.eval (Contextual.algebra M) env =
    .context (inputContext M.toStructuralModel A B) :=
  extend_eval M env _ _ _ _ (qPoints_eval M A B).context_eval (uFamily_eval M A B)

theorem selectedHomotopy_eval : signature.input.h.eval (Contextual.algebra M) env =
    .term (inputContext M.toStructuralModel A B) _ (selectedHomotopy M.toStructuralModel A B) := by
  have h0 := generic_eval M env _ _ _ _ (parallel_eval M A B).context_eval
    (parallel_eval M A B).identity_eval
  have h1 := subTm_eval M env signature.withH.h _ _ _ _ _ _ h0
    (weaken_eval M env _ _ _ _ (homotopyPoints_eval M A B).context_eval (qFamily_eval M A B))
  exact subTm_eval M env signature.withQ.h _ _ _ _ _ _ h1
    (weaken_eval M env _ _ _ _ (qPoints_eval M A B).context_eval (uFamily_eval M A B))
end Examples.FrozenMemoStages
