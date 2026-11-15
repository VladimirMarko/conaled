import SquareKit.Internal.DependentJudgments.LeftConcatRecipe
import SquareKit.Internal.DependentJudgments.DerivedPathSemantics

/-! Evaluation of the generated first-path recipe. The premises describe the
actual dependent telescope, retained branch and argument substitution; the
conclusion retains the model's selected J operation. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.LeftSemantics
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false

universe u
variable (M : PathTransport.Typed.Model.{u}) {V : Type}
variable (ρ : V → Value M.toStructuralModel)

theorem j_eval (a x t d b : Expression V) (Γ : M.Context)
    (A : M.Family Γ) (v : M.Section Γ A) {n : Nat}
    (T : Telescope M.toStructuralModel (M.toStructuralModel.pathContext A v) n)
    (D : M.Family T.total)
    (branch : M.Section (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A v)).total
      (M.subTy D (M.toStructuralModel.rootTail A v T)))
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hx : x.eval (algebra M) ρ = .term Γ A v)
    (ht : t.eval (algebra M) ρ = .telescope (M.toStructuralModel.pathContext A v) n T)
    (hd : d.eval (algebra M) ρ = .family T.total D)
    (hb : b.eval (algebra M) ρ = .term (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A v)).total
      (M.subTy D (M.toStructuralModel.rootTail A v T)) branch) :
    (j a x t d b).eval (algebra M) ρ = .term T.total D (M.j A v T D branch) := by
  change operation M .j ![a.eval (algebra M) ρ, x.eval (algebra M) ρ,
    t.eval (algebra M) ρ, d.eval (algebra M) ρ, b.eval (algebra M) ρ] = _
  rw [ha, hx, ht, hd, hb]
  simp [operation]

/-- Evaluation of the actual guarded recipe, with two dependent tail entries.
The branch premise refers to the retained q through its root-tail map. -/
theorem leftConcat_eval (g a x y z p q : Expression V) (Γ : M.Context)
    (A : M.Family Γ) (v : M.Section Γ A)
    (T : Telescope M.toStructuralModel (M.toStructuralModel.pathContext A v) 2)
    (D : M.Family T.total)
    (branch : M.Section (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A v)).total
      (M.subTy D (M.toStructuralModel.rootTail A v T)))
    (σ : M.Substitution Γ T.total)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hx : x.eval (algebra M) ρ = .term Γ A v)
    (ht : ((LeftConcatFrame.tail g a x).code (path a x)).eval (algebra M) ρ =
      .telescope (M.toStructuralModel.pathContext A v) 2 T)
    (hd : (LeftConcatFrame.motive g a x).eval (algebra M) ρ = .family T.total D)
    (hb : (subTm (LeftConcatFrame.q g a x) ((LeftConcatFrame.tail g a x).map g (root a x))).eval
      (algebra M) ρ = .term (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A v)).total
        (M.subTy D (M.toStructuralModel.rootTail A v T)) branch)
    (hs : (LeftConcatArguments.atQ g a x y z p q).eval (algebra M) ρ =
      .substitution Γ T.total σ) :
    (leftConcat g a x y z p q).eval (algebra M) ρ =
      .term Γ (M.subTy D σ) (M.subTm (M.j A v T D branch) σ) :=
  DerivedSemantics.subTm_eval M ρ _ _ _ _ _ _ _
    (j_eval M ρ _ _ _ _ _ Γ A v T D branch ha hx ht hd hb) hs
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.LeftSemantics
