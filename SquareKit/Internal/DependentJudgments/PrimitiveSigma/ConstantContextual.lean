import SquareKit.Internal.DependentJudgments.PrimitiveSigma.ConstantFamilies

/-! Contextual J in the constant-family interpretation. Every finite tail is
retained while the endpoint and its indiscrete identity witness are forgotten. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma.ConstantFamilies
open PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u
variable (Base : Type u)
local notation "M" => structuralModel Base

/-- Change the base of a constant-family telescope, retaining every tail entry. -/
def reverse {Γ Δ : (M).Context} {n} (T : Telescope M Γ n)
    (σ : (M).Substitution Δ Γ) (f : Γ → Δ) : T.total → (Telescope.pullback M T σ).total :=
  match T with
  | .nil => f
  | .cons A tail => reverse tail ((M).lift A σ) (fun p => (f p.1, p.2))

theorem reverse_lift {Γ Δ : (M).Context} {n} (T : Telescope M Γ n)
    (σ : (M).Substitution Δ Γ) (f : Γ → Δ) (h : ∀ d, f (σ.down d) = d)
    (d : (Telescope.pullback M T σ).total) : reverse Base T σ f ((Telescope.liftSub M T σ).down d) = d :=
  match n, Γ, T with
  | _, _, .nil => h d
  | _, _, .cons A tail =>
    reverse_lift tail ((M).lift A σ) (fun p => (f p.1, p.2))
      (fun p => Prod.ext (h p.1) rfl) d

theorem reverse_square {Γ Γ' Δ Δ' : (M).Context} {n}
    (T : Telescope M Γ n) (F : (M).Substitution Δ Γ) (F' : (M).Substitution Δ' Γ')
    (K : (M).Substitution Γ' Γ) (L : (M).Substitution Δ' Δ)
    (h : (M).compSub K F' = (M).compSub F L)
    (r : Γ → Δ) (r' : Γ' → Δ') (hr : ∀ g, r (K.down g) = L.down (r' g))
    (g : (Telescope.pullback M T K).total) :
    reverse Base T F r ((Telescope.liftSub M T K).down g) =
      (Telescope.square M F F' K L h T).val.down (reverse Base (Telescope.pullback M T K) F' r' g) :=
  match n, Γ, T with
  | _, _, .nil => by simpa only [Telescope.square, reverse, Telescope.liftSub, Telescope.pullback, Telescope.reindex] using hr g
  | _, _, .cons A tail => by
    simpa only [Telescope.square, reverse, Telescope.liftSub, Telescope.pullback, Telescope.reindex] using reverse_square tail ((M).lift A F) ((M).lift ((M).subTy A K) F') ((M).lift A K)
      ((M).squareLift F F' K L h A) ((M).squareLift_forward F F' K L h A)
      (fun p => (r p.1, p.2)) (fun p => (r' p.1, p.2))
      (fun p => Prod.ext (hr p.1) rfl) g

def contextualJ {Γ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : Telescope M ((M).pathContext A x) n) (C : (M).Family T.total)
    (d : (M).Section (Telescope.pullback M T ((M).rootSub A x)).total C) : (M).Section T.total C :=
  ⟨fun p => d.down (reverse Base T ((M).rootSub A x) (fun g => g.1.1) p)⟩

theorem contextualJ_beta {Γ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : Telescope M ((M).pathContext A x) n) (C : (M).Family T.total)
    (d : (M).Section (Telescope.pullback M T ((M).rootSub A x)).total C) :
    HEq ((M).subTm (contextualJ Base A x T C d) ((M).rootTail A x T)) d := by
  apply heq_of_eq
  apply ULift.ext
  funext p
  exact congrArg d.down (reverse_lift Base T ((M).rootSub A x) (fun g => g.1.1) (fun _ => rfl) p)

theorem contextualJ_sub {Γ Δ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : Telescope M ((M).pathContext A x) n) (C : (M).Family T.total)
    (d : (M).Section (Telescope.pullback M T ((M).rootSub A x)).total C) (σ : (M).Substitution Δ Γ) :
    HEq ((M).subTm (contextualJ Base A x T C d) ((M).pathTailMap A x T σ))
      (contextualJ Base ((M).subTy A σ) ((M).subTm x σ) ((M).pathTail A x T σ)
        ((M).subTy C ((M).pathTailMap A x T σ)) ((M).reindexBranch A x T σ C d)) := by
  apply heq_of_eq
  apply ULift.ext
  funext p
  apply congrArg d.down
  exact reverse_square Base T ((M).rootSub A x)
    ((M).rootSub ((M).subTy A σ) ((M).subTm x σ)) ((M).pathSub A x σ) σ
    ((M).pathSub_root A x σ) (fun g => g.1.1) (fun g => g.1.1) (fun _ => rfl) p

def model : Model.{u+1} where
  toStructuralModel := M
  j := contextualJ Base
  j_beta := contextualJ_beta Base
  j_sub := contextualJ_sub Base

end SquareKit.Internal.DependentJudgments.PrimitiveSigma.ConstantFamilies
