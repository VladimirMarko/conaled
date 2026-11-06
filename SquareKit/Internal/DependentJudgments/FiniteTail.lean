import SquareKit.Internal.DependentJudgments.TelescopePresentation

/-! Finite lists of dependent declarations. Binding is contextual: each next
family is checked over the context extended by the preceding declarations. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
variable {V : Type}

inductive Tail (V : Type) where
  | nil : Tail V
  | cons (A : Expression V) (rest : Tail V) : Tail V

namespace Tail

def length : Tail V → Nat
  | .nil => 0
  | .cons _ rest => rest.length + 1

def total (Γ : Expression V) : Tail V → Expression V
  | .nil => Γ
  | .cons A rest => rest.total (extend Γ A)

def code (Γ : Expression V) : Tail V → Expression V
  | .nil => telNil Γ
  | .cons A rest => telCons A (rest.code (extend Γ A))

def projection (Γ : Expression V) : Tail V → Expression V
  | .nil => identitySub Γ
  | .cons A rest => comp (weaken Γ A) (rest.projection (extend Γ A))

/-- Object substitution traverses the declarations and lifts the substitution
through each binder. It is distinct from schematic instantiation of leaves. -/
def reindex (Δ σ : Expression V) : Tail V → Tail V
  | .nil => .nil
  | .cons A rest => .cons (subTy A σ)
      (rest.reindex (extend Δ (subTy A σ)) (liftSyntax Δ A σ))

def map (Δ σ : Expression V) : Tail V → Expression V
  | .nil => σ
  | .cons A rest => rest.map (extend Δ (subTy A σ)) (liftSyntax Δ A σ)

def alongPath (T : Tail V) (A x σ : Expression V) : Tail V :=
  T.reindex (path (subTy A σ) (subTm x σ)) (pathSub A x σ)

def alongPathMap (T : Tail V) (A x σ : Expression V) : Expression V :=
  T.map (path (subTy A σ) (subTm x σ)) (pathSub A x σ)

def rootDomain (T : Tail V) (Γ A x : Expression V) : Expression V :=
  (T.reindex Γ (root A x)).total Γ

@[simp] theorem reindex_length (T : Tail V) (Δ σ : Expression V) :
    (T.reindex Δ σ).length = T.length := by
  induction T generalizing Δ σ with
  | nil => rfl
  | cons A T ih => simp only [reindex, length, ih]

def instantiate {W : Type} (θ : V → Expression W) : Tail V → Tail W
  | .nil => .nil
  | .cons A rest => .cons (A.subst θ) (rest.instantiate θ)

@[simp] theorem instantiate_total {W : Type} (θ : V → Expression W)
    (Γ : Expression V) (T : Tail V) :
    (T.instantiate θ).total (Γ.subst θ) = (T.total Γ).subst θ := by
  induction T generalizing Γ with
  | nil => rfl
  | cons A T ih => simp only [instantiate, total, ← subst_extend, ih]

@[simp] theorem instantiate_code {W : Type} (θ : V → Expression W)
    (Γ : Expression V) (T : Tail V) :
    (T.instantiate θ).code (Γ.subst θ) = (T.code Γ).subst θ := by
  induction T generalizing Γ with
  | nil => simp only [instantiate, code, subst_telNil]
  | cons A T ih => simp only [instantiate, code, ← subst_extend, ih, subst_telCons]

end Tail
end SquareKit.Internal.DependentJudgments.Contextual.Reference
