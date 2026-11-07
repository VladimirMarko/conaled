import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Syntax

/-! Raw substitution through the primitive pair constructors. These syntax
identities do not assert semantic stability of an object-language substitution. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma
open GuardedTheory
variable {V W : Type}
@[simp] theorem subst_var (v : V) (σ : V → Expression W) :
    (Term.var v : Expression V).subst σ = σ v := rfl
@[simp] theorem subst_eq (a b : Expression V) (σ : V → Expression W) :
    (Atom.eq a b).subst σ = Atom.eq (a.subst σ) (b.subst σ) := rfl

@[simp] theorem subst_family (a0 a1 : Expression V) (σ : V → Expression W) :
    (family a0 a1).subst σ = family (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Atom.pred (S := signature) (.inl (.inl .family)))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_term (a0 a1 a2 : Expression V) (σ : V → Expression W) :
    (term a0 a1 a2).subst σ = term (a0.subst σ) (a1.subst σ) (a2.subst σ) := by
  apply congrArg (Atom.pred (S := signature) (.inl (.inl .term)))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_extend (a0 a1 : Expression V) (σ : V → Expression W) :
    (extend a0 a1).subst σ = extend (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inl (.inl .extend)))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_sigma (a0 a1 : Expression V) (σ : V → Expression W) :
    (sigma a0 a1).subst σ = sigma (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inr .sigma))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_pack (a0 a1 : Expression V) (σ : V → Expression W) :
    (pack a0 a1).subst σ = pack (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inr .pack))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_split (a0 a1 a2 a3 : Expression V) (σ : V → Expression W) :
    (split a0 a1 a2 a3).subst σ = split (a0.subst σ) (a1.subst σ) (a2.subst σ) (a3.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inr .split))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_subTy (a0 a1 : Expression V) (σ : V → Expression W) :
    (subTy a0 a1).subst σ = subTy (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inl (.inl .subTy)))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_subTm (a0 a1 : Expression V) (σ : V → Expression W) :
    (subTm a0 a1).subst σ = subTm (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inl (.inl .subTm)))
  funext i
  fin_cases i <;> rfl

end SquareKit.Internal.DependentJudgments.PrimitiveSigma
