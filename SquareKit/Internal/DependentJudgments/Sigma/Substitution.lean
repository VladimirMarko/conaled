import SquareKit.Internal.DependentJudgments.Sigma.Theory

/-! Raw source substitution commutes with each constructor expression. These
syntax identities do not replace semantic substitution laws. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open GuardedTheory
variable {V W : Type}
@[simp] theorem subst_var (v : V) (σ : V → Expression W) :
    (Term.var v : Expression V).subst σ = σ v := rfl
@[simp] theorem subst_eq (a b : Expression V) (σ : V → Expression W) :
    (Atom.eq a b).subst σ = Atom.eq (a.subst σ) (b.subst σ) := rfl

@[simp] theorem subst_context (a0 : Expression V) (σ : V → Expression W) :
    (context a0).subst σ = context (a0.subst σ) := by
  apply congrArg (Atom.pred (S := signature) (.inl (.inl .context)))
  funext i
  fin_cases i ; rfl

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

@[simp] theorem subst_substitution (a0 a1 a2 : Expression V) (σ : V → Expression W) :
    (substitution a0 a1 a2).subst σ = substitution (a0.subst σ) (a1.subst σ) (a2.subst σ) := by
  apply congrArg (Atom.pred (S := signature) (.inl (.inl .substitution)))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_extend (a0 a1 : Expression V) (σ : V → Expression W) :
    (extend a0 a1).subst σ = extend (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inl (.inl .extend)))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_identitySub (a0 : Expression V) (σ : V → Expression W) :
    (identitySub a0).subst σ = identitySub (a0.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inl (.inl .id)))
  funext i
  fin_cases i ; rfl

@[simp] theorem subst_comp (a0 a1 : Expression V) (σ : V → Expression W) :
    (comp a0 a1).subst σ = comp (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inl (.inl .comp)))
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

@[simp] theorem subst_weaken (a0 a1 : Expression V) (σ : V → Expression W) :
    (weaken a0 a1).subst σ = weaken (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inl (.inl .weaken)))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_generic (a0 a1 : Expression V) (σ : V → Expression W) :
    (generic a0 a1).subst σ = generic (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inl (.inl .generic)))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_pairSub (a0 a1 a2 : Expression V) (σ : V → Expression W) :
    (pairSub a0 a1 a2).subst σ = pairSub (a0.subst σ) (a1.subst σ) (a2.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inl (.inl .pair)))
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

@[simp] theorem subst_unpack (a0 a1 : Expression V) (σ : V → Expression W) :
    (unpack a0 a1).subst σ = unpack (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (.inr .unpack))
  funext i
  fin_cases i <;> rfl

end SquareKit.Internal.DependentJudgments.Sigma
