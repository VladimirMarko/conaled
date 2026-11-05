import SquareKit.Internal.DependentJudgments.Theory

/-! Substitution equations for the source constructors. These normalize raw
syntax only; semantic transports are absent from the statement and proof. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
set_option backward.isDefEq.respectTransparency false
open GuardedTheory
variable {V W : Type}

@[simp] theorem subst_var (v : V) (σ : V → Expression W) :
    (Term.var v : Expression V).subst σ = σ v := rfl

@[simp] theorem inl_var (v : V) :
    (Term.var v : DependentJudgments.Expression V).inl extraSignature = Term.var v := rfl

@[simp] theorem subst_eq (a b : Expression V) (σ : V → Expression W) :
    (Atom.eq a b).subst σ = Atom.eq (a.subst σ) (b.subst σ) := rfl

@[simp] theorem subst_context (a0 : Expression V) (σ : V → Expression W) :
    (context a0).subst σ = context (a0.subst σ) := by
  apply congrArg (Atom.pred (S := signature) (Sum.inl DependentJudgments.Predicate.context))
  funext i
  fin_cases i; rfl

@[simp] theorem subst_family (a0 a1 : Expression V) (σ : V → Expression W) :
    (family a0 a1).subst σ = family (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Atom.pred (S := signature) (Sum.inl DependentJudgments.Predicate.family))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_term (a0 a1 a2 : Expression V) (σ : V → Expression W) :
    (term a0 a1 a2).subst σ = term (a0.subst σ) (a1.subst σ) (a2.subst σ) := by
  apply congrArg (Atom.pred (S := signature) (Sum.inl DependentJudgments.Predicate.term))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_substitution (a0 a1 a2 : Expression V) (σ : V → Expression W) :
    (substitution a0 a1 a2).subst σ = substitution (a0.subst σ) (a1.subst σ) (a2.subst σ) := by
  apply congrArg (Atom.pred (S := signature) (Sum.inl DependentJudgments.Predicate.substitution))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_telescope (n : Nat) (a0 a1 : Expression V) (σ : V → Expression W) :
    (telescope n a0 a1).subst σ = telescope n (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Atom.pred (S := signature) (Sum.inr (Predicate.telescope n)))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_empty (σ : V → Expression W) :
    (empty).subst σ = empty := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.empty))
  funext i
  exact Fin.elim0 i

@[simp] theorem subst_extend (a0 a1 : Expression V) (σ : V → Expression W) :
    (extend a0 a1).subst σ = extend (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.extend))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_identitySub (a0 : Expression V) (σ : V → Expression W) :
    (identitySub a0).subst σ = identitySub (a0.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.id))
  funext i
  fin_cases i; rfl

@[simp] theorem subst_comp (a0 a1 : Expression V) (σ : V → Expression W) :
    (comp a0 a1).subst σ = comp (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.comp))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_subTy (a0 a1 : Expression V) (σ : V → Expression W) :
    (subTy a0 a1).subst σ = subTy (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.subTy))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_subTm (a0 a1 : Expression V) (σ : V → Expression W) :
    (subTm a0 a1).subst σ = subTm (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.subTm))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_weaken (a0 a1 : Expression V) (σ : V → Expression W) :
    (weaken a0 a1).subst σ = weaken (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.weaken))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_generic (a0 a1 : Expression V) (σ : V → Expression W) :
    (generic a0 a1).subst σ = generic (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.generic))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_pair (a0 a1 a2 : Expression V) (σ : V → Expression W) :
    (pair a0 a1 a2).subst σ = pair (a0.subst σ) (a1.subst σ) (a2.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.pair))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_identity (a0 a1 a2 : Expression V) (σ : V → Expression W) :
    (identity a0 a1 a2).subst σ = identity (a0.subst σ) (a1.subst σ) (a2.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.identity))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_reflexivity (a0 a1 : Expression V) (σ : V → Expression W) :
    (reflexivity a0 a1).subst σ = reflexivity (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.reflexivity))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_path (a0 a1 : Expression V) (σ : V → Expression W) :
    (path a0 a1).subst σ = path (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.path))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_root (a0 a1 : Expression V) (σ : V → Expression W) :
    (root a0 a1).subst σ = root (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.root))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_telNil (a0 : Expression V) (σ : V → Expression W) :
    (telNil a0).subst σ = telNil (a0.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.telNil))
  funext i
  fin_cases i; rfl

@[simp] theorem subst_telCons (a0 a1 : Expression V) (σ : V → Expression W) :
    (telCons a0 a1).subst σ = telCons (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.telCons))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_total (a0 : Expression V) (σ : V → Expression W) :
    (total a0).subst σ = total (a0.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.total))
  funext i
  fin_cases i; rfl

@[simp] theorem subst_projection (a0 : Expression V) (σ : V → Expression W) :
    (projection a0).subst σ = projection (a0.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.projection))
  funext i
  fin_cases i; rfl

@[simp] theorem subst_pullback (a0 a1 : Expression V) (σ : V → Expression W) :
    (pullback a0 a1).subst σ = pullback (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.pullback))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_tailMap (a0 a1 : Expression V) (σ : V → Expression W) :
    (tailMap a0 a1).subst σ = tailMap (a0.subst σ) (a1.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.tailMap))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_rootTail (a0 a1 a2 : Expression V) (σ : V → Expression W) :
    (rootTail a0 a1 a2).subst σ = rootTail (a0.subst σ) (a1.subst σ) (a2.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.rootTail))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_pathSub (a0 a1 a2 : Expression V) (σ : V → Expression W) :
    (pathSub a0 a1 a2).subst σ = pathSub (a0.subst σ) (a1.subst σ) (a2.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.pathSub))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_pathTail (a0 a1 a2 a3 : Expression V) (σ : V → Expression W) :
    (pathTail a0 a1 a2 a3).subst σ = pathTail (a0.subst σ) (a1.subst σ) (a2.subst σ) (a3.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.pathTail))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_pathTailMap (a0 a1 a2 a3 : Expression V) (σ : V → Expression W) :
    (pathTailMap a0 a1 a2 a3).subst σ = pathTailMap (a0.subst σ) (a1.subst σ) (a2.subst σ) (a3.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.pathTailMap))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_branchMap (a0 a1 a2 a3 : Expression V) (σ : V → Expression W) :
    (branchMap a0 a1 a2 a3).subst σ = branchMap (a0.subst σ) (a1.subst σ) (a2.subst σ) (a3.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.branchMap))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_reindexBranch (a0 a1 a2 a3 a4 a5 : Expression V) (σ : V → Expression W) :
    (reindexBranch a0 a1 a2 a3 a4 a5).subst σ = reindexBranch (a0.subst σ) (a1.subst σ) (a2.subst σ) (a3.subst σ) (a4.subst σ) (a5.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.reindexBranch))
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_j (a0 a1 a2 a3 a4 : Expression V) (σ : V → Expression W) :
    (j a0 a1 a2 a3 a4).subst σ = j (a0.subst σ) (a1.subst σ) (a2.subst σ) (a3.subst σ) (a4.subst σ) := by
  apply congrArg (Term.app (S := signature) (Sum.inr Operation.j))
  funext i
  fin_cases i <;> rfl

@[simp] theorem inl_context (a0 : DependentJudgments.Expression V) :
    (DependentJudgments.context a0).inl extraSignature = context (a0.inl extraSignature) := by
  apply congrArg (Atom.pred (S := signature) (Sum.inl DependentJudgments.Predicate.context))
  funext i
  fin_cases i; rfl

@[simp] theorem inl_family (a0 a1 : DependentJudgments.Expression V) :
    (DependentJudgments.family a0 a1).inl extraSignature = family (a0.inl extraSignature) (a1.inl extraSignature) := by
  apply congrArg (Atom.pred (S := signature) (Sum.inl DependentJudgments.Predicate.family))
  funext i
  fin_cases i <;> rfl

@[simp] theorem inl_term (a0 a1 a2 : DependentJudgments.Expression V) :
    (DependentJudgments.term a0 a1 a2).inl extraSignature = term (a0.inl extraSignature) (a1.inl extraSignature) (a2.inl extraSignature) := by
  apply congrArg (Atom.pred (S := signature) (Sum.inl DependentJudgments.Predicate.term))
  funext i
  fin_cases i <;> rfl

@[simp] theorem inl_substitution (a0 a1 a2 : DependentJudgments.Expression V) :
    (DependentJudgments.substitution a0 a1 a2).inl extraSignature = substitution (a0.inl extraSignature) (a1.inl extraSignature) (a2.inl extraSignature) := by
  apply congrArg (Atom.pred (S := signature) (Sum.inl DependentJudgments.Predicate.substitution))
  funext i
  fin_cases i <;> rfl

@[simp] theorem inl_empty  :
    (DependentJudgments.empty (V := V)).inl extraSignature = empty := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.empty))
  funext i
  exact Fin.elim0 i

@[simp] theorem inl_extend (a0 a1 : DependentJudgments.Expression V) :
    (DependentJudgments.extend a0 a1).inl extraSignature = extend (a0.inl extraSignature) (a1.inl extraSignature) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.extend))
  funext i
  fin_cases i <;> rfl

@[simp] theorem inl_identitySub (a0 : DependentJudgments.Expression V) :
    (DependentJudgments.identitySub a0).inl extraSignature = identitySub (a0.inl extraSignature) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.id))
  funext i
  fin_cases i; rfl

@[simp] theorem inl_comp (a0 a1 : DependentJudgments.Expression V) :
    (DependentJudgments.comp a0 a1).inl extraSignature = comp (a0.inl extraSignature) (a1.inl extraSignature) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.comp))
  funext i
  fin_cases i <;> rfl

@[simp] theorem inl_subTy (a0 a1 : DependentJudgments.Expression V) :
    (DependentJudgments.subTy a0 a1).inl extraSignature = subTy (a0.inl extraSignature) (a1.inl extraSignature) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.subTy))
  funext i
  fin_cases i <;> rfl

@[simp] theorem inl_subTm (a0 a1 : DependentJudgments.Expression V) :
    (DependentJudgments.subTm a0 a1).inl extraSignature = subTm (a0.inl extraSignature) (a1.inl extraSignature) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.subTm))
  funext i
  fin_cases i <;> rfl

@[simp] theorem inl_weaken (a0 a1 : DependentJudgments.Expression V) :
    (DependentJudgments.weaken a0 a1).inl extraSignature = weaken (a0.inl extraSignature) (a1.inl extraSignature) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.weaken))
  funext i
  fin_cases i <;> rfl

@[simp] theorem inl_generic (a0 a1 : DependentJudgments.Expression V) :
    (DependentJudgments.generic a0 a1).inl extraSignature = generic (a0.inl extraSignature) (a1.inl extraSignature) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.generic))
  funext i
  fin_cases i <;> rfl

@[simp] theorem inl_pair (a0 a1 a2 : DependentJudgments.Expression V) :
    (DependentJudgments.pair a0 a1 a2).inl extraSignature = pair (a0.inl extraSignature) (a1.inl extraSignature) (a2.inl extraSignature) := by
  apply congrArg (Term.app (S := signature) (Sum.inl DependentJudgments.Operation.pair))
  funext i
  fin_cases i <;> rfl

end SquareKit.Internal.DependentJudgments.Contextual
