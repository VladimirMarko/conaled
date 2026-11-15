import SquareKit.Internal.DependentJudgments.NilReindexRules

namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

abbrev liftSyntax (Δ A σ : Expression V) : Expression V :=
  pair A (comp σ (weaken Δ (subTy A σ))) (generic Δ (subTy A σ))

theorem liftSyntax_eval (M : PathTransport.Typed.Model.{u}) {V : Type}
    (ρ : V → Value M.toStructuralModel) (g a s : Expression V)
    (Γ Δ : M.Context) (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (hg : g.eval (algebra M) ρ = .context Δ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hs : s.eval (algebra M) ρ = .substitution Δ Γ σ) :
    (liftSyntax g a s).eval (algebra M) ρ =
      .substitution (M.extend Δ (M.subTy A σ)) (M.extend Γ A) (M.lift A σ) := by
  simp only [Term.eval, algebra] at hg ha hs
  simp only [Term.eval, FinitaryTerm.fold, algebra, DependentJudgments.operation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    hg, ha, hs, Value.familyAt_family, Value.substitutionAt_substitution]
  have ht : Value.term (M := M.toStructuralModel) (M.extend Δ (M.subTy A σ))
      (M.subTy (M.subTy A σ) (M.weaken Δ (M.subTy A σ))) (M.genericVariable Δ (M.subTy A σ)) =
      .term (M.extend Δ (M.subTy A σ)) (M.subTy A (M.compSub σ (M.weaken Δ (M.subTy A σ))))
        (cast (congrArg (M.Section _) (M.subTy_comp A σ (M.weaken Δ (M.subTy A σ))))
          (M.genericVariable Δ (M.subTy A σ))) :=
    Value.term_eq (M.subTy_comp A σ (M.weaken Δ (M.subTy A σ))) (cast_heq _ _).symm
  rw [ht, Value.termAt_term]
  rfl

abbrev pathSubDefRule := termSubSchema (.eq
  (pathSub (.var 2) (.var 3) (.var 4))
  (pair (pathFamily (.var 0) (.var 2) (.var 3))
    (comp (liftSyntax (.var 1) (.var 2) (.var 4))
      (weaken (extend (.var 1) (subTy (.var 2) (.var 4)))
        (pathFamily (.var 1) (subTy (.var 2) (.var 4)) (subTm (.var 3) (.var 4)))))
    (generic (extend (.var 1) (subTy (.var 2) (.var 4)))
      (pathFamily (.var 1) (subTy (.var 2) (.var 4)) (subTm (.var 3) (.var 4))))))

theorem pathSubDef_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) pathSubDefRule := by
  apply termSubSchema_valid
  intro Γ Δ A x σ
  change Term.eval (algebra M) _ _ = _
  have hl := liftSyntax_eval M
    (![Value.context Γ, .context Δ, .family Γ A, .term Γ A x, .substitution Δ Γ σ])
    (.var 1) (.var 2) (.var 4) Γ Δ A σ rfl rfl rfl
  simp only [Term.eval, algebra] at hl
  simp only [Term.eval, FinitaryTerm.fold, algebra, operation, DependentJudgments.operation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, hl, point_values, Id.run, Pure.pure,
    Value.familyAt_family, Value.termIn_term, Value.termAt_term, Value.substitutionAt_substitution]
  have ht : Value.term (M := M.toStructuralModel)
      (M.pathContext (M.subTy A σ) (M.subTm x σ))
      (M.subTy (M.pathFamily (M.subTy A σ) (M.subTm x σ))
        (M.weaken _ (M.pathFamily (M.subTy A σ) (M.subTm x σ))))
      (M.genericVariable _ (M.pathFamily (M.subTy A σ) (M.subTm x σ))) =
      .term (M.pathContext (M.subTy A σ) (M.subTm x σ))
        (M.subTy (M.pathFamily A x)
          (M.compSub (M.lift A σ) (M.weaken _ (M.pathFamily (M.subTy A σ) (M.subTm x σ)))))
        (cast (congrArg (M.Section _) (M.pathSub_type A x σ).symm)
          (M.genericVariable _ (M.pathFamily (M.subTy A σ) (M.subTm x σ)))) :=
    Value.term_eq (M.pathSub_type A x σ).symm (cast_heq _ _).symm
  simp only [StructuralModel.pathContext, StructuralModel.pathFamily] at ht
  rw [ht, Value.termAt_term]
  rfl

end SquareKit.Internal.DependentJudgments.Contextual
