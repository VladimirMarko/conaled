import SquareKit.Internal.DependentJudgments.ContextualRules

/-! Definitional and comprehension consequences used to assemble source J
recipes. None of these rules introduces transport or a path-composition axiom. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

abbrev sectionSub (Γ A x : Expression V) : Expression V := pair A (identitySub Γ) x
abbrev pathFamily (Γ A x : Expression V) : Expression V :=
  identity (subTy A (weaken Γ A)) (subTm x (weaken Γ A)) (generic Γ A)

abbrev pathDefRule := pointSchema (.eq (path (.var 1) (.var 2))
  (extend (extend (.var 0) (.var 1)) (pathFamily (.var 0) (.var 1) (.var 2))))

abbrev rootDefRule := pointSchema (.eq (root (.var 1) (.var 2))
  (pair (pathFamily (.var 0) (.var 1) (.var 2)) (sectionSub (.var 0) (.var 1) (.var 2))
    (reflexivity (.var 1) (.var 2))))

abbrev rootProjectionRule := pointSchema (.eq
  (comp (weaken (extend (.var 0) (.var 1)) (pathFamily (.var 0) (.var 1) (.var 2)))
    (root (.var 1) (.var 2))) (sectionSub (.var 0) (.var 1) (.var 2)))

abbrev rootTailNilRule := pointSchema (.eq
  (rootTail (.var 1) (.var 2) (telNil (path (.var 1) (.var 2)))) (root (.var 1) (.var 2)))

abbrev contextSchema (out : Judgment (Fin 1)) : Rule signature where
  parameterCount := 1
  hypotheses := 1
  premise := ![context (.var 0)]
  conclusion := out

theorem contextSchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 1))
    (h : ∀ Γ, out.eval (algebra M) ![.context Γ]) : Satisfies (algebra M) (contextSchema out) := by
  intro ρ hs
  rcases hs 0 with ⟨Γ, hΓ⟩
  have he : ρ = ![Value.context Γ] := by funext i; fin_cases i; exact hΓ
  subst ρ
  exact h Γ

abbrev totalNilRule := contextSchema (.eq (total (telNil (.var 0))) (.var 0))
abbrev pullbackNilRule := subSchema
  (.eq (pullback (telNil (.var 0)) (.var 2)) (telNil (.var 1)))

theorem totalNil_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) totalNilRule := by
  apply contextSchema_valid
  intro Γ
  rfl

theorem pullbackNil_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) pullbackNilRule := by
  apply subSchema_valid
  intro Γ Δ σ
  simp [Atom.eval, Term.eval, FinitaryTerm.fold, algebra, operation, Telescope.pullback, Telescope.reindex]

theorem rootTailNil_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) rootTailNilRule := by
  apply pointSchema_valid
  intro Γ A x
  simp [Atom.eval, Term.eval, FinitaryTerm.fold, algebra, operation, Telescope.pullback, Telescope.total, StructuralModel.rootTail, Telescope.liftSub, Telescope.reindex]

theorem pathDef_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) pathDefRule := by
  apply pointSchema_valid
  intro Γ A x
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, algebra, operation, DependentJudgments.operation,
    pathFamily, StructuralModel.pathContext, StructuralModel.pathFamily]

private theorem sectionSub_eval (M : PathTransport.Typed.Model.{u}) {V : Type}
    (ρ : V → Value M.toStructuralModel) (g a t : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (x : M.Section Γ A)
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (ht : t.eval (algebra M) ρ = .term Γ A x) :
    (sectionSub g a t).eval (algebra M) ρ = .substitution Γ (M.extend Γ A) (M.toStructuralModel.sectionSub A x) := by
  simp only [Term.eval, algebra] at hg ha ht
  simp only [identitySub, Term.eval, FinitaryTerm.fold, algebra,
    DependentJudgments.operation, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, hg, ha, ht, Value.substitutionAt_substitution]
  have hx : Value.term Γ A x = .term Γ (M.subTy A (M.idSub Γ))
      (cast (congrArg (M.Section Γ) (M.subTy_id A).symm) x) :=
    Value.term_eq (M.subTy_id A).symm (cast_heq _ _).symm
  rw [hx, Value.termAt_term]
  rfl

theorem rootProjection_valid (M : PathTransport.Typed.Model.{u}) :
    Satisfies (algebra M) rootProjectionRule := by
  apply pointSchema_valid
  intro Γ A x
  change Term.eval (algebra M) _ _ = _
  rw [sectionSub_eval M _ _ _ _ Γ A x rfl rfl rfl]
  simp [Term.eval, FinitaryTerm.fold, algebra, operation, DependentJudgments.operation,
    pathFamily, StructuralModel.pathContext, StructuralModel.pathFamily]
  exact M.toStructuralModel.weaken_root A x

theorem rootDef_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) rootDefRule := by
  apply pointSchema_valid
  intro Γ A x
  change Term.eval (algebra M) _ _ = _
  have hs := sectionSub_eval M (![Value.context Γ, .family Γ A, .term Γ A x])
    (.var 0) (.var 1) (.var 2) Γ A x rfl rfl rfl
  simp only [Term.eval, FinitaryTerm.fold, algebra, operation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, point_values, Id.run] at ⊢
  change Value.substitution Γ (M.pathContext A x) (M.rootSub A x) = _
  simp only [Term.eval, algebra] at hs
  simp only [DependentJudgments.operation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hs]
  simp only [Pure.pure, subTy, subTm, weaken, generic,
    FinitaryTerm.fold, operation, DependentJudgments.operation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    point_values, Id.run, Value.familyAt_family, Value.termIn_term, Value.termAt_term, Value.substitutionAt_substitution]
  have hx : Value.term (M := M.toStructuralModel) Γ (M.identity A x x) (M.reflexivity A x) =
      .term Γ (M.subTy (M.pathFamily A x) (M.sectionSub A x))
        (cast (congrArg (M.Section Γ) (M.pathFamily_root A x).symm) (M.reflexivity A x)) :=
    Value.term_eq (M.pathFamily_root A x).symm (cast_heq _ _).symm
  simp only [StructuralModel.pathFamily] at hx
  rw [hx, Value.termAt_term]
  rfl

end SquareKit.Internal.DependentJudgments.Contextual
