import SquareKit.Internal.DependentJudgments.Sigma.Operations

/-! Constructor admission is proved from the operation laws. Ordinary source
clients do not provide instances of Satisfies or reprove constructor coherence. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u
variable (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel)

local macro "eval_simp" : tactic => `(tactic|
  simp [Term.eval, algebra, operation, Contextual.algebra, DependentJudgments.operation])

theorem formation_valid : Satisfies (algebra M S) formationRule := by
  apply formationSchema_valid
  intro Γ A B
  refine ⟨Γ, S.sigma A B, rfl, ?_⟩
  eval_simp

theorem pack_valid : Satisfies (algebra M S) packRule := by
  apply formationSchema_valid
  intro Γ A B
  refine ⟨M.extend (M.extend Γ A) B, M.extend Γ (S.sigma A B), S.pack A B, ?_, ?_, ?_⟩ <;>
    eval_simp

theorem unpack_valid : Satisfies (algebra M S) unpackRule := by
  apply formationSchema_valid
  intro Γ A B
  refine ⟨M.extend Γ (S.sigma A B), M.extend (M.extend Γ A) B, S.unpack A B, ?_, ?_, ?_⟩ <;>
    eval_simp

theorem beta_valid : Satisfies (algebra M S) betaRule := by
  apply formationSchema_valid
  intro Γ A B
  change (comp (unpack (.var 1) (.var 2)) (pack (.var 1) (.var 2))).eval _ _ = _
  simpa [Term.eval, algebra, operation, Contextual.algebra, DependentJudgments.operation]
    using congrArg (Value.substitution _ _) (S.unpack_pack A B)

theorem eta_valid : Satisfies (algebra M S) etaRule := by
  apply formationSchema_valid
  intro Γ A B
  change (comp (pack (.var 1) (.var 2)) (unpack (.var 1) (.var 2))).eval _ _ = _
  simpa [Term.eval, algebra, operation, Contextual.algebra, DependentJudgments.operation]
    using congrArg (Value.substitution _ _) (S.pack_unpack A B)

theorem packOver_valid : Satisfies (algebra M S) packOverRule := by
  apply formationSchema_valid
  intro Γ A B
  change (comp (weaken (.var 0) (sigma (.var 1) (.var 2))) (pack (.var 1) (.var 2))).eval _ _ = _
  simpa [Term.eval, algebra, operation, Contextual.algebra, DependentJudgments.operation]
    using congrArg (Value.substitution _ _) (S.pack_over A B)

/-- Inversion of the eliminator guards recovers a motive depending on the
whole sum value and a branch in its pullback along packing. -/
theorem splitSchema_inputs (out : Judgment (Fin 5)) (ρ : Fin 5 → Value M.toStructuralModel)
    (h : ∀ i, ((splitSchema out).premise i).eval (algebra M S) ρ) :
    ∃ (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
      (C : M.Family (M.extend Γ (S.sigma A B)))
      (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))),
      ρ = ![.context Γ, .family Γ A, .family (M.extend Γ A) B,
        .family (M.extend Γ (S.sigma A B)) C,
        .term (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)) d] := by
  let ρ₀ : Fin 3 → Value M.toStructuralModel := fun i => ρ (i.castAdd 2)
  have h₀ : ∀ i, (formationRule.premise i).eval (algebra M S) ρ₀ := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1
  rcases formationSchema_inputs M S _ ρ₀ h₀ with ⟨Γ, A, B, e⟩
  have hΓ := congrFun e 0
  have hA := congrFun e 1
  have hB := congrFun e 2
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  change ρ 2 = .family (M.extend Γ A) B at hB
  have hSum : (extend (.var 0) (sigma (.var 1) (.var 2))).eval (algebra M S) ρ =
      .context (M.extend Γ (S.sigma A B)) := by
    simp [Term.eval, algebra, operation, Contextual.algebra, DependentJudgments.operation, hΓ, hA, hB]
  have hc := h 2
  change ∃ Γ' C, (extend (.var 0) (sigma (.var 1) (.var 2))).eval (algebra M S) ρ =
    .context Γ' ∧ ρ 3 = .family Γ' C at hc
  rw [hSum] at hc
  rcases hc with ⟨Γ', C, eΓ, hC⟩
  have eΓ' := Value.context.inj eΓ
  subst Γ'
  have he : (branchContext (.var 0) (.var 1) (.var 2)).eval (algebra M S) ρ =
      .context (M.extend (M.extend Γ A) B) := by
    simp [Term.eval, algebra, Contextual.algebra, DependentJudgments.operation, hΓ, hA, hB]
  have ht : (subTy (.var 3) (pack (.var 1) (.var 2))).eval (algebra M S) ρ =
      .family (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)) := by
    simp [Term.eval, algebra, operation, Contextual.algebra, DependentJudgments.operation, hA, hB, hC]
  have hd := h 3
  change ∃ Γ' D d, (branchContext (.var 0) (.var 1) (.var 2)).eval (algebra M S) ρ = .context Γ' ∧
    (subTy (.var 3) (pack (.var 1) (.var 2))).eval (algebra M S) ρ = .family Γ' D ∧
    ρ 4 = .term Γ' D d at hd
  rw [he, ht] at hd
  rcases hd with ⟨Γ', D, d, eΓ, eD, hd⟩
  have eΓ' := Value.context.inj eΓ
  subst Γ'
  have eD' := eq_of_heq (Value.family.inj eD).2
  subst D
  refine ⟨Γ, A, B, C, d, ?_⟩
  funext i
  fin_cases i <;> first | exact hΓ | exact hA | exact hB | exact hC | exact hd

theorem splitSchema_valid (out : Judgment (Fin 5))
    (valid : ∀ (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
      (C : M.Family (M.extend Γ (S.sigma A B)))
      (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))),
      out.eval (algebra M S) ![.context Γ, .family Γ A, .family (M.extend Γ A) B,
        .family (M.extend Γ (S.sigma A B)) C,
        .term (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)) d]) :
    Satisfies (algebra M S) (splitSchema out) := by
  intro ρ h
  rcases splitSchema_inputs M S out ρ h with ⟨Γ, A, B, C, d, rfl⟩
  exact valid Γ A B C d

theorem split_valid : Satisfies (algebra M S) splitRule := by
  apply splitSchema_valid
  intro Γ A B C d
  refine ⟨M.extend Γ (S.sigma A B), C, S.split A B C d, ?_, rfl, ?_⟩
  · eval_simp
  · simp only [Term.eval, FinitaryTerm.fold, algebra, Contextual.algebra,
      DependentJudgments.operation, operation, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ, inputs_values,
      Value.termIn_term]
    exact Value.term_eq (S.split_type A B C) (S.split_heq A B C d).symm

theorem splitBeta_valid : Satisfies (algebra M S) splitBetaRule := by
  apply splitSchema_valid
  intro Γ A B C d
  change (subTm (split (.var 1) (.var 2) (.var 4)) (pack (.var 1) (.var 2))).eval _ _ = _
  simp only [Term.eval, FinitaryTerm.fold, algebra, Contextual.algebra,
    DependentJudgments.operation, operation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ, inputs_values,
    Value.termIn_term]
  apply Value.term_eq
  · rw [M.subTy_comp, S.unpack_pack, M.subTy_id]
  · apply (M.subTm_comp _ _ _).trans
    rw [S.unpack_pack]
    exact M.subTm_id d

end SquareKit.Internal.DependentJudgments.Sigma
