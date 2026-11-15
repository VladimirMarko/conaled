import SquareKit.Internal.DependentJudgments.Sigma.Authoring

/-! A second rule extension adds dependent elimination uniqueness as a law of
existing operations. Its model is constructed from the selected Sigma laws;
no independent law is required from the model builder or proof author. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u

abbrev splitEtaRule : Rule signature where
  parameterCount := 5
  hypotheses := 4
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2),
    family (extend (.var 0) (sigma (.var 1) (.var 2))) (.var 3),
    term (extend (.var 0) (sigma (.var 1) (.var 2))) (.var 3) (.var 4)]
  conclusion := .eq (split (.var 1) (.var 2) (subTm (.var 4) (pack (.var 1) (.var 2)))) (.var 4)

theorem splitEta_valid (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel) :
    Satisfies (algebra M S) splitEtaRule := by
  intro ρ h
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
  have he : (extend (.var 0) (sigma (.var 1) (.var 2))).eval (algebra M S) ρ =
      .context (M.extend Γ (S.sigma A B)) := by
    simp [Term.eval, algebra, operation, Contextual.algebra, DependentJudgments.operation, hΓ, hA, hB]
  have ht := h 3
  change ∃ Γ' C t, (extend (.var 0) (sigma (.var 1) (.var 2))).eval (algebra M S) ρ =
    .context Γ' ∧ ρ 3 = .family Γ' C ∧ ρ 4 = .term Γ' C t at ht
  rw [he] at ht
  rcases ht with ⟨Γ', C, t, eΓ, hC, ht⟩
  have eΓ' := Value.context.inj eΓ
  subst Γ'
  change (split (.var 1) (.var 2) (subTm (.var 4) (pack (.var 1) (.var 2)))).eval _ _ = _
  simp only [Term.eval, FinitaryTerm.fold, algebra, operation, Contextual.algebra,
    DependentJudgments.operation, Matrix.cons_val_zero, Matrix.cons_val_one,
    hA, hB, ht, inputs_values, Value.termIn_term]
  apply Value.term_eq
  · exact S.split_type A B C
  · apply (M.subTm_comp _ _ _).trans
    rw [S.pack_unpack]
    exact M.subTm_id t

/-- Empty extra signature: this extension changes laws, not operations. -/
def lawSignature : Signature where
  Operation := Empty
  arity := Empty.elim
  Predicate := Empty
  arguments := Empty.elim

abbrev closureRule (_ : Unit) : Rule (signature.sum lawSignature) := splitEtaRule.inl lawSignature
abbrev closureTheory := theory.extend lawSignature Unit closureRule

noncomputable def closureAlgebra (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel) :
    Algebra (signature.sum lawSignature) where
  Carrier := Value M.toStructuralModel
  operation
    | .inl op => (algebra M S).operation op
    | .inr op => nomatch op
  predicate
    | .inl p => (algebra M S).predicate p
    | .inr p => nomatch p

/-- Sequential extension is valid because the extra law follows from the first
extension's operations and inverse laws. Arbitrary further laws need not pass. -/
noncomputable def closureModel (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel) :
    GuardedTheory.Model closureTheory where
  toAlgebra := closureAlgebra M S
  rules
    | .inl a => by
      intro ρ h
      simp only [closureTheory, Theory.extend, Rule.inl, Atom.eval_inl] at h ⊢
      exact (model M S).rules a ρ h
    | .inr () => by
      intro ρ h
      simp only [closureTheory, Theory.extend, closureRule, Rule.inl, Atom.eval_inl] at h ⊢
      exact splitEta_valid M S ρ h

theorem closure_reduct (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel) :
    (closureModel M S).restrictLeft = model M S := rfl

/-- The two inclusions compose for every old derivation. -/
noncomputable def retain_twice {V : Type} {Ω : List (Contextual.Judgment V)}
    {a : Contextual.Judgment V} (d : Derivation Contextual.theory Ω a) :
    Derivation closureTheory ((Ω.map (Atom.inl extraSignature)).map (Atom.inl lawSignature))
      ((a.inl extraSignature).inl lawSignature) := (retain d).inl closureRule

/-- Selected observations are unchanged through both reducts. -/
theorem recover_twice (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel)
    {V : Type} (t : Contextual.Expression V) (ρ : V → Value M.toStructuralModel) :
    ((t.inl extraSignature).inl lawSignature).eval (closureAlgebra M S) ρ =
      t.eval (Contextual.algebra M) ρ := by
  rw [Term.eval_inl]
  exact eval_old M S t ρ

end SquareKit.Internal.DependentJudgments.Sigma
