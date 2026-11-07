import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Substitution
import SquareKit.GuardedRuleInterpretation
import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Separation
import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Comparison

/-! A compositional specification experiment: primitive sums, stable primitive
sums, and stable sums satisfying an additional elimination-eta rule. The last
contract is a stronger specification over the same syntax, not a new logic. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma.Specification
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false

/-- The added requirement names the existing elimination-eta judgment. -/
def etaTheory : Theory signature where
  Axiom := Sum Reindexing.theory.Axiom Unit
  rule
    | .inl a => Reindexing.theory.rule a
    | .inr _ => splitEtaRule

noncomputable def stableView : RuleInterpretation theory Reindexing.theory :=
  .ofRuleMap Sum.inl (fun _ => rfl)

noncomputable def etaView : RuleInterpretation Reindexing.theory etaTheory :=
  .ofRuleMap Sum.inl (fun _ => rfl)

noncomputable def composedView : RuleInterpretation theory etaTheory :=
  etaView.compose stableView

/-- Primitive certificates transport an argument through both specification
extensions without changing its chosen terms, motive, branch or assumptions. -/
noncomputable def sharedArgument :
    Derivation theory (List.ofFn splitBetaRule.premise) splitBetaRule.conclusion :=
  RuleInterpretation.axiomDerivation theory (.inr .splitBeta)

noncomputable def sharedArgumentStrong :
    Derivation etaTheory (List.ofFn splitBetaRule.premise) splitBetaRule.conclusion :=
  composedView.transport sharedArgument

/-- A client consequence: substitute a dependent elimination computation into
an arbitrary well-typed context. It is not a primitive axiom of the theory. -/
abbrev reindexedBetaRule : Rule signature where
  parameterCount := 7
  hypotheses := 5
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2),
    family (extend (.var 0) (sigma (.var 1) (.var 2))) (.var 3),
    term (branchContext (.var 0) (.var 1) (.var 2))
      (subTy (.var 3) (pack (.var 1) (.var 2))) (.var 4),
    substitution (.var 5) (branchContext (.var 0) (.var 1) (.var 2)) (.var 6)]
  conclusion := .eq
    (subTm (subTm (split (.var 1) (.var 2) (.var 3) (.var 4))
      (pack (.var 1) (.var 2))) (.var 6))
    (subTm (.var 4) (.var 6))

noncomputable def reindexedArgument : Derivation theory
    (List.ofFn reindexedBetaRule.premise) reindexedBetaRule.conclusion := by
  have beta : Derivation theory (List.ofFn reindexedBetaRule.premise)
      (.eq (subTm (split (.var 1) (.var 2) (.var 3) (.var 4))
        (pack (.var 1) (.var 2))) (.var 4)) := by
    have h (i : Fin 5) : Derivation theory (List.ofFn reindexedBetaRule.premise)
        (reindexedBetaRule.premise i) := .hypothesis (List.mem_ofFn.mpr ⟨i, rfl⟩)
    have d := Derivation.rule (T := theory) (Γ := List.ofFn reindexedBetaRule.premise) (.inr .splitBeta)
      ![.var 0, .var 1, .var 2, .var 3, .var 4]
      (Fin.cases (by simpa [theory, Theory.extend, rule] using h 0)
        (Fin.cases (by simpa [theory, Theory.extend, rule] using h 1)
          (Fin.cases (by simpa [theory, Theory.extend, rule] using h 2)
            (Fin.cases (by simpa [theory, Theory.extend, rule] using h 3) (fun i => nomatch i)))))
    simpa [theory, Theory.extend, rule] using d
  apply Derivation.congruence (T := theory)
    (Sum.inl (Sum.inl DependentJudgments.Operation.subTm))
  exact Fin.cases beta (Fin.cases (.reflexive (.var 6)) (fun i => nomatch i))

/-- Publishing this derived rule needs no new semantic operation or axiom in
its implementation: its local certificate expands into beta and congruence. -/
def clientTheory : Theory signature where
  Axiom := Unit
  rule _ := reindexedBetaRule

noncomputable def clientView : RuleInterpretation clientTheory theory := ⟨fun _ => reindexedArgument⟩

/-- The stronger argument exposes its additional principle in its theory. -/
noncomputable def strongerArgument :
    Derivation etaTheory (List.ofFn splitEtaRule.premise) splitEtaRule.conclusion :=
  RuleInterpretation.axiomDerivation etaTheory (.inr ())

/-- A reverse view fixing this syntax would prove the known false eta rule. -/
theorem no_reverse_view : ¬ Nonempty (RuleInterpretation etaTheory Reindexing.theory) := by
  rintro ⟨F⟩
  exact Separation.stable_splitEta_not_derivable (F.transport strongerArgument)

/-- Stability's extra rules do not invalidate the shared derivation. -/
theorem weak_interpretation (ρ : Fin 5 → Value Separation.M.toStructuralModel)
    (h : ∀ p ∈ List.ofFn splitBetaRule.premise,
      p.eval (algebra Separation.M Separation.S) ρ) :
    splitBetaRule.conclusion.eval (algebra Separation.M Separation.S) ρ :=
  (stableView.transport sharedArgument).sound
    (Reindexing.model Separation.M (ConstantFamilies.stable PUnit)) ρ h

/-- Validation of the added rule comes from the existing strong capability;
model builders do not supply this rule's final semantic conclusion. -/
theorem eta_valid (M : PathTransport.Typed.Model) (S : Sigma.Capability M.toStructuralModel) :
    Satisfies (algebra M (ofStrong S)) splitEtaRule := by
  intro ρ h
  let ρ₀ : Fin 3 → Value M.toStructuralModel := fun i => ρ (i.castAdd 2)
  have h₀ : ∀ i, (formationRule.premise i).eval (algebra M (ofStrong S)) ρ₀ := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1
  rcases formationSchema_inputs M (ofStrong S) _ ρ₀ h₀ with ⟨Γ, A, B, e⟩
  have hΓ := congrFun e 0
  have hA := congrFun e 1
  have hB := congrFun e 2
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  change ρ 2 = .family (M.extend Γ A) B at hB
  have he : (extend (.var 0) (sigma (.var 1) (.var 2))).eval
      (algebra M (ofStrong S)) ρ = .context (M.extend Γ (S.sigma A B)) := by
    simp [Term.eval, algebra, operation, Contextual.algebra,
      DependentJudgments.operation, hΓ, hA, hB, ofStrong]
  have ht := h 3
  change ∃ Γ' C t, (extend (.var 0) (sigma (.var 1) (.var 2))).eval
      (algebra M (ofStrong S)) ρ = .context Γ' ∧
      ρ 3 = .family Γ' C ∧ ρ 4 = .term Γ' C t at ht
  rw [he] at ht
  rcases ht with ⟨Γ', C, t, eΓ, hC, ht⟩
  have eΓ' := Value.context.inj eΓ
  subst Γ'
  change (split (.var 1) (.var 2) (.var 3)
    (subTm (.var 4) (pack (.var 1) (.var 2)))).eval _ _ = _
  simp only [Term.eval, FinitaryTerm.fold, algebra, operation, Contextual.algebra,
    DependentJudgments.operation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    hA, hB, hC, ht, inputs_values, Value.familyAt_family, Value.termIn_term,
    Value.termAt_term]
  exact congrArg (Value.term _ _) (S.split_eta A B C t)

noncomputable def strongModel (M : PathTransport.Typed.Model)
    (S : Sigma.Stable M.toStructuralModel) : Model etaTheory where
  toAlgebra := algebra M (ofStrong S.toCapability)
  rules
    | .inl a => (Reindexing.model M (Stable.ofStrong S)).rules a
    | .inr _ => eta_valid M S.toCapability

/-- Both routes recover the original selected interpreter exactly. -/
theorem strong_reduct (M : PathTransport.Typed.Model) (S : Sigma.Stable M.toStructuralModel) :
    composedView.reduct (strongModel M S) = model M (ofStrong S.toCapability) := rfl

/-- Raw source substitution acts on the transported proof without changing its
judgment. Semantic dependent stability is supplied by the stable model. -/
noncomputable def substitutedShared {V : Type} (σ : Fin 5 → Expression V) :
    Derivation etaTheory ((List.ofFn splitBetaRule.premise).map (Atom.subst σ))
      (splitBetaRule.conclusion.subst σ) :=
  composedView.transportSubstitute sharedArgument σ

end SquareKit.Internal.DependentJudgments.PrimitiveSigma.Specification
