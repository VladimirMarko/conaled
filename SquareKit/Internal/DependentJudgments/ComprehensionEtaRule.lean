import SquareKit.Internal.DependentJudgments.PathReindexRules

/-! The reconstruction equation is the existing comprehension eta law. It is
needed to identify a lifted identity substitution with the actual identity. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

abbrev pairEtaRule : Rule signature where
  parameterCount := 4
  hypotheses := 2
  premise := ![family (.var 0) (.var 2), substitution (.var 1) (extend (.var 0) (.var 2)) (.var 3)]
  conclusion := .eq
    (pair (.var 2) (comp (weaken (.var 0) (.var 2)) (.var 3)) (subTm (generic (.var 0) (.var 2)) (.var 3)))
    (.var 3)

theorem pairEta_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) pairEtaRule := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, hΓ, hA⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 2 = .family Γ A at hA
  have he : (extend (.var 0) (.var 2)).eval (algebra M) ρ = .context (M.extend Γ A) := by
    simp [Term.eval, algebra, DependentJudgments.operation, hΓ, hA]
  rcases h 1 with ⟨Δ, Γ', σ, hΔ, he', hσ⟩
  change (extend (.var 0) (.var 2)).eval (algebra M) ρ = .context Γ' at he'
  have heq := Value.context.inj (he'.symm.trans he)
  subst Γ'
  have e : ρ = ![Value.context Γ, .context Δ, .family Γ A, .substitution Δ (M.extend Γ A) σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hA | exact hσ
  subst ρ
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, FinitaryTerm.fold, algebra, DependentJudgments.operation]
  have hv : Value.term (M := M.toStructuralModel) Δ (M.subTy (M.subTy A (M.weaken Γ A)) σ)
      (M.subTm (M.genericVariable Γ A) σ) =
      .term Δ (M.subTy A (M.compSub (M.weaken Γ A) σ))
        (cast (congrArg (M.Section Δ) (M.subTy_comp A (M.weaken Γ A) σ))
          (M.subTm (M.genericVariable Γ A) σ)) :=
    Value.term_eq (M.subTy_comp A (M.weaken Γ A) σ) (cast_heq _ _).symm
  rw [hv, Value.termAt_term]
  exact congrArg (Value.substitution Δ (M.extend Γ A)) (M.pair_eta A σ)

end SquareKit.Internal.DependentJudgments.Contextual
