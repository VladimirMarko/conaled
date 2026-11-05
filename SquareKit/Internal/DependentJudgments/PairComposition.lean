import SquareKit.Internal.DependentJudgments.DerivedRules
import SquareKit.Internal.PathTransport.Comprehension

namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

abbrev pairCompRule : Rule signature where
  parameterCount := 7
  hypotheses := 4
  premise := ![family (.var 0) (.var 3), substitution (.var 1) (.var 0) (.var 4),
    term (.var 1) (subTy (.var 3) (.var 4)) (.var 5), substitution (.var 2) (.var 1) (.var 6)]
  conclusion := .eq (comp (pair (.var 3) (.var 4) (.var 5)) (.var 6))
    (pair (.var 3) (comp (.var 4) (.var 6)) (subTm (.var 5) (.var 6)))

theorem pairComp_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) pairCompRule := by
  intro ρ h
  have hp : ∀ i, (variablePairRule.premise i).eval (DependentJudgments.algebra M.toStructuralModel)
      ![ρ 0, ρ 1, ρ 3, ρ 4, ρ 5] := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1 | exact h 2
  obtain ⟨Γ, Δ, A, σ, t, he⟩ := pairing_inputs M.toStructuralModel _ hp
  have hΓ : ρ 0 = .context Γ := congrFun he 0
  have hΔ : ρ 1 = .context Δ := congrFun he 1
  have hA : ρ 3 = .family Γ A := congrFun he 2
  have hσ : ρ 4 = .substitution Δ Γ σ := congrFun he 3
  have ht : ρ 5 = .term Δ (M.subTy A σ) t := congrFun he 4
  rcases h 3 with ⟨Θ, Δ', τ, hΘ, hΔ', hτ⟩
  change ρ 1 = .context Δ' at hΔ'
  have eΔ := Value.context.inj (hΔ'.symm.trans hΔ)
  subst Δ'
  have e : ρ = ![Value.context Γ, .context Δ, .context Θ, .family Γ A,
      .substitution Δ Γ σ, .term Δ (M.subTy A σ) t, .substitution Θ Δ τ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hΘ | exact hA | exact hσ | exact ht | exact hτ
  subst ρ
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, FinitaryTerm.fold, algebra, DependentJudgments.operation]
  have hc : Value.term (M := M.toStructuralModel) Θ (M.subTy (M.subTy A σ) τ) (M.subTm t τ) =
      .term Θ (M.subTy A (M.compSub σ τ))
        (cast (congrArg (M.Section Θ) (M.subTy_comp A σ τ)) (M.subTm t τ)) :=
    Value.term_eq (M.subTy_comp A σ τ) (cast_heq _ _).symm
  rw [hc, Value.termAt_term, M.toStructuralModel.pair_naturality]

end SquareKit.Internal.DependentJudgments.Contextual
