import SquareKit.Internal.DependentJudgments.ContextualOperations

/-! Structural rules of the guarded source. Their semantic proofs are built
once from the contextual model laws; authored derivations contain only syntax. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
set_option backward.isDefEq.respectTransparency false
open GuardedTheory PathTransport.Typed
universe u

abbrev familySubSchema (out : Judgment (Fin 4)) : Rule signature where
  parameterCount := 4
  hypotheses := 2
  premise := ![family (.var 0) (.var 2), substitution (.var 1) (.var 0) (.var 3)]
  conclusion := out

theorem familySubSchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 4))
    (valid : ∀ Γ Δ A σ, out.eval (algebra M)
      ![.context Γ, .context Δ, .family Γ A, .substitution Δ Γ σ]) :
    Satisfies (algebra M) (familySubSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, hΓ, hA⟩
  rcases h 1 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have e : ρ = ![Value.context Γ, .context Δ, .family Γ A, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hA | exact hσ
  subst ρ
  exact valid Γ Δ A σ

abbrev subTyRule := familySubSchema (family (.var 1) (subTy (.var 2) (.var 3)))

theorem subTy_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) subTyRule := by
  apply familySubSchema_valid
  intro Γ Δ A σ
  refine ⟨Δ, M.subTy A σ, rfl, ?_⟩
  simp [Term.eval, algebra, DependentJudgments.operation]

abbrev termSubSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 2
  premise := ![term (.var 0) (.var 2) (.var 3), substitution (.var 1) (.var 0) (.var 4)]
  conclusion := out

theorem termSubSchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 5))
    (valid : ∀ Γ Δ A t σ, out.eval (algebra M)
      ![.context Γ, .context Δ, .family Γ A, .term Γ A t, .substitution Δ Γ σ]) :
    Satisfies (algebra M) (termSubSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, t, hΓ, hA, ht⟩
  rcases h 1 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have e : ρ = ![Value.context Γ, .context Δ, .family Γ A, .term Γ A t, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hA | exact ht | exact hσ
  subst ρ
  exact valid Γ Δ A t σ

abbrev subTmRule := termSubSchema
  (term (.var 1) (subTy (.var 2) (.var 4)) (subTm (.var 3) (.var 4)))
abbrev reflSubRule := termSubSchema
  (.eq (subTm (reflexivity (.var 2) (.var 3)) (.var 4))
    (reflexivity (subTy (.var 2) (.var 4)) (subTm (.var 3) (.var 4))))

theorem subTm_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) subTmRule := by
  apply termSubSchema_valid
  intro Γ Δ A t σ
  refine ⟨Δ, M.subTy A σ, M.subTm t σ, rfl, ?_, ?_⟩ <;>
    simp [Term.eval, algebra, DependentJudgments.operation]

theorem reflSub_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) reflSubRule := by
  apply termSubSchema_valid
  intro Γ Δ A t σ
  change Term.eval (algebra M) _ _ = _
  simpa [Term.eval, algebra, DependentJudgments.operation, operation]
    using Value.term_eq (M.identity_sub A t t σ) (M.refl_sub A t σ)

abbrev subSchema (out : Judgment (Fin 3)) : Rule signature where
  parameterCount := 3
  hypotheses := 1
  premise := ![substitution (.var 1) (.var 0) (.var 2)]
  conclusion := out

theorem subSchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 3))
    (valid : ∀ Γ Δ σ, out.eval (algebra M) ![.context Γ, .context Δ, .substitution Δ Γ σ]) :
    Satisfies (algebra M) (subSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Δ, Γ, σ, hΔ, hΓ, hσ⟩
  have e : ρ = ![Value.context Γ, .context Δ, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hσ
  subst ρ
  exact valid Γ Δ σ

abbrev compIdLeftRule := subSchema (.eq (comp (identitySub (.var 0)) (.var 2)) (.var 2))
abbrev compIdRightRule := subSchema (.eq (comp (.var 2) (identitySub (.var 1))) (.var 2))

theorem compIdLeft_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) compIdLeftRule := by
  apply subSchema_valid
  intro Γ Δ σ
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, algebra, DependentJudgments.operation, M.comp_id_left]

theorem compIdRight_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) compIdRightRule := by
  apply subSchema_valid
  intro Γ Δ σ
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, algebra, DependentJudgments.operation, M.comp_id_right]

abbrev familySchema (out : Judgment (Fin 2)) : Rule signature where
  parameterCount := 2
  hypotheses := 1
  premise := ![family (.var 0) (.var 1)]
  conclusion := out

theorem familySchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 2))
    (valid : ∀ Γ A, out.eval (algebra M) ![.context Γ, .family Γ A]) :
    Satisfies (algebra M) (familySchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, hΓ, hA⟩
  have e : ρ = ![Value.context Γ, .family Γ A] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA
  subst ρ
  exact valid Γ A

abbrev subTyIdRule := familySchema (.eq (subTy (.var 1) (identitySub (.var 0))) (.var 1))
abbrev subTmIdRule := pointSchema (.eq (subTm (.var 2) (identitySub (.var 0))) (.var 2))
abbrev termFamilyRule := pointSchema (family (.var 0) (.var 1))
abbrev familyContextRule := familySchema (context (.var 0))

theorem subTyId_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) subTyIdRule := by
  apply familySchema_valid
  intro Γ A
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, algebra, DependentJudgments.operation, M.subTy_id]

theorem subTmId_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) subTmIdRule := by
  apply pointSchema_valid
  intro Γ A t
  change Term.eval (algebra M) _ _ = _
  simpa [Term.eval, algebra, DependentJudgments.operation]
    using Value.term_eq (M.subTy_id A) (M.subTm_id t)

theorem termFamily_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) termFamilyRule := by
  apply pointSchema_valid
  intro Γ A _
  exact ⟨Γ, A, rfl, rfl⟩

theorem familyContext_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) familyContextRule := by
  apply familySchema_valid
  intro Γ _
  exact ⟨Γ, rfl⟩


abbrev compSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 2
  premise := ![substitution (.var 1) (.var 0) (.var 3), substitution (.var 2) (.var 1) (.var 4)]
  conclusion := out

theorem compSchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 5))
    (valid : ∀ Γ Δ Θ σ τ, out.eval (algebra M)
      ![.context Γ, .context Δ, .context Θ, .substitution Δ Γ σ, .substitution Θ Δ τ]) :
    Satisfies (algebra M) (compSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Δ, Γ, σ, hΔ, hΓ, hσ⟩
  rcases h 1 with ⟨Θ, Δ', τ, hΘ, hΔ', hτ⟩
  change ρ 1 = .context Δ at hΔ
  change ρ 1 = .context Δ' at hΔ'
  have eΔ := Value.context.inj (hΔ'.symm.trans hΔ)
  subst Δ'
  have e : ρ = ![Value.context Γ, .context Δ, .context Θ, .substitution Δ Γ σ, .substitution Θ Δ τ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hΘ | exact hσ | exact hτ
  subst ρ
  exact valid Γ Δ Θ σ τ

abbrev compRule := compSchema (substitution (.var 2) (.var 0) (comp (.var 3) (.var 4)))

theorem comp_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) compRule := by
  apply compSchema_valid
  intro Γ Δ Θ σ τ
  refine ⟨Θ, Γ, M.compSub σ τ, rfl, rfl, ?_⟩
  simp [Term.eval, algebra, DependentJudgments.operation]

abbrev familyCompSchema (out : Judgment (Fin 6)) : Rule signature where
  parameterCount := 6
  hypotheses := 3
  premise := ![family (.var 0) (.var 3),
    substitution (.var 1) (.var 0) (.var 4), substitution (.var 2) (.var 1) (.var 5)]
  conclusion := out

theorem familyCompSchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 6))
    (valid : ∀ Γ Δ Θ A σ τ, out.eval (algebra M)
      ![.context Γ, .context Δ, .context Θ, .family Γ A, .substitution Δ Γ σ, .substitution Θ Δ τ]) :
    Satisfies (algebra M) (familyCompSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, hΓ, hA⟩
  rcases h 1 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  rcases h 2 with ⟨Θ, Δ', τ, hΘ, hΔ', hτ⟩
  change ρ 1 = .context Δ at hΔ
  change ρ 1 = .context Δ' at hΔ'
  have eΔ := Value.context.inj (hΔ'.symm.trans hΔ)
  subst Δ'
  have e : ρ = ![Value.context Γ, .context Δ, .context Θ, .family Γ A,
      .substitution Δ Γ σ, .substitution Θ Δ τ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hΘ | exact hA | exact hσ | exact hτ
  subst ρ
  exact valid Γ Δ Θ A σ τ

abbrev subTyCompRule := familyCompSchema
  (.eq (subTy (subTy (.var 3) (.var 4)) (.var 5)) (subTy (.var 3) (comp (.var 4) (.var 5))))

theorem subTyComp_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) subTyCompRule := by
  apply familyCompSchema_valid
  intro Γ Δ Θ A σ τ
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, algebra, DependentJudgments.operation, M.subTy_comp]

abbrev termCompSchema (out : Judgment (Fin 7)) : Rule signature where
  parameterCount := 7
  hypotheses := 3
  premise := ![term (.var 0) (.var 3) (.var 4),
    substitution (.var 1) (.var 0) (.var 5), substitution (.var 2) (.var 1) (.var 6)]
  conclusion := out

theorem termCompSchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 7))
    (valid : ∀ Γ Δ Θ A t σ τ, out.eval (algebra M)
      ![.context Γ, .context Δ, .context Θ, .family Γ A, .term Γ A t,
        .substitution Δ Γ σ, .substitution Θ Δ τ]) :
    Satisfies (algebra M) (termCompSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, t, hΓ, hA, ht⟩
  rcases h 1 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  rcases h 2 with ⟨Θ, Δ', τ, hΘ, hΔ', hτ⟩
  change ρ 1 = .context Δ at hΔ
  change ρ 1 = .context Δ' at hΔ'
  have eΔ := Value.context.inj (hΔ'.symm.trans hΔ)
  subst Δ'
  have e : ρ = ![Value.context Γ, .context Δ, .context Θ, .family Γ A, .term Γ A t,
      .substitution Δ Γ σ, .substitution Θ Δ τ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hΘ | exact hA | exact ht | exact hσ | exact hτ
  subst ρ
  exact valid Γ Δ Θ A t σ τ

abbrev subTmCompRule := termCompSchema
  (.eq (subTm (subTm (.var 4) (.var 5)) (.var 6)) (subTm (.var 4) (comp (.var 5) (.var 6))))

theorem subTmComp_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) subTmCompRule := by
  apply termCompSchema_valid
  intro Γ Δ Θ A t σ τ
  change Term.eval (algebra M) _ _ = _
  simpa [Term.eval, algebra, DependentJudgments.operation]
    using Value.term_eq (M.subTy_comp A σ τ) (M.subTm_comp t σ τ)

abbrev assocSchema (out : Judgment (Fin 7)) : Rule signature where
  parameterCount := 7
  hypotheses := 3
  premise := ![substitution (.var 1) (.var 0) (.var 4),
    substitution (.var 2) (.var 1) (.var 5), substitution (.var 3) (.var 2) (.var 6)]
  conclusion := out

theorem assocSchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 7))
    (valid : ∀ Γ Δ Θ Ξ σ τ υ, out.eval (algebra M)
      ![.context Γ, .context Δ, .context Θ, .context Ξ,
        .substitution Δ Γ σ, .substitution Θ Δ τ, .substitution Ξ Θ υ]) :
    Satisfies (algebra M) (assocSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Δ, Γ, σ, hΔ, hΓ, hσ⟩
  rcases h 1 with ⟨Θ, Δ', τ, hΘ, hΔ', hτ⟩
  change ρ 1 = .context Δ at hΔ
  change ρ 1 = .context Δ' at hΔ'
  have eΔ := Value.context.inj (hΔ'.symm.trans hΔ)
  subst Δ'
  rcases h 2 with ⟨Ξ, Θ', υ, hΞ, hΘ', hυ⟩
  change ρ 2 = .context Θ at hΘ
  change ρ 2 = .context Θ' at hΘ'
  have eΘ := Value.context.inj (hΘ'.symm.trans hΘ)
  subst Θ'
  have e : ρ = ![Value.context Γ, .context Δ, .context Θ, .context Ξ,
      .substitution Δ Γ σ, .substitution Θ Δ τ, .substitution Ξ Θ υ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hΘ | exact hΞ | exact hσ | exact hτ | exact hυ
  subst ρ
  exact valid Γ Δ Θ Ξ σ τ υ

abbrev compAssocRule := assocSchema
  (.eq (comp (comp (.var 4) (.var 5)) (.var 6)) (comp (.var 4) (comp (.var 5) (.var 6))))

theorem compAssoc_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) compAssocRule := by
  apply assocSchema_valid
  intro Γ Δ Θ Ξ σ τ υ
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, algebra, DependentJudgments.operation, M.comp_assoc]

end SquareKit.Internal.DependentJudgments.Contextual
