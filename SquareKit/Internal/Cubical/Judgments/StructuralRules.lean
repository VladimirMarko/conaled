import SquareKit.Internal.Cubical.Judgments.Comprehension

/-! Object-context substitution and structural judgmental rules. The source
schemas contain only raw expressions and typing premises. -/
namespace SquareKit.Cubical.Source
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Internal.DependentJudgments
universe u
attribute [local simp] subTy subTm identitySub comp apply1 apply2

abbrev pointSchema (out : Judgment (Fin 3)) : Rule signature where
  parameterCount := 3
  hypotheses := 1
  premise := ![term (.var 0) (.var 1) (.var 2)]
  conclusion := out

theorem pointSchema_valid (out : Judgment (Fin 3))
    (valid : ∀ Γ A t, out.eval algebra.{u} ![.context Γ, .family Γ A, .term Γ A t]) :
    Satisfies algebra.{u} (pointSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ,A,t,hΓ,hA,ht⟩
  have e : ρ = ![Value.context Γ, .family Γ A, .term Γ A t] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact ht
  subst ρ
  exact valid Γ A t

abbrev familySubSchema (out : Judgment (Fin 4)) : Rule signature where
  parameterCount := 4
  hypotheses := 2
  premise := ![family (.var 0) (.var 2), substitution (.var 1) (.var 0) (.var 3)]
  conclusion := out

theorem familySubSchema_valid (out : Judgment (Fin 4))
    (valid : ∀ Γ Δ A σ, out.eval algebra.{u}
      ![.context Γ, .context Δ, .family Γ A, .substitution Δ Γ σ]) :
    Satisfies algebra.{u} (familySubSchema out) := by
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

theorem subTy_valid : Satisfies algebra.{u} subTyRule := by
  apply familySubSchema_valid
  intro Γ Δ A σ
  refine ⟨Δ, Semantics.subTy A σ, rfl, ?_⟩
  simp [Term.eval, algebra, operation]

abbrev termSubSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 2
  premise := ![term (.var 0) (.var 2) (.var 3), substitution (.var 1) (.var 0) (.var 4)]
  conclusion := out

theorem termSubSchema_valid (out : Judgment (Fin 5))
    (valid : ∀ Γ Δ A t σ, out.eval algebra.{u}
      ![.context Γ, .context Δ, .family Γ A, .term Γ A t, .substitution Δ Γ σ]) :
    Satisfies algebra.{u} (termSubSchema out) := by
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
theorem subTm_valid : Satisfies algebra.{u} subTmRule := by
  apply termSubSchema_valid
  intro Γ Δ A t σ
  refine ⟨Δ, Semantics.subTy A σ, Semantics.subTm t σ, rfl, ?_, ?_⟩ <;>
    simp [Term.eval, algebra, operation]

abbrev subSchema (out : Judgment (Fin 3)) : Rule signature where
  parameterCount := 3
  hypotheses := 1
  premise := ![substitution (.var 1) (.var 0) (.var 2)]
  conclusion := out

theorem subSchema_valid (out : Judgment (Fin 3))
    (valid : ∀ Γ Δ σ, out.eval algebra.{u} ![.context Γ, .context Δ, .substitution Δ Γ σ]) :
    Satisfies algebra.{u} (subSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Δ, Γ, σ, hΔ, hΓ, hσ⟩
  have e : ρ = ![Value.context Γ, .context Δ, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hσ
  subst ρ
  exact valid Γ Δ σ

abbrev compIdLeftRule := subSchema (.eq (comp (identitySub (.var 0)) (.var 2)) (.var 2))
abbrev compIdRightRule := subSchema (.eq (comp (.var 2) (identitySub (.var 1))) (.var 2))

theorem compIdLeft_valid : Satisfies algebra.{u} compIdLeftRule := by
  apply subSchema_valid
  intro Γ Δ σ
  change Term.eval algebra.{u} _ _ = _
  simp [Term.eval, algebra, operation]

theorem compIdRight_valid : Satisfies algebra.{u} compIdRightRule := by
  apply subSchema_valid
  intro Γ Δ σ
  change Term.eval algebra.{u} _ _ = _
  simp [Term.eval, algebra, operation]

abbrev subTyIdRule := familySchema (.eq (subTy (.var 1) (identitySub (.var 0))) (.var 1))
abbrev subTmIdRule := pointSchema (.eq (subTm (.var 2) (identitySub (.var 0))) (.var 2))
abbrev termFamilyRule := pointSchema (family (.var 0) (.var 1))
abbrev familyContextRule := familySchema (context (.var 0))

theorem subTyId_valid : Satisfies algebra.{u} subTyIdRule := by
  apply familySchema_valid
  intro Γ A
  change Term.eval algebra.{u} _ _ = _
  simp [Term.eval, algebra, operation]

theorem subTmId_valid : Satisfies algebra.{u} subTmIdRule := by
  apply pointSchema_valid
  intro Γ A t
  change Term.eval algebra.{u} _ _ = _
  simp [Term.eval, algebra, operation]

theorem termFamily_valid : Satisfies algebra.{u} termFamilyRule := by
  apply pointSchema_valid
  intro Γ A _
  exact ⟨Γ, A, rfl, rfl⟩

theorem familyContext_valid : Satisfies algebra.{u} familyContextRule := by
  apply familySchema_valid
  intro Γ _
  exact ⟨Γ, rfl⟩


abbrev compSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 2
  premise := ![substitution (.var 1) (.var 0) (.var 3), substitution (.var 2) (.var 1) (.var 4)]
  conclusion := out

theorem compSchema_valid (out : Judgment (Fin 5))
    (valid : ∀ Γ Δ Θ σ τ, out.eval algebra.{u}
      ![.context Γ, .context Δ, .context Θ, .substitution Δ Γ σ, .substitution Θ Δ τ]) :
    Satisfies algebra.{u} (compSchema out) := by
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

theorem comp_valid : Satisfies algebra.{u} compRule := by
  apply compSchema_valid
  intro Γ Δ Θ σ τ
  refine ⟨Θ, Γ, Semantics.compSub σ τ, rfl, rfl, ?_⟩
  simp [Term.eval, algebra, operation]

abbrev familyCompSchema (out : Judgment (Fin 6)) : Rule signature where
  parameterCount := 6
  hypotheses := 3
  premise := ![family (.var 0) (.var 3),
    substitution (.var 1) (.var 0) (.var 4), substitution (.var 2) (.var 1) (.var 5)]
  conclusion := out

theorem familyCompSchema_valid (out : Judgment (Fin 6))
    (valid : ∀ Γ Δ Θ A σ τ, out.eval algebra.{u}
      ![.context Γ, .context Δ, .context Θ, .family Γ A, .substitution Δ Γ σ, .substitution Θ Δ τ]) :
    Satisfies algebra.{u} (familyCompSchema out) := by
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

theorem subTyComp_valid : Satisfies algebra.{u} subTyCompRule := by
  apply familyCompSchema_valid
  intro Γ Δ Θ A σ τ
  change Term.eval algebra.{u} _ _ = _
  simp [Term.eval, algebra, operation]

abbrev termCompSchema (out : Judgment (Fin 7)) : Rule signature where
  parameterCount := 7
  hypotheses := 3
  premise := ![term (.var 0) (.var 3) (.var 4),
    substitution (.var 1) (.var 0) (.var 5), substitution (.var 2) (.var 1) (.var 6)]
  conclusion := out

theorem termCompSchema_valid (out : Judgment (Fin 7))
    (valid : ∀ Γ Δ Θ A t σ τ, out.eval algebra.{u}
      ![.context Γ, .context Δ, .context Θ, .family Γ A, .term Γ A t,
        .substitution Δ Γ σ, .substitution Θ Δ τ]) :
    Satisfies algebra.{u} (termCompSchema out) := by
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

theorem subTmComp_valid : Satisfies algebra.{u} subTmCompRule := by
  apply termCompSchema_valid
  intro Γ Δ Θ A t σ τ
  change Term.eval algebra.{u} _ _ = _
  simpa [Term.eval, algebra, operation]
    using Value.term_eq (Semantics.subTy_comp A σ τ) (Semantics.subTm_comp t σ τ)

abbrev assocSchema (out : Judgment (Fin 7)) : Rule signature where
  parameterCount := 7
  hypotheses := 3
  premise := ![substitution (.var 1) (.var 0) (.var 4),
    substitution (.var 2) (.var 1) (.var 5), substitution (.var 3) (.var 2) (.var 6)]
  conclusion := out

theorem assocSchema_valid (out : Judgment (Fin 7))
    (valid : ∀ Γ Δ Θ Ξ σ τ υ, out.eval algebra.{u}
      ![.context Γ, .context Δ, .context Θ, .context Ξ,
        .substitution Δ Γ σ, .substitution Θ Δ τ, .substitution Ξ Θ υ]) :
    Satisfies algebra.{u} (assocSchema out) := by
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

theorem compAssoc_valid : Satisfies algebra.{u} compAssocRule := by
  apply assocSchema_valid
  intro Γ Δ Θ Ξ σ τ υ
  change operation .comp ![operation .comp ![.substitution Δ Γ σ, .substitution Θ Δ τ],
      .substitution Ξ Θ υ] =
    operation .comp ![.substitution Δ Γ σ,
      operation .comp ![.substitution Θ Δ τ, .substitution Ξ Θ υ]]
  simp only [operation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Value.substitutionAt_substitution]
  exact congrArg (Value.substitution Ξ Γ) (Semantics.comp_assoc σ τ υ)

end SquareKit.Cubical.Source
