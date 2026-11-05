import SquareKit.Internal.DependentJudgments.StructuralRules

/-! Formation and substitution laws for the contextual identity signature. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
set_option backward.isDefEq.respectTransparency false
open GuardedTheory PathTransport.Typed StructuralModel
universe u

abbrev identitySchema (out : Judgment (Fin 4)) : Rule signature where
  parameterCount := 4
  hypotheses := 2
  premise := ![term (.var 0) (.var 1) (.var 2), term (.var 0) (.var 1) (.var 3)]
  conclusion := out

theorem identitySchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 4))
    (valid : ∀ Γ A x y, out.eval (algebra M)
      ![.context Γ, .family Γ A, .term Γ A x, .term Γ A y]) :
    Satisfies (algebra M) (identitySchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, x, hΓ, hA, hx⟩
  rcases h 1 with ⟨Γ', A', y, hΓ', hA', hy⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  change ρ 1 = .family Γ A at hA
  change ρ 1 = .family Γ A' at hA'
  have eA := eq_of_heq (Value.family.inj (hA'.symm.trans hA)).2
  subst A'
  have e : ρ = ![Value.context Γ, .family Γ A, .term Γ A x, .term Γ A y] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hx | exact hy
  subst ρ
  exact valid Γ A x y

abbrev identityRule := identitySchema (family (.var 0) (identity (.var 1) (.var 2) (.var 3)))

theorem identity_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) identityRule := by
  apply identitySchema_valid
  intro Γ A x y
  exact ⟨Γ, M.identity A x y, rfl, by simp [Term.eval, algebra, operation]⟩

abbrev identitySubSchema (out : Judgment (Fin 6)) : Rule signature where
  parameterCount := 6
  hypotheses := 3
  premise := ![term (.var 0) (.var 1) (.var 2), term (.var 0) (.var 1) (.var 3),
    substitution (.var 4) (.var 0) (.var 5)]
  conclusion := out

theorem identitySubSchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 6))
    (valid : ∀ Γ Δ A x y σ, out.eval (algebra M)
      ![.context Γ, .family Γ A, .term Γ A x, .term Γ A y, .context Δ, .substitution Δ Γ σ]) :
    Satisfies (algebra M) (identitySubSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, x, hΓ, hA, hx⟩
  rcases h 1 with ⟨Γ', A', y, hΓ', hA', hy⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  change ρ 1 = .family Γ A at hA
  change ρ 1 = .family Γ A' at hA'
  have eA := eq_of_heq (Value.family.inj (hA'.symm.trans hA)).2
  subst A'
  rcases h 2 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have e : ρ = ![Value.context Γ, .family Γ A, .term Γ A x, .term Γ A y,
      .context Δ, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hx | exact hy | exact hΔ | exact hσ
  subst ρ
  exact valid Γ Δ A x y σ

abbrev identitySubRule := identitySubSchema
  (.eq (subTy (identity (.var 1) (.var 2) (.var 3)) (.var 5))
    (identity (subTy (.var 1) (.var 5)) (subTm (.var 2) (.var 5)) (subTm (.var 3) (.var 5))))

theorem identitySub_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) identitySubRule := by
  apply identitySubSchema_valid
  intro Γ Δ A x y σ
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, algebra, operation, DependentJudgments.operation, M.identity_sub]

abbrev telSchema (n : Nat) (out : Judgment (Fin 2)) : Rule signature where
  parameterCount := 2
  hypotheses := 1
  premise := ![telescope n (.var 0) (.var 1)]
  conclusion := out

theorem telSchema_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) (out : Judgment (Fin 2))
    (valid : ∀ Γ T, out.eval (algebra M) ![.context Γ, .telescope Γ n T]) :
    Satisfies (algebra M) (telSchema n out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, T, hΓ, hT⟩
  have e : ρ = ![Value.context Γ, .telescope Γ n T] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hT
  subst ρ
  exact valid Γ T

abbrev totalRule (n : Nat) := telSchema n (context (total (.var 1)))
abbrev projectionRule (n : Nat) := telSchema n
  (substitution (total (.var 1)) (.var 0) (projection (.var 1)))

theorem total_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) : Satisfies (algebra M) (totalRule n) := by
  apply telSchema_valid
  intro Γ T
  exact ⟨T.total, rfl⟩

theorem projection_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (projectionRule n) := by
  apply telSchema_valid
  intro Γ T
  exact ⟨T.total, Γ, T.projection, rfl, rfl, rfl⟩

abbrev telNilRule : Rule signature where
  parameterCount := 1
  hypotheses := 1
  premise := ![context (.var 0)]
  conclusion := telescope 0 (.var 0) (telNil (.var 0))

theorem telNil_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) telNilRule := by
  intro ρ h
  rcases h 0 with ⟨Γ, hΓ⟩
  change ρ 0 = .context Γ at hΓ
  refine ⟨Γ, .nil, hΓ, ?_⟩
  simp [Term.eval, algebra, operation, hΓ]

abbrev telConsRule (n : Nat) : Rule signature where
  parameterCount := 3
  hypotheses := 2
  premise := ![family (.var 0) (.var 1), telescope n (extend (.var 0) (.var 1)) (.var 2)]
  conclusion := telescope (n + 1) (.var 0) (telCons (.var 1) (.var 2))

theorem telCons_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (telConsRule n) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, hΓ, hA⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  have he : (extend (.var 0) (.var 1)).eval (algebra M) ρ = .context (M.extend Γ A) := by
    simp [Term.eval, algebra, DependentJudgments.operation, hΓ, hA]
  rcases h 1 with ⟨Γ', T, hΓ', hT⟩
  change (extend (.var 0) (.var 1)).eval (algebra M) ρ = .context Γ' at hΓ'
  have eΓ := Value.context.inj (he.symm.trans hΓ')
  subst Γ'
  change ρ 2 = .telescope (M.extend Γ A) n T at hT
  refine ⟨Γ, .cons A T, hΓ, ?_⟩
  simp [Term.eval, algebra, operation, hA, hT]

abbrev telSubSchema (n : Nat) (out : Judgment (Fin 4)) : Rule signature where
  parameterCount := 4
  hypotheses := 2
  premise := ![telescope n (.var 0) (.var 2), substitution (.var 1) (.var 0) (.var 3)]
  conclusion := out

theorem telSubSchema_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) (out : Judgment (Fin 4))
    (valid : ∀ Γ Δ T σ, out.eval (algebra M)
      ![.context Γ, .context Δ, .telescope Γ n T, .substitution Δ Γ σ]) :
    Satisfies (algebra M) (telSubSchema n out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, T, hΓ, hT⟩
  rcases h 1 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have e : ρ = ![Value.context Γ, .context Δ, .telescope Γ n T, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hT | exact hσ
  subst ρ
  exact valid Γ Δ T σ

abbrev pullbackRule (n : Nat) := telSubSchema n (telescope n (.var 1) (pullback (.var 2) (.var 3)))
abbrev tailMapRule (n : Nat) := telSubSchema n
  (substitution (total (pullback (.var 2) (.var 3))) (total (.var 2)) (tailMap (.var 2) (.var 3)))

theorem pullback_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (pullbackRule n) := by
  apply telSubSchema_valid
  intro Γ Δ T σ
  refine ⟨Δ, Telescope.pullback M.toStructuralModel T σ, rfl, ?_⟩
  simp [Term.eval, algebra, operation]

theorem tailMap_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (tailMapRule n) := by
  apply telSubSchema_valid
  intro Γ Δ T σ
  refine ⟨(Telescope.pullback M.toStructuralModel T σ).total, T.total,
    Telescope.liftSub M.toStructuralModel T σ, ?_, rfl, ?_⟩ <;>
    simp [Term.eval, algebra, operation]


abbrev tailSchema (n : Nat) (out : Judgment (Fin 4)) : Rule signature where
  parameterCount := 4
  hypotheses := 2
  premise := ![term (.var 0) (.var 1) (.var 2), telescope n (path (.var 1) (.var 2)) (.var 3)]
  conclusion := out

theorem tailSchema_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) (out : Judgment (Fin 4))
    (valid : ∀ Γ A x T, out.eval (algebra M)
      ![.context Γ, .family Γ A, .term Γ A x, .telescope (M.toStructuralModel.pathContext A x) n T]) :
    Satisfies (algebra M) (tailSchema n out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, x, hΓ, hA, hx⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  change ρ 2 = .term Γ A x at hx
  have hp : (path (.var 1) (.var 2)).eval (algebra M) ρ =
      .context (M.toStructuralModel.pathContext A x) := by
    simp [Term.eval, algebra, operation, hA, hx]
  rcases h 1 with ⟨Γ', T, hΓ', hT⟩
  change (path (.var 1) (.var 2)).eval (algebra M) ρ = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hp.symm.trans hΓ')
  subst Γ'
  have e : ρ = ![Value.context Γ, .family Γ A, .term Γ A x,
      .telescope (M.toStructuralModel.pathContext A x) n T] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hx | exact hT
  subst ρ
  exact valid Γ A x T

abbrev rootTailRule (n : Nat) := tailSchema n
  (substitution (total (pullback (.var 3) (root (.var 1) (.var 2)))) (total (.var 3))
    (rootTail (.var 1) (.var 2) (.var 3)))

theorem rootTail_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (rootTailRule n) := by
  apply tailSchema_valid
  intro Γ A x T
  refine ⟨(Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A x)).total,
    T.total, M.toStructuralModel.rootTail A x T, ?_, rfl, ?_⟩ <;>
    simp [Term.eval, algebra, operation]

abbrev pathSubRule := termSubSchema
  (substitution (path (subTy (.var 2) (.var 4)) (subTm (.var 3) (.var 4)))
    (path (.var 2) (.var 3)) (pathSub (.var 2) (.var 3) (.var 4)))

theorem pathSub_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) pathSubRule := by
  apply termSubSchema_valid
  intro Γ Δ A x σ
  refine ⟨M.toStructuralModel.pathContext (M.subTy A σ) (M.subTm x σ),
    M.toStructuralModel.pathContext A x, M.toStructuralModel.pathSub A x σ, ?_, ?_, ?_⟩ <;>
    simp [Term.eval, algebra, operation, DependentJudgments.operation]

abbrev tailSubSchema (n : Nat) (out : Judgment (Fin 6)) : Rule signature where
  parameterCount := 6
  hypotheses := 3
  premise := ![term (.var 0) (.var 1) (.var 2), telescope n (path (.var 1) (.var 2)) (.var 3),
    substitution (.var 4) (.var 0) (.var 5)]
  conclusion := out

theorem tailSubSchema_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) (out : Judgment (Fin 6))
    (valid : ∀ Γ Δ A x T σ, out.eval (algebra M)
      ![.context Γ, .family Γ A, .term Γ A x, .telescope (M.toStructuralModel.pathContext A x) n T,
        .context Δ, .substitution Δ Γ σ]) :
    Satisfies (algebra M) (tailSubSchema n out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, x, hΓ, hA, hx⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  change ρ 2 = .term Γ A x at hx
  have hp : (path (.var 1) (.var 2)).eval (algebra M) ρ =
      .context (M.toStructuralModel.pathContext A x) := by
    simp [Term.eval, algebra, operation, hA, hx]
  rcases h 1 with ⟨Γ', T, hΓ', hT⟩
  change (path (.var 1) (.var 2)).eval (algebra M) ρ = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hp.symm.trans hΓ')
  subst Γ'
  rcases h 2 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have e : ρ = ![Value.context Γ, .family Γ A, .term Γ A x,
      .telescope (M.toStructuralModel.pathContext A x) n T, .context Δ, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hx | exact hT | exact hΔ | exact hσ
  subst ρ
  exact valid Γ Δ A x T σ

abbrev pathTailRule (n : Nat) := tailSubSchema n
  (telescope n (path (subTy (.var 1) (.var 5)) (subTm (.var 2) (.var 5)))
    (pathTail (.var 1) (.var 2) (.var 3) (.var 5)))
abbrev pathTailMapRule (n : Nat) := tailSubSchema n
  (substitution (total (pathTail (.var 1) (.var 2) (.var 3) (.var 5))) (total (.var 3))
    (pathTailMap (.var 1) (.var 2) (.var 3) (.var 5)))
abbrev branchMapRule (n : Nat) := tailSubSchema n
  (substitution
    (total (pullback (pathTail (.var 1) (.var 2) (.var 3) (.var 5))
      (root (subTy (.var 1) (.var 5)) (subTm (.var 2) (.var 5)))))
    (total (pullback (.var 3) (root (.var 1) (.var 2))))
    (branchMap (.var 1) (.var 2) (.var 3) (.var 5)))

theorem pathTail_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (pathTailRule n) := by
  apply tailSubSchema_valid
  intro Γ Δ A x T σ
  refine ⟨M.toStructuralModel.pathContext (M.subTy A σ) (M.subTm x σ),
    M.toStructuralModel.pathTail A x T σ, ?_, ?_⟩ <;>
    simp [Term.eval, algebra, operation, DependentJudgments.operation]

theorem pathTailMap_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (pathTailMapRule n) := by
  apply tailSubSchema_valid
  intro Γ Δ A x T σ
  refine ⟨(M.toStructuralModel.pathTail A x T σ).total, T.total,
    M.toStructuralModel.pathTailMap A x T σ, ?_, rfl, ?_⟩ <;>
    simp [Term.eval, algebra, operation]

theorem branchMap_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (branchMapRule n) := by
  apply tailSubSchema_valid
  intro Γ Δ A x T σ
  refine ⟨(Telescope.pullback M.toStructuralModel (M.toStructuralModel.pathTail A x T σ)
    (M.toStructuralModel.rootSub (M.subTy A σ) (M.subTm x σ))).total,
    (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A x)).total,
    M.toStructuralModel.branchMap A x T σ, ?_, ?_, ?_⟩ <;>
    simp [Term.eval, algebra, operation, DependentJudgments.operation]

abbrev reindexBranchRule (n : Nat) := jSubSchema n
  (term
    (total (pullback (pathTail (.var 1) (.var 2) (.var 3) (.var 7))
      (root (subTy (.var 1) (.var 7)) (subTm (.var 2) (.var 7)))))
    (subTy (subTy (.var 4) (pathTailMap (.var 1) (.var 2) (.var 3) (.var 7)))
      (rootTail (subTy (.var 1) (.var 7)) (subTm (.var 2) (.var 7))
        (pathTail (.var 1) (.var 2) (.var 3) (.var 7))))
    (reindexBranch (.var 1) (.var 2) (.var 3) (.var 7) (.var 4) (.var 5)))

theorem reindexBranch_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (reindexBranchRule n) := by
  apply jSubSchema_valid
  intro p Δ σ
  rcases p with ⟨⟨⟨Γ, A, x⟩, k, T⟩, D, d⟩
  refine ⟨_, _, M.toStructuralModel.reindexBranch A x T σ D d, ?_, ?_, ?_⟩ <;>
    simp [Term.eval, algebra, operation, DependentJudgments.operation, substitutedEnvironment]

end SquareKit.Internal.DependentJudgments.Contextual
