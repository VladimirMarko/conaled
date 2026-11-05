import SquareKit.Internal.DependentJudgments.PairComposition

/-! Empty-tail reduction of structural reindexing data. J itself keeps its
primitive substitution law; these equations unfold its constructed arguments. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

theorem jSubSchema_valid_length (M : PathTransport.Typed.Model.{u}) (n : Nat)
    (out : Judgment (Fin 8))
    (valid : ∀ (p : Problem M.toStructuralModel), p.length = n → ∀ (Δ : M.Context) (σ : M.Substitution Δ p.context),
      out.eval (algebra M) (substitutedEnvironment M.toStructuralModel p Δ σ)) :
    Satisfies (algebra M) (jSubSchema n out) := by
  intro ρ h
  let ρ₀ : Fin 6 → Value M.toStructuralModel := fun i => ρ (i.castAdd 2)
  have h₀ : ∀ i, ((jRule n).premise i).eval (algebra M) ρ₀ := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1 | exact h 2 | exact h 3
  rcases jSchema_inputs M n _ ρ₀ h₀ with ⟨p, hn, hp⟩
  have hΓ := congrFun hp 0
  change ρ 0 = .context p.context at hΓ
  rcases h 4 with ⟨Δ, Γ, σ, hΔ, hΓ', hσ⟩
  change ρ 6 = .context Δ at hΔ
  change ρ 0 = .context Γ at hΓ'
  change ρ 7 = .substitution Δ Γ σ at hσ
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ
  have e : ρ = substitutedEnvironment M.toStructuralModel p Δ σ := by
    funext i
    fin_cases i
    · exact congrFun hp 0
    · exact congrFun hp 1
    · exact congrFun hp 2
    · exact congrFun hp 3
    · exact congrFun hp 4
    · exact congrFun hp 5
    · exact hΔ
    · exact hσ
  subst ρ
  exact valid p hn Δ σ


abbrev pathTailNilRule := tailSubSchema 0 (.eq
  (pathTail (.var 1) (.var 2) (.var 3) (.var 5))
  (telNil (path (subTy (.var 1) (.var 5)) (subTm (.var 2) (.var 5)))))
abbrev pathTailMapNilRule := tailSubSchema 0 (.eq
  (pathTailMap (.var 1) (.var 2) (.var 3) (.var 5)) (pathSub (.var 1) (.var 2) (.var 5)))
abbrev reindexBranchNilRule := jSubSchema 0 (.eq
  (reindexBranch (.var 1) (.var 2) (.var 3) (.var 7) (.var 4) (.var 5)) (subTm (.var 5) (.var 7)))

theorem pathTailNil_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) pathTailNilRule := by
  apply tailSubSchema_valid
  intro Γ Δ A x T σ
  cases T
  simp [Atom.eval, Term.eval, FinitaryTerm.fold, algebra, operation, DependentJudgments.operation,
    StructuralModel.pathTail, Telescope.pullback, Telescope.reindex]

theorem pathTailMapNil_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) pathTailMapNilRule := by
  apply tailSubSchema_valid
  intro Γ Δ A x T σ
  cases T
  simp [Atom.eval, Term.eval, FinitaryTerm.fold, algebra, operation,
    StructuralModel.pathTail, StructuralModel.pathTailMap, Telescope.pullback, Telescope.liftSub,
    Telescope.reindex, Telescope.total]

theorem reindexBranchNil_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) reindexBranchNilRule := by
  apply jSubSchema_valid_length
  intro p hn Δ σ
  rcases p with ⟨⟨⟨Γ, A, x⟩, n, T⟩, D, d⟩
  change n = 0 at hn
  subst n
  cases T
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, FinitaryTerm.fold, algebra, operation, DependentJudgments.operation, substitutedEnvironment]
  simp only [StructuralModel.pathTail, StructuralModel.pathTailMap, StructuralModel.rootTail,
    Telescope.pullback, Telescope.liftSub, Telescope.reindex, Telescope.total, Value.termIn_term]
  apply Value.term_eq
  · simpa [StructuralModel.pathTail, StructuralModel.pathTailMap, StructuralModel.rootTail,
      StructuralModel.branchMap, Telescope.square, Telescope.pullback, Telescope.liftSub, Telescope.reindex]
      using M.toStructuralModel.branchMap_type A x .nil σ D
  · unfold StructuralModel.reindexBranch
    apply (cast_heq _ _).trans
    have hb : M.branchMap A x Telescope.nil σ = σ := by
      unfold StructuralModel.branchMap
      rw [Telescope.square]
    rw [hb]

end SquareKit.Internal.DependentJudgments.Contextual
