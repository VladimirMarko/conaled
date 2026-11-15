import Examples.CoherentGuardedJudgments

/-! Fresh-command comparison is inherited by an authored template, then
composed with the constructed coherent comparison of its interpreted J. -/
namespace Examples.GuardedCommandComparisons
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.CoherentTypePresentations
open SquareKit.Internal.PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

abbrev assumptions (n : Nat) : List (Contextual.Judgment (Fin 8)) := List.ofFn (jSubRule n).premise

def command (n : Nat) : Command (assumptions n) (.var 0) (.var 1) (.var 2) where
  point := .hypothesis (List.mem_ofFn.mpr ⟨0, rfl⟩)
  length := n
  tail := .var 3
  tailTyping := .hypothesis (List.mem_ofFn.mpr ⟨1, rfl⟩)
  motive := .var 4
  motiveTyping := .hypothesis (List.mem_ofFn.mpr ⟨2, rfl⟩)
  branch := .var 5
  branchTyping := .hypothesis (List.mem_ofFn.mpr ⟨3, rfl⟩)

def substitution (n : Nat) : Sub (Ω := assumptions n) (.var 6) (.var 0) (.var 7) :=
  .hypothesis (List.mem_ofFn.mpr ⟨4, rfl⟩)

theorem inputs (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
    (p : Problem M.toStructuralModel) (Δ : M.Context) (σ : M.Substitution Δ p.context) :
    ∀ a ∈ assumptions p.length,
      a.eval (Contextual.algebra M) (substitutedEnvironment M.toStructuralModel p Δ σ) := by
  intro a ha
  rcases List.mem_ofFn.mp ha with ⟨i, rfl⟩
  rcases p with ⟨⟨⟨Γ, A, x⟩, n, T⟩, D, d⟩
  change Fin 5 at i
  fin_cases i
  · exact ⟨Γ, A, x, rfl, rfl, rfl⟩
  · refine ⟨M.toStructuralModel.pathContext A x, T, ?_, rfl⟩
    simp [Term.eval, Contextual.algebra, Contextual.operation, substitutedEnvironment]
  · exact ⟨T.total, D, rfl, rfl⟩
  · refine ⟨_, _, d, ?_, ?_, rfl⟩ <;>
      simp [Term.eval, Contextual.algebra, Contextual.operation,
        SquareKit.Internal.DependentJudgments.operation, substitutedEnvironment]
  · exact ⟨Δ, Γ, σ, rfl, rfl, rfl⟩

noncomputable def evaluatedFresh (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
    (p : Problem M.toStructuralModel) (Δ : M.Context) (σ : M.Substitution Δ p.context) :
    Value M.toStructuralModel :=
  ((command p.length).fresh (substitution p.length)).expression.eval
    (Contextual.algebra M) (substitutedEnvironment M.toStructuralModel p Δ σ)

/-- This equation uses the authored comparison derivation. It identifies the
fresh recipe with the substituted original output, including its result type. -/
theorem evaluatedFresh_value (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
    (p : Problem M.toStructuralModel) (Δ : M.Context) (σ : M.Substitution Δ p.context) :
    evaluatedFresh M p Δ σ =
      .term (M.toStructuralModel.pathTail p.family p.term p.telescope σ).total
        (M.subTy p.motive (M.toStructuralModel.pathTailMap p.family p.term p.telescope σ))
        (M.subTm (M.j p.family p.term p.telescope p.motive p.branch)
          (M.toStructuralModel.pathTailMap p.family p.term p.telescope σ)) := by
  have h := interpret ((command p.length).substituted_eq_fresh (substitution p.length))
    M (substitutedEnvironment M.toStructuralModel p Δ σ) (inputs M p Δ σ)
  rcases p with ⟨⟨⟨Γ, A, x⟩, n, T⟩, D, d⟩
  change _ = evaluatedFresh M _ Δ σ at h
  rw [← h]
  simp [command, Command.expression, Term.eval, Contextual.algebra,
    Contextual.operation, substitutedEnvironment, SquareKit.Internal.DependentJudgments.operation]

section Coherent
variable (Base : Type u) (Fiber : Base → Type u)
local notation "M" => NativeType.model Base Fiber
local notation "S" => NativeType.structuralModel Base Fiber
variable {Γ Δ : Type u} {e : Γ ≃ Δ} {A : Γ → Type u} {B : Δ → Type u}
variable (f : FamilyComparison e A B) (x : (γ : Γ) → A γ) {n : Nat}
variable {T : Telescope (NativeType.structuralModel Base Fiber)
  ((NativeType.structuralModel Base Fiber).pathContext A ⟨x⟩) n}
variable {U : Telescope (NativeType.structuralModel Base Fiber)
  ((NativeType.structuralModel Base Fiber).pathContext B ⟨f.term x⟩) n}
variable (tails : TelescopeComparison Base Fiber (f.path x) T U)
variable {C : T.total → Type u} {D : U.total → Type u}
variable (motives : FamilyComparison tails.total C D)

/-- Any simultaneous substitution of the authored command inherits its
specified coherent output comparison. The left side is the fresh recipe; its
comparison with substitution of the original recipe was generated above. -/
theorem fresh_coherent_observation
    (branch : (γ : (Telescope.pullback S T ((S).rootSub A ⟨x⟩)).total) →
      C (((S).rootTail A ⟨x⟩ T).down γ))
    {Ξ : Type u} (σ : Ξ → Γ)
    (z : ((S).pathTail A ⟨x⟩ T ⟨σ⟩).total) :
    Option.map
      (fun t => motives (((S).pathTailMap A ⟨x⟩ T ⟨σ⟩).down z) (t.down z))
      ((evaluatedFresh M
        (CoherentGuardedJudgments.sourceProblem Base Fiber x branch) Ξ ⟨σ⟩).termAt
          ((S).pathTail A ⟨x⟩ T ⟨σ⟩).total
          ((S).subTy C ((S).pathTailMap A ⟨x⟩ T ⟨σ⟩))) =
    Option.map (fun t => t.down (tails.total (((S).pathTailMap A ⟨x⟩ T ⟨σ⟩).down z)))
      ((CoherentGuardedJudgments.evaluated Base Fiber
        (CoherentGuardedJudgments.targetProblem Base Fiber f x tails motives branch)).termAt
          U.total D) := by
  rw [evaluatedFresh_value, CoherentGuardedJudgments.evaluated_value]
  simp only [CoherentGuardedJudgments.sourceProblem, CoherentGuardedJudgments.targetProblem,
    NativeType.model, Value.termAt_term, Option.map_some]
  have h := congrFun (contextualJ_compare f x tails motives ⟨branch⟩)
    (tails.total (((S).pathTailMap A ⟨x⟩ T ⟨σ⟩).down z))
  rw [FamilyComparison.term_apply] at h
  exact congrArg some h

end Coherent
namespace FiniteOptionExample
open CoherentTypePresentations.FiniteOption
local notation "M₀" => NativeType.model Nat (fun n => Fin (n + 1))
local notation "S₀" => NativeType.structuralModel Nat (fun n => Fin (n + 1))

def shift (p : FiniteOption.Base) : FiniteOption.Base := (p.1 + 1, p.2)
abbrev shiftedTail := (S₀).pathTail direct ⟨zero⟩ sourceTail ⟨shift⟩
def shiftedBranchPoint :
    (Telescope.pullback S₀ shiftedTail
      ((S₀).rootSub ((S₀).subTy direct ⟨shift⟩) ((S₀).subTm ⟨zero⟩ ⟨shift⟩))).total :=
  ⟨⟨(2, false), (⟨2, by decide⟩ : Fin 4)⟩, (⟨1, by decide⟩ : Fin 3)⟩
def shiftedPoint : shiftedTail.total :=
  ((S₀).rootTail ((S₀).subTy direct ⟨shift⟩) ((S₀).subTm ⟨zero⟩ ⟨shift⟩) shiftedTail).down
    shiftedBranchPoint

theorem shifted_point_maps_to_sample :
    ((S₀).pathTailMap direct ⟨zero⟩ sourceTail ⟨shift⟩).down shiftedPoint = sampleSource := rfl

/-- A nonidentity base substitution, a fresh J command, and changed dependent
presentations meet in one observed equality inherited from the builders. -/
theorem fresh_selected_code :
    Option.map
      (fun t => motives sampleSource (t.down shiftedPoint))
      ((evaluatedFresh M₀ CoherentGuardedJudgments.FiniteOptionExample.source
          FiniteOption.Base ⟨shift⟩).termAt shiftedTail.total
        ((S₀).subTy sourceMotive ((S₀).pathTailMap direct ⟨zero⟩ sourceTail ⟨shift⟩))) =
      some (some (⟨1, by decide⟩ : Fin 3)) := by
  have h := fresh_coherent_observation Nat (fun n => Fin (n + 1)) comparison zero tails motives
    sourceBranch.down shift shiftedPoint
  exact h.trans CoherentGuardedJudgments.FiniteOptionExample.target_recipe_selected

end FiniteOptionExample
end Examples.GuardedCommandComparisons
