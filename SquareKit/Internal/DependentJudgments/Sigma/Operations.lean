import SquareKit.Internal.DependentJudgments.Sigma.Syntax
import SquareKit.Internal.DependentJudgments.Sigma.Capability

/-! Totalized constructor operations. The family decoder checks the dependency
B : Ty(Γ.A); malformed inputs evaluate to invalid and cannot satisfy the rule
premises. The interpretation keeps the old contextual carrier and operations. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u

structure Inputs (M : StructuralModel.{u}) where
  context : M.Context
  first : M.Family context
  second : M.Family (M.extend context first)

noncomputable def inputs (M : StructuralModel.{u}) (a b : Value M) : Option (Inputs M) := do
  let .family Γ A := a | none
  let B ← b.familyAt (M.extend Γ A)
  pure ⟨Γ, A, B⟩

@[simp] theorem inputs_values (M : StructuralModel.{u}) (Γ : M.Context)
    (A : M.Family Γ) (B : M.Family (M.extend Γ A)) :
    inputs M (.family Γ A) (.family (M.extend Γ A) B) = some ⟨Γ, A, B⟩ := by
  simp [inputs]

noncomputable def operation (M : StructuralModel.{u}) (S : Capability M)
    (op : Operation) (args : Fin 2 → Value M) : Value M :=
  match inputs M (args 0) (args 1) with
  | none => .invalid
  | some p => match op with
    | .sigma => .family p.context (S.sigma p.first p.second)
    | .pack => .substitution (M.extend (M.extend p.context p.first) p.second)
        (M.extend p.context (S.sigma p.first p.second)) (S.pack p.first p.second)
    | .unpack => .substitution (M.extend p.context (S.sigma p.first p.second))
        (M.extend (M.extend p.context p.first) p.second) (S.unpack p.first p.second)

noncomputable def algebra (M : PathTransport.Typed.Model.{u})
    (S : Capability M.toStructuralModel) : Algebra signature where
  Carrier := Value M.toStructuralModel
  operation
    | .inl op => (Contextual.algebra M).operation op
    | .inr op => operation M.toStructuralModel S op
  predicate
    | .inl p => (Contextual.algebra M).predicate p
    | .inr p => nomatch p

@[simp] theorem restrict_algebra (M : PathTransport.Typed.Model.{u})
    (S : Capability M.toStructuralModel) : (algebra M S).restrictLeft = Contextual.algebra M := rfl

@[simp] theorem eval_old (M : PathTransport.Typed.Model.{u})
    (S : Capability M.toStructuralModel) {V : Type} (t : Contextual.Expression V)
    (ρ : V → Value M.toStructuralModel) :
    (t.inl extraSignature).eval (algebra M S) ρ = t.eval (Contextual.algebra M) ρ :=
  Term.eval_inl _ _ _

@[simp] theorem eval_old_judgment (M : PathTransport.Typed.Model.{u})
    (S : Capability M.toStructuralModel) {V : Type} (a : Contextual.Judgment V)
    (ρ : V → Value M.toStructuralModel) :
    (a.inl extraSignature).eval (algebra M S) ρ = a.eval (Contextual.algebra M) ρ :=
  Atom.eval_inl _ _ _

/-- Guard inversion retains the actual dependent second family. -/
theorem formationSchema_inputs (M : PathTransport.Typed.Model.{u})
    (S : Capability M.toStructuralModel) (out : Judgment (Fin 3))
    (ρ : Fin 3 → Value M.toStructuralModel)
    (h : ∀ i, ((formationSchema out).premise i).eval (algebra M S) ρ) :
    ∃ (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
      ρ = ![.context Γ, .family Γ A, .family (M.extend Γ A) B] := by
  rcases h 0 with ⟨Γ, A, hΓ, hA⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  have he : (extend (.var 0) (.var 1)).eval (algebra M S) ρ =
      .context (M.extend Γ A) := by
    simp [Term.eval, algebra, Contextual.algebra, DependentJudgments.operation, hΓ, hA]
  have hb := h 1
  change ∃ Γ' B, (extend (.var 0) (.var 1)).eval (algebra M S) ρ = .context Γ' ∧
    ρ 2 = .family Γ' B at hb
  rw [he] at hb
  rcases hb with ⟨Γ', B, hΓ', hB⟩
  have e := Value.context.inj hΓ'
  subst Γ'
  refine ⟨Γ, A, B, ?_⟩
  funext i
  fin_cases i <;> first | exact hΓ | exact hA | exact hB

theorem formationSchema_valid (M : PathTransport.Typed.Model.{u})
    (S : Capability M.toStructuralModel) (out : Judgment (Fin 3))
    (valid : ∀ (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
      out.eval (algebra M S) ![.context Γ, .family Γ A, .family (M.extend Γ A) B]) :
    Satisfies (algebra M S) (formationSchema out) := by
  intro ρ h
  rcases formationSchema_inputs M S out ρ h with ⟨Γ, A, B, rfl⟩
  exact valid Γ A B

end SquareKit.Internal.DependentJudgments.Sigma
