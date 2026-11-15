import SquareKit.Internal.DependentJudgments.ReferenceDerived

/-! Interpretation of the bounded reference calculus through its proved forward
translation. Typed equality retains operand guards in this statement. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
universe u
variable {V : Type} {Ξ : List (Declaration V)}

def Claim.Valid (M : PathTransport.Typed.Model.{u})
    (ρ : V → Value M.toStructuralModel) : Claim V → Prop
  | .has b t => (b.encode t).eval (algebra M) ρ
  | .eq b s t => (b.encode s).eval (algebra M) ρ ∧
      (b.encode t).eval (algebra M) ρ ∧ s.eval (algebra M) ρ = t.eval (algebra M) ρ
  | .tail Γ T => (telescope T.length Γ (T.code Γ)).eval (algebra M) ρ

/-- The declaration interpretation must validate every supplied declaration.
The calculus separately checks their syntactic presuppositions at each use. -/
theorem sound (M : PathTransport.Typed.Model.{u}) (ρ : V → Value M.toStructuralModel)
    (hΞ : ∀ d ∈ Ξ, d.encode.eval (algebra M) ρ) {c : Claim V} (h : Derives Ξ c) :
    c.Valid M ρ := by
  have hs : ∀ p ∈ Ξ.map Declaration.encode,
      p.eval (TelescopePresentation.model M).toAlgebra ρ := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨d, hd, rfl⟩
    exact hΞ d hd
  cases c with
  | has b t => exact (translate h).sound (TelescopePresentation.model M) ρ hs
  | eq b s t =>
    exact ⟨(translate h.eqOperands.1).sound (TelescopePresentation.model M) ρ hs,
      (translate h.eqOperands.2).sound (TelescopePresentation.model M) ρ hs,
      (translate h).sound (TelescopePresentation.model M) ρ hs⟩
  | tail Γ T => exact (translate h).typing.sound (TelescopePresentation.model M) ρ hs

/-- An expression interpreted as the untyped failure value cannot be a term,
even when the raw engine proves its reflexive equation. -/
theorem not_term_of_invalid (M : PathTransport.Typed.Model.{u})
    (ρ : V → Value M.toStructuralModel)
    (hΞ : ∀ d ∈ Ξ, d.encode.eval (algebra M) ρ)
    {Γ A t : Expression V} (ht : t.eval (algebra M) ρ = .invalid) :
    ¬ Nonempty (Derives Ξ (.has (.tm Γ A) t)) := by
  intro ⟨h⟩
  rcases sound M ρ hΞ h with ⟨Γ', A', t', _, _, he⟩
  change t.eval (algebra M) ρ = .term Γ' A' t' at he
  rw [ht] at he
  cases he

end SquareKit.Internal.DependentJudgments.Contextual.Reference
