import SquareKit.Internal.Cubical.Judgments.IntervalsRules

namespace SquareKit.Cubical.Source.Intervals
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf
universe u

inductive Axiom where
  | formation
  | intervalSub
  | dimensionSub {n : ℕ} (e : Expr (Fin n))
  | dimension {n : ℕ} (e : Expr (Fin n))
  | variable {n : ℕ} (k : Fin n)
  | conversion {n : ℕ} {e e' : Expr (Fin n)} (h : Expr.Conv e e')
  | composition {m n : ℕ} (e : Expr (Fin m)) (σ : Fin m → Expr (Fin n))

def rule : Axiom → Rule signature
  | .formation => formationRule
  | .intervalSub => intervalSubRule
  | .dimensionSub e => dimensionSubRule e
  | .dimension e => dimensionRule e
  | .variable k => variableRule k
  | .conversion (e := e) (e' := e') _ => conversionRule e e'
  | .composition e σ => compositionRule e σ

def theory := Naturals.theory.extend extraSignature Axiom rule

noncomputable def model : GuardedTheory.Model.{0,u+1} theory where
  toAlgebra := algebra
  rules
    | .inl a => by
      intro ρ h
      simp only [theory,Theory.extend,Rule.inl,Atom.eval_inl,
        algebra,Algebra.restrictLeft,Naturals.algebra] at h ⊢
      exact Naturals.model.rules a ρ h
    | .inr .formation => formation_valid
    | .inr .intervalSub => intervalSub_valid
    | .inr (.dimensionSub e) => dimensionSub_valid e
    | .inr (.dimension e) => dimension_valid e
    | .inr (.variable k) => variable_valid k
    | .inr (.conversion h) => conversion_valid h
    | .inr (.composition e σ) => composition_valid e σ

theorem interpret {V : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation theory Ω a) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra ρ) : a.eval algebra ρ :=
  d.sound model ρ h

end SquareKit.Cubical.Source.Intervals
