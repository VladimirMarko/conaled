import SquareKit.Internal.Cubical.Judgments.NaturalsRules

namespace SquareKit.Cubical.Source.Naturals
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf
universe u

inductive Axiom where
  | formation | zero | successor | elimination | zeroBeta | successorBeta

def rule : Axiom → Rule signature
  | .formation => formationRule
  | .zero => zeroRule
  | .successor => successorRule
  | .elimination => eliminationRule
  | .zeroBeta => zeroBetaRule
  | .successorBeta => successorBetaRule

def theory := Sums.theory.extend extraSignature Axiom rule

noncomputable def model : GuardedTheory.Model.{0,u+1} theory where
  toAlgebra := algebra
  rules
    | .inl a => by
      intro ρ h
      simp only [theory, Theory.extend, Rule.inl, Atom.eval_inl,
        algebra, Algebra.restrictLeft, Sums.algebra] at h ⊢
      exact Sums.model.rules a ρ h
    | .inr .formation => formation_valid
    | .inr .zero => zero_valid
    | .inr .successor => successor_valid
    | .inr .elimination => elimination_valid
    | .inr .zeroBeta => zeroBeta_valid
    | .inr .successorBeta => successorBeta_valid

theorem interpret {V : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation theory Ω a) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra ρ) : a.eval algebra ρ :=
  d.sound model ρ h

end SquareKit.Cubical.Source.Naturals
