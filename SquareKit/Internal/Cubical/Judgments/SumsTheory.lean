import SquareKit.Internal.Cubical.Judgments.SumsRules
import SquareKit.Internal.Cubical.Judgments.SumsSubstitutionRules

namespace SquareKit.Cubical.Source.Sums
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf
universe u

inductive Axiom where
  | formation | pack | unpack | beta | eta | sigmaSub | elimination | eliminationBeta | packSub | unpackSub

def rule : Axiom → Rule signature
  | .formation => formationRule
  | .pack => packRule
  | .unpack => unpackRule
  | .beta => betaRule
  | .eta => etaRule
  | .sigmaSub => sigmaSubRule
  | .elimination => eliminationRule
  | .eliminationBeta => eliminationBetaRule
  | .packSub => packSubRule
  | .unpackSub => unpackSubRule

def theory := Products.theory.extend extraSignature Axiom rule

noncomputable def model : GuardedTheory.Model.{0,u+1} theory where
  toAlgebra := algebra
  rules
    | .inl a => by
      intro ρ h
      simp only [theory, Theory.extend, Rule.inl, Atom.eval_inl,
        algebra, Algebra.restrictLeft, Products.algebra] at h ⊢
      exact Products.model.rules a ρ h
    | .inr .formation => formation_valid
    | .inr .pack => pack_valid
    | .inr .unpack => unpack_valid
    | .inr .beta => beta_valid
    | .inr .eta => eta_valid
    | .inr .sigmaSub => sigmaSubRule_valid
    | .inr .elimination => elimination_valid
    | .inr .eliminationBeta => eliminationBetaRule_valid
    | .inr .packSub => packSubRule_valid
    | .inr .unpackSub => unpackSubRule_valid

theorem interpret {V : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation theory Ω a) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.Eval algebra ρ) : a.Eval algebra ρ :=
  d.sound model ρ h

end SquareKit.Cubical.Source.Sums
