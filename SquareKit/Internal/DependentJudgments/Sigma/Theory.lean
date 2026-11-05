import SquareKit.Internal.DependentJudgments.Sigma.Pairing

/-! Admission of the chosen judgmental-η sum contract. Soundness follows from
actual constructor operations; clients supply derivations and source assumptions.
The earlier Id/J model and its selected data are retained by exact reduct.

This API is experimental. The [admission report](../../../../docs/research/dependent-constructor-admission.md)
records its chosen eta contract, supported interpretations and remaining gates. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u

inductive Axiom where
  | formation | pack | unpack | beta | eta | packOver | pair | split | splitBeta

def rule : Axiom → Rule signature
  | .formation => formationRule
  | .pack => packRule
  | .unpack => unpackRule
  | .beta => betaRule
  | .eta => etaRule
  | .packOver => packOverRule
  | .pair => pairRule
  | .split => splitRule
  | .splitBeta => splitBetaRule

abbrev theory := Contextual.theory.extend extraSignature Axiom rule

theorem rule_valid (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel) :
    ∀ a, Satisfies (algebra M S) (rule a)
  | .formation => formation_valid M S
  | .pack => pack_valid M S
  | .unpack => unpack_valid M S
  | .beta => beta_valid M S
  | .eta => eta_valid M S
  | .packOver => packOver_valid M S
  | .pair => pair_valid M S
  | .split => split_valid M S
  | .splitBeta => splitBeta_valid M S

noncomputable def model (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel) :
    GuardedTheory.Model theory where
  toAlgebra := algebra M S
  rules
    | .inl a => by
      intro ρ h
      simp only [theory, Theory.extend, Rule.inl, eval_old_judgment] at h ⊢
      exact (Contextual.model M).rules a ρ h
    | .inr a => rule_valid M S a

variable {V : Type} {Ω : List (Judgment V)}
abbrev Ctx (Γ : Expression V) := Derivation theory Ω (context Γ)
abbrev Ty (Γ A : Expression V) := Derivation theory Ω (family Γ A)
abbrev Tm (Γ A t : Expression V) := Derivation theory Ω (term Γ A t)
abbrev Sub (Δ Γ σ : Expression V) := Derivation theory Ω (substitution Δ Γ σ)
abbrev Equal (a b : Expression V) := Derivation theory Ω (.eq a b)

/-- The single ordinary-client soundness theorem. No constructor law or final
preservation equation is supplied by the proof author. -/
theorem interpret {a : Judgment V} (d : Derivation theory Ω a)
    (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel)
    (ρ : V → Value M.toStructuralModel) (h : ∀ p ∈ Ω, p.eval (algebra M S) ρ) :
    a.eval (algebra M S) ρ := d.sound (model M S) ρ h

/-- Raw simultaneous source substitution preserves admitted derivations. This
is distinct from the semantic stability laws of a reindexed constructor. -/
noncomputable def substitute {W : Type} {a : Judgment V} (d : Derivation theory Ω a)
    (σ : V → Expression W) : Derivation theory (Ω.map (Atom.subst σ)) (a.subst σ) := d.substitute σ

/-- Every old argument is retained without changes to its chosen source terms. -/
noncomputable def retain {Ω : List (Contextual.Judgment V)} {a : Contextual.Judgment V}
    (d : Derivation Contextual.theory Ω a) :
    Derivation theory (Ω.map (Atom.inl extraSignature)) (a.inl extraSignature) := d.inl rule

/-- Reduct recovers the actual prior interpreter, including Id and selected J. -/
theorem reduct (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel) :
    (model M S).restrictLeft = Contextual.model M := rfl

end SquareKit.Internal.DependentJudgments.Sigma
