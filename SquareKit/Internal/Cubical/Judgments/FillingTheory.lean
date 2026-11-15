import SquareKit.Internal.Cubical.Judgments.FillingStructuralRules
import SquareKit.Internal.Cubical.Judgments.HcompRules
import SquareKit.Internal.Cubical.Judgments.TransportRules
import SquareKit.Internal.Cubical.Judgments.HcompSubstitutionRule
import SquareKit.Internal.Cubical.Judgments.TransportSubstitutionRule

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf
universe u

inductive Axiom where
  | faceTop | faceBot | restriction | inclusion | faceJoin | faceEndpoint (b : Bool)
  | faceSub | restrictedSub | providerSub
  | hcomp | hcompBoundary | hcompSub | transp | transpBoundary | transpSub

def rule : Axiom → Rule signature
  | .faceTop => faceTopRule
  | .faceBot => faceBotRule
  | .restriction => restrictionRule
  | .inclusion => inclusionRule
  | .faceJoin => faceJoinRule
  | .faceSub => faceSubRule
  | .restrictedSub => restrictedSubRule
  | .providerSub => providerSubRule
  | .hcomp => hcompRule
  | .hcompBoundary => hcompBoundaryRule
  | .hcompSub => hcompSubRule
  | .transp => transpRule
  | .transpBoundary => transpBoundaryRule
  | .transpSub => transpSubRule
  | .faceEndpoint b => faceEndpointRule b

def theory := Paths.theory.extend extraSignature Axiom rule

noncomputable def model : GuardedTheory.Model.{0,u+1} theory where
  toAlgebra := algebra
  rules
    | .inl a => by
      intro ρ h
      simp only [theory,Theory.extend,Rule.inl,Atom.eval_inl,
        algebra,Algebra.restrictLeft,Paths.algebra] at h ⊢
      exact Paths.model.rules a ρ h
    | .inr .faceTop => faceTop_valid
    | .inr .faceBot => faceBot_valid
    | .inr .restriction => restriction_valid
    | .inr .inclusion => inclusion_valid
    | .inr .faceJoin => faceJoin_valid
    | .inr .faceSub => faceSub_valid
    | .inr .restrictedSub => restrictedSub_valid
    | .inr .providerSub => providerSub_valid
    | .inr .hcomp => hcomp_valid
    | .inr .hcompBoundary => hcompBoundary_valid
    | .inr .hcompSub => hcompSub_valid
    | .inr .transp => transp_valid
    | .inr .transpBoundary => transpBoundary_valid
    | .inr .transpSub => transpSub_valid
    | .inr (.faceEndpoint b) => faceEndpoint_valid b

theorem interpret {V : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation theory Ω a) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra ρ) : a.eval algebra ρ :=
  d.sound model ρ h

theorem typed_result {V : Type} {Ω : List (Judgment V)} {γ a t : Expression V}
    (d : Derivation theory Ω (term γ a t)) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra ρ) (Γ : Context.{u}) (A : Family Γ)
    (hΓ : γ.eval algebra ρ = .context Γ) (hA : a.eval algebra ρ = .family Γ A) :
    ∃ b : Presheaf.Term A, t.eval algebra ρ = .term Γ A b := by
  have ht := interpret d ρ h
  change Source.predicate .term ![γ.eval algebra ρ,a.eval algebra ρ,t.eval algebra ρ] at ht
  rw [hΓ,hA] at ht
  exact Value.term_input Γ A _ ht

theorem familyEquality {V : Type} {Ω : List (Judgment V)} {a b : Expression V}
    (d : Derivation theory Ω (.eq a b)) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra ρ) (Γ : Context.{u}) (A B : Family Γ)
    (ha : a.eval algebra ρ = .family Γ A) (hb : b.eval algebra ρ = .family Γ B) : A = B := by
  have he := interpret d ρ h
  change a.eval algebra ρ = b.eval algebra ρ at he
  exact eq_of_heq (Value.family.inj (ha.symm.trans (he.trans hb))).2

theorem conversion_independent {V : Type} {Ω : List (Judgment V)} {a b : Expression V}
    (d e : Derivation theory Ω (.eq a b)) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra ρ) (Γ : Context.{u}) (A B : Family Γ)
    (ha : a.eval algebra ρ = .family Γ A) (hb : b.eval algebra ρ = .family Γ B)
    (t : Presheaf.Term A) :
    t.convert (familyEquality d ρ h Γ A B ha hb) =
      t.convert (familyEquality e ρ h Γ A B ha hb) :=
  Presheaf.Term.convert_independent _ _ t

theorem interpret_substitute {V W : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation theory Ω a) (σ : V → Expression W) (ρ : W → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra (fun x => (σ x).eval algebra ρ)) :
    (a.subst σ).eval algebra ρ := by
  rw [Atom.eval_subst]
  exact interpret d _ h

end SquareKit.Cubical.Source.Fillings
