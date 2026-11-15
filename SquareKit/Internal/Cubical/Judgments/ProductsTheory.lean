import SquareKit.Internal.Cubical.Judgments.ProductsRules

/-! General source judgment interpretation for the structural and dependent
product fragment. Source equalities remain literal equalities of tagged values. -/
namespace SquareKit.Cubical.Source.Products
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf
universe u

inductive Axiom where
  | formation | lam | app | beta | eta | piSub | lamSub | appSub

def rule : Axiom → Rule signature
  | .formation => formationRule
  | .lam => lamRule
  | .app => appRule
  | .beta => betaRule
  | .eta => etaRule
  | .piSub => piSubRule
  | .lamSub => lamSubRule
  | .appSub => appSubRule

def theory := coreTheory.extend extraSignature Axiom rule

noncomputable def model : GuardedTheory.Model.{0,u+1} theory where
  toAlgebra := algebra
  rules
    | .inl a => by
      intro ρ h
      simp only [theory, Theory.extend, Rule.inl, Atom.eval_inl] at h ⊢
      exact coreModel.rules a ρ h
    | .inr .formation => formation_valid
    | .inr .lam => lam_valid
    | .inr .app => app_valid
    | .inr .beta => beta_valid
    | .inr .eta => eta_valid
    | .inr .piSub => piSub_valid
    | .inr .lamSub => lamSub_valid
    | .inr .appSub => appSub_valid

theorem interpret {V : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation theory Ω a) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra ρ) : a.eval algebra ρ :=
  d.sound model ρ h

noncomputable def substitute {V W : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation theory Ω a) (σ : V → Expression W) :
    Derivation theory (Ω.map (Atom.subst σ)) (a.subst σ) := d.substitute σ

/-- Typing soundness recovers a coherent section in the declared dependent family. -/
theorem typed_result {V : Type} {Ω : List (Judgment V)} {γ a t : Expression V}
    (d : Derivation theory Ω (term γ a t)) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra ρ) (Γ : Context.{u}) (A : Family Γ)
    (hΓ : γ.eval algebra ρ = .context Γ) (hA : a.eval algebra ρ = .family Γ A) :
    ∃ b : Presheaf.Term A, t.eval algebra ρ = .term Γ A b := by
  have ht := interpret d ρ h
  change Source.predicate .term ![γ.eval algebra ρ,a.eval algebra ρ,t.eval algebra ρ] at ht
  rw [hΓ,hA] at ht
  exact Value.term_input Γ A _ ht

theorem typed_result_unique {V : Type} (ρ : V → Value.{u}) (t : Expression V)
    (Γ : Context.{u}) (A : Family Γ) (b c : Presheaf.Term A)
    (hb : t.eval algebra ρ = .term Γ A b) (hc : t.eval algebra ρ = .term Γ A c) : b = c :=
  eq_of_heq (Value.term.inj (hb.symm.trans hc)).2.2

/-- Schematic substitution interprets by changing the assignment. The source
subTy/subTm rules separately validate actual context maps and dependent reindexing. -/
theorem interpret_substitute {V W : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation theory Ω a) (σ : V → Expression W) (ρ : W → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra (fun x => (σ x).eval algebra ρ)) :
    (a.subst σ).eval algebra ρ := by
  rw [Atom.eval_subst]
  exact interpret d _ h

theorem familyEquality {V : Type} {Ω : List (Judgment V)} {a b : Expression V}
    (d : Derivation theory Ω (.eq a b)) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra ρ) (Γ : Context.{u}) (A B : Family Γ)
    (ha : a.eval algebra ρ = .family Γ A) (hb : b.eval algebra ρ = .family Γ B) : A = B := by
  have he := interpret d ρ h
  change a.eval algebra ρ = b.eval algebra ρ at he
  have hv := ha.symm.trans (he.trans hb)
  cases hv
  rfl

/-- Two source derivations of the same family conversion induce the same
transport of every dependent section. This uses the proved rule interpreter. -/
theorem conversion_independent {V : Type} {Ω : List (Judgment V)} {a b : Expression V}
    (d e : Derivation theory Ω (.eq a b)) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.eval algebra ρ) (Γ : Context.{u}) (A B : Family Γ)
    (ha : a.eval algebra ρ = .family Γ A) (hb : b.eval algebra ρ = .family Γ B)
    (t : Presheaf.Term A) :
    t.convert (familyEquality d ρ h Γ A B ha hb) =
      t.convert (familyEquality e ρ h Γ A B ha hb) :=
  Presheaf.Term.convert_independent _ _ t

end SquareKit.Cubical.Source.Products
