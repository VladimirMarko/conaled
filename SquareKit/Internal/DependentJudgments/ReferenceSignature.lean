import SquareKit.Internal.DependentJudgments.ReferenceSubstitution

/-! The conventional declaration boundary: fresh primitive leaves are declared
only after their context and type are formed. Equality axioms have two already
formed operands. General assertion lists remain a separate supported input. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
variable {V : Type}

def Declaration.name : Declaration V → Option V
  | .family _ (.var v) => some v
  | .term _ _ (.var v) => some v
  | _ => none

def Fresh (v : V) (Ξ : List (Declaration V)) : Prop :=
  ∀ d ∈ Ξ, d.name ≠ some v

inductive WellFormedSignature : List (Declaration V) → Type where
  | nil : WellFormedSignature []
  | family {Ξ : List (Declaration V)} {Γ : Expression V} (v : V) :
      WellFormedSignature Ξ → Derives Ξ (.has .ctx Γ) → Fresh v Ξ →
      WellFormedSignature (Ξ ++ [.family Γ (.var v)])
  | term {Ξ : List (Declaration V)} {Γ A : Expression V} (v : V) :
      WellFormedSignature Ξ → Derives Ξ (.has (.ty Γ) A) → Fresh v Ξ →
      WellFormedSignature (Ξ ++ [.term Γ A (.var v)])
  | familyEq {Ξ : List (Declaration V)} {Γ A B : Expression V} :
      WellFormedSignature Ξ → Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has (.ty Γ) B) →
      WellFormedSignature (Ξ ++ [.familyEq Γ A B])
  | termEq {Ξ : List (Declaration V)} {Γ A s t : Expression V} :
      WellFormedSignature Ξ → Derives Ξ (.has (.tm Γ A) s) → Derives Ξ (.has (.tm Γ A) t) →
      WellFormedSignature (Ξ ++ [.termEq Γ A s t])

/-- This specification excludes primitive context and substitution declarations
by construction; it does not assert consistency of arbitrary equality axioms. -/
def Declaration.IsConventional : Declaration V → Prop
  | .family _ e => ∃ v, e = .var v
  | .term _ _ e => ∃ v, e = .var v
  | .familyEq _ _ _ => True
  | .termEq _ _ _ _ => True

theorem WellFormedSignature.declarations {Ξ : List (Declaration V)}
    (h : WellFormedSignature Ξ) : ∀ d ∈ Ξ, d.IsConventional := by
  induction h with
  | nil => simp
  | family v _ _ _ ih =>
    intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact ih d hd
    · exact ⟨v, rfl⟩
  | term v _ _ _ ih =>
    intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact ih d hd
    · exact ⟨v, rfl⟩
  | familyEq _ _ _ ih =>
    intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact ih d hd
    · trivial
  | termEq _ _ _ ih =>
    intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact ih d hd
    · trivial

end SquareKit.Internal.DependentJudgments.Contextual.Reference
