import SquareKit.Internal.DependentJudgments.Templates
import SquareKit.Internal.DependentJudgments.ContextualMaps

/-! Model-map preservation has a typed boundary. Raw Horn equality may compare
invalid expressions; typed premises and results supply the definedness evidence
needed by the partial interpreter. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u v
variable {V : Type} {Ω : List (Judgment V)}

/-- Evidence of definedness is generated from source typing, not a semantic
condition that an ordinary author must prove at every interpretation. -/
inductive Defined (Ω : List (Judgment V)) : Expression V → Type where
  | context (h : Ctx (Ω := Ω) Γ) : Defined Ω Γ
  | family (h : Ty (Ω := Ω) Γ A) : Defined Ω A
  | term (h : Tm (Ω := Ω) Γ A t) : Defined Ω t
  | substitution (h : Sub (Ω := Ω) Δ Γ σ) : Defined Ω σ
  | telescope (h : Tel (Ω := Ω) n Γ T) : Defined Ω T

theorem Defined.sound {e : Expression V} (he : Defined Ω e)
    (M : PathTransport.Typed.Model.{u}) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M) ρ) : e.eval (algebra M) ρ ≠ .invalid := by
  cases he with
  | context h =>
    rcases interpret h M ρ hΩ with ⟨Γ, hΓ⟩
    change e.eval (algebra M) ρ = .context Γ at hΓ
    erw [hΓ]
    intro h; cases h
  | family h =>
    rcases interpret h M ρ hΩ with ⟨Γ, A, _, hA⟩
    change e.eval (algebra M) ρ = .family Γ A at hA
    erw [hA]
    intro h; cases h
  | term h =>
    rcases interpret h M ρ hΩ with ⟨Γ, A, t, _, _, ht⟩
    change e.eval (algebra M) ρ = .term Γ A t at ht
    erw [ht]
    intro h; cases h
  | substitution h =>
    rcases interpret h M ρ hΩ with ⟨Δ, Γ, σ, _, _, hσ⟩
    change e.eval (algebra M) ρ = .substitution Δ Γ σ at hσ
    erw [hσ]
    intro h; cases h
  | telescope h =>
    rcases interpret h M ρ hΩ with ⟨Γ, T, _, hT⟩
    change e.eval (algebra M) ρ = .telescope Γ _ T at hT
    erw [hT]
    intro h; cases h

/-- Positive guards already entail definedness of each argument. Equality
assumptions additionally retain source typing of both operands. -/
def TypedAssumptions (Ω : List (Judgment V)) : Prop :=
  ∀ s t, Atom.eq s t ∈ Ω → Nonempty (Defined Ω s) ∧ Nonempty (Defined Ω t)

theorem predicate_defined (M : PathTransport.Typed.Model.{u}) (p : signature.Predicate)
    (args : Fin (signature.arguments p) → Value M.toStructuralModel)
    (h : (algebra M).predicate p args) : ∀ i, args i ≠ .invalid := by
  cases p with
  | inl p =>
    cases p with
    | context =>
      rcases h with ⟨Γ, hΓ⟩
      intro i
      fin_cases i
      erw [hΓ]
      intro h; cases h
    | family =>
      rcases h with ⟨Γ, A, hΓ, hA⟩
      intro i
      fin_cases i
      · erw [hΓ]; intro h; cases h
      · erw [hA]; intro h; cases h
    | term =>
      rcases h with ⟨Γ, A, t, hΓ, hA, ht⟩
      intro i
      fin_cases i
      · erw [hΓ]; intro h; cases h
      · erw [hA]; intro h; cases h
      · erw [ht]; intro h; cases h
    | substitution =>
      rcases h with ⟨Δ, Γ, σ, hΔ, hΓ, hσ⟩
      intro i
      fin_cases i
      · erw [hΔ]; intro h; cases h
      · erw [hΓ]; intro h; cases h
      · erw [hσ]; intro h; cases h
  | inr p =>
    cases p with
    | telescope n =>
      rcases h with ⟨Γ, T, hΓ, hT⟩
      intro i
      fin_cases i
      · erw [hΓ]; intro h; cases h
      · erw [hT]; intro h; cases h

/-- Each source assumption transports under the specified model map. No
reflection of equality, sorting, or invalid values is needed. -/
theorem premises_map {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    (F : ModelMap M N) (typed : TypedAssumptions Ω) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M) ρ) :
    ∀ p ∈ Ω, p.eval (algebra N) (Value.map F.toStructuralMap ∘ ρ) := by
  intro p hp
  cases p with
  | eq s t =>
    rcases typed s t hp with ⟨⟨hs⟩, ⟨ht⟩⟩
    have h := congrArg (Value.map F.toStructuralMap) (hΩ (.eq s t) hp)
    change Value.map F.toStructuralMap (s.eval (algebra M) ρ) =
      Value.map F.toStructuralMap (t.eval (algebra M) ρ) at h
    erw [interpret_map F s ρ (hs.sound M ρ hΩ), interpret_map F t ρ (ht.sound M ρ hΩ)] at h
    exact h
  | pred p args =>
    have h := hΩ (.pred p args) hp
    have hd := predicate_defined M p (fun i => (args i).eval (algebra M) ρ) h
    have hm := (partialHom F).predicate p (fun i => (args i).eval (algebra M) ρ) h
    have e : (Value.map F.toStructuralMap ∘ fun i => (args i).eval (algebra M) ρ) =
        (fun i => (args i).eval (algebra N) (Value.map F.toStructuralMap ∘ ρ)) :=
      funext (fun i => interpret_map F (args i) ρ (hd i))
    change (algebra N).predicate p
      (Value.map F.toStructuralMap ∘ fun i => (args i).eval (algebra M) ρ) at hm
    erw [e] at hm
    exact hm

/-- The same derivation is admitted at the target interpretation. -/
theorem interpret_target {a : Judgment V} (d : Derivation theory Ω a)
    {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    (F : ModelMap M N) (typed : TypedAssumptions Ω) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M) ρ) :
    a.eval (algebra N) (Value.map F.toStructuralMap ∘ ρ) :=
  interpret d N _ (premises_map F typed ρ hΩ)

/-- Typing supplies the side condition for preservation of the retained value. -/
theorem Tm.interpret_map {Γ A t : Expression V} (ht : Tm (Ω := Ω) Γ A t)
    {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    (F : ModelMap M N) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M) ρ) :
    Value.map F.toStructuralMap (t.eval (algebra M) ρ) =
      t.eval (algebra N) (Value.map F.toStructuralMap ∘ ρ) :=
  Contextual.interpret_map F t ρ ((Defined.term ht).sound M ρ hΩ)

end SquareKit.Internal.DependentJudgments.Contextual
