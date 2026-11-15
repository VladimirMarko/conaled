import SquareKit.Internal.DependentJudgments.GeneratedContexts
import Mathlib.CategoryTheory.Category.Basic

/-! Generated substitutions with an explicit policy for primitive arrows.
The closed policy admits identity, composition, weakening, pairing and source
equality conversion. Type and term premises remain ordinary guarded proofs. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}

/-- Primitive substitutions admitted in addition to structural generation. -/
abbrev ArrowPolicy (V : Type) := Expression V → Expression V → Expression V → Prop

def closedArrows : ArrowPolicy V := fun _ _ _ => False
def hypothesisArrows (Ω : List (Judgment V)) : ArrowPolicy V :=
  fun Δ Γ σ => substitution Δ Γ σ ∈ Ω

/-- Object witnesses fix the finite context presentations. Arbitrary typed
terms may be paired, but an arbitrary substitution needs policy permission. -/
inductive GeneratedArrow (P : ArrowPolicy V) (Ω : List (Judgment V)) :
    {Δ Γ : Expression V} → GeneratedContext Ω Δ → GeneratedContext Ω Γ →
      Expression V → Type where
  | identity (hΓ : GeneratedContext Ω Γ) : GeneratedArrow P Ω hΓ hΓ (identitySub Γ)
  | comp {hΓ : GeneratedContext Ω Γ} {hΔ : GeneratedContext Ω Δ}
      {hΘ : GeneratedContext Ω Θ}
      (f : GeneratedArrow P Ω hΔ hΓ σ) (g : GeneratedArrow P Ω hΘ hΔ τ) :
      GeneratedArrow P Ω hΘ hΓ (Contextual.comp σ τ)
  | weaken (hΓ : GeneratedContext Ω Γ) (hA : Ty (Ω := Ω) Γ A) :
      GeneratedArrow P Ω (hΓ.extend hA) hΓ (Contextual.weaken Γ A)
  | pair {hΓ : GeneratedContext Ω Γ} {hΔ : GeneratedContext Ω Δ}
      (hA : Ty (Ω := Ω) Γ A) (f : GeneratedArrow P Ω hΔ hΓ σ)
      (ht : Tm (Ω := Ω) Δ (subTy A σ) t) :
      GeneratedArrow P Ω hΔ (hΓ.extend hA) (Contextual.pair A σ t)
  | convert {hΓ : GeneratedContext Ω Γ} {hΔ : GeneratedContext Ω Δ}
      (f : GeneratedArrow P Ω hΔ hΓ σ) (e : Equal (Ω := Ω) σ τ) :
      GeneratedArrow P Ω hΔ hΓ τ
  | generator (hΔ : GeneratedContext Ω Δ) (hΓ : GeneratedContext Ω Γ)
      (allowed : P Δ Γ σ) (typed : Sub (Ω := Ω) Δ Γ σ) :
      GeneratedArrow P Ω hΔ hΓ σ

namespace GeneratedArrow
variable {P : ArrowPolicy V}

def typing {hΔ : GeneratedContext Ω Δ} {hΓ : GeneratedContext Ω Γ}
    (f : GeneratedArrow P Ω hΔ hΓ σ) : Sub (Ω := Ω) Δ Γ σ :=
  match f with
  | .identity hΓ => hΓ.typing.identity
  | .comp f g => f.typing.comp g.typing
  | .weaken _ hA => hA.weaken
  | .pair hA f ht => Sub.pair hA f.typing ht
  | .convert f e => Derivation.conversion (T := theory) (.inl .substitution)
      (Fin.cases (.reflexive _) (Fin.cases (.reflexive _)
        (Fin.cases e (fun i => nomatch i)))) f.typing
  | .generator _ _ _ h => h

def compEquality {σ σ' τ τ' : Expression V}
    (hσ : Equal (Ω := Ω) σ σ') (hτ : Equal (Ω := Ω) τ τ') :
    Equal (Ω := Ω) (Contextual.comp σ τ) (Contextual.comp σ' τ') :=
  Derivation.congruence (T := theory) (.inl .comp)
    (Fin.cases hσ (Fin.cases hτ (fun i => nomatch i)))

/-- The canonical projection to empty is stable under every closed generated
arrow. This is a source derivation, not equality in one chosen model. -/
def empty_natural {hΔ : GeneratedContext Ω Δ} {hΓ : GeneratedContext Ω Γ}
    (f : GeneratedArrow closedArrows Ω hΔ hΓ σ) :
    Equal (Ω := Ω) (Contextual.comp hΓ.emptySubstitution σ) hΔ.emptySubstitution :=
  match f with
  | .identity hΓ => hΓ.emptySubstitution_typed.idRight
  | .comp (hΓ := hΓ) f g =>
      (Sub.assoc hΓ.emptySubstitution_typed f.typing g.typing).symmetric.transitive
        ((compEquality f.empty_natural (.reflexive _)).transitive g.empty_natural)
  | .weaken _ _ => .reflexive _
  | .pair (hΓ := hΓ) hA f ht =>
      (Sub.assoc hΓ.emptySubstitution_typed hA.weaken (Sub.pair hA f.typing ht)).transitive
        ((compEquality (.reflexive _) (hA.weakenPair f.typing ht)).transitive
          f.empty_natural)
  | .convert f e => (compEquality (.reflexive _) e).symmetric.transitive f.empty_natural
  | .generator _ _ h _ => False.elim h

/-- A closed generated arrow to empty equals the constructed projection. -/
def empty_unique {hΔ : GeneratedContext Ω Δ}
    (f : GeneratedArrow closedArrows Ω hΔ .empty σ) :
    Equal (Ω := Ω) σ hΔ.emptySubstitution :=
  f.typing.idLeft.symmetric.transitive f.empty_natural

/-- The constructed projection belongs to the same generated-arrow grammar. -/
def toEmpty (hΓ : GeneratedContext Ω Γ) :
    GeneratedArrow P Ω hΓ .empty hΓ.emptySubstitution :=
  match hΓ with
  | .empty => .identity .empty
  | .extend hΓ hA => .comp (toEmpty hΓ) (.weaken hΓ hA)

end GeneratedArrow

namespace GeneratedCategory

/-- Context expressions with their finite extension presentations. -/
def Object (_P : ArrowPolicy V) (Ω : List (Judgment V)) :=
  (Γ : Expression V) × GeneratedContext Ω Γ

abbrev Representative (P : ArrowPolicy V) (Δ Γ : Object P Ω) :=
  (σ : Expression V) × GeneratedArrow P Ω Δ.2 Γ.2 σ

def sourceEquality (P : ArrowPolicy V) (Δ Γ : Object P Ω) : Setoid (Representative P Δ Γ) where
  r f g := Nonempty (Equal (Ω := Ω) f.1 g.1)
  iseqv := ⟨fun f => ⟨.reflexive f.1⟩,
    fun ⟨h⟩ => ⟨h.symmetric⟩, fun ⟨h⟩ ⟨k⟩ => ⟨h.transitive k⟩⟩

def compose (P : ArrowPolicy V) {Γ Δ Θ : Object P Ω}
    (f : Quotient (sourceEquality P Γ Δ)) (g : Quotient (sourceEquality P Δ Θ)) :
    Quotient (sourceEquality P Γ Θ) :=
  Quotient.map₂ (fun f g => ⟨Contextual.comp g.1 f.1, .comp g.2 f.2⟩)
    (by
      intro f f' ⟨hf⟩ g g' ⟨hg⟩
      exact ⟨GeneratedArrow.compEquality hg hf⟩) f g

instance category (P : ArrowPolicy V) : Category (Object P Ω) where
  Hom Δ Γ := Quotient (sourceEquality P Δ Γ)
  id Γ := Quotient.mk _ ⟨identitySub Γ.1, .identity Γ.2⟩
  comp := compose P
  id_comp f := Quotient.inductionOn f fun f => Quotient.sound ⟨f.2.typing.idRight⟩
  comp_id f := Quotient.inductionOn f fun f => Quotient.sound ⟨f.2.typing.idLeft⟩
  assoc f g h := Quotient.inductionOn₃ f g h fun f g h =>
    Quotient.sound ⟨(Sub.assoc h.2.typing g.2.typing f.2.typing).symmetric⟩

def emptyObject (P : ArrowPolicy V) (Ω : List (Judgment V)) : Object P Ω := ⟨empty, .empty⟩

/-- Every hom-set into empty in the closed generated category has exactly one
element. Equality is the quotient by source derivability at fixed boundaries. -/
instance emptyUnique (Δ : Object closedArrows Ω) :
    Unique (Δ ⟶ emptyObject closedArrows Ω) where
  default := Quotient.mk _ ⟨Δ.2.emptySubstitution, GeneratedArrow.toEmpty Δ.2⟩
  uniq f := Quotient.inductionOn f fun f => Quotient.sound ⟨f.2.empty_unique⟩

end GeneratedCategory
end SquareKit.Internal.DependentJudgments.Contextual
