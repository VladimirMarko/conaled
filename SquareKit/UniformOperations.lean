import Mathlib.Data.Fin.Basic

/-! A checked comparison of variable syntax with uniform semantic operations.
The naturality condition is extra evidence; Lean polymorphism alone supplies
no such theorem. This is the variable fragment, not dependent-syntax initiality. -/
namespace SquareKit

structure UniformOperation (n : Nat) where
  run : (A : Type) → (Fin n → A) → A
  natural : ∀ (A B : Type) (f : A → B) (ρ : Fin n → A),
    f (run A ρ) = run B (f ∘ ρ)

namespace UniformOperation
variable {n : Nat}

def fromVariable (i : Fin n) : UniformOperation n where
  run _ ρ := ρ i
  natural _ _ _ _ := rfl

def selected (t : UniformOperation n) : Fin n := t.run (Fin n) id

theorem reconstruction (t : UniformOperation n) (A : Type) (ρ : Fin n → A) :
    t.run A ρ = ρ t.selected := (t.natural (Fin n) A ρ id).symm

@[ext] theorem ext {s t : UniformOperation n} (h : s.run = t.run) : s = t := by
  cases s; cases t; cases h; rfl

def syntaxEquiv : Fin n ≃ UniformOperation n where
  toFun := fromVariable
  invFun := selected
  left_inv _ := rfl
  right_inv t := by
    apply ext
    funext A ρ
    exact (t.reconstruction A ρ).symm

/-- There is no uniform closed element of every carrier, even when an
unrestricted function may choose an element of each nonempty carrier. -/
theorem no_closed : IsEmpty (UniformOperation 0) := ⟨fun t => Fin.elim0 t.selected⟩

end UniformOperation

/-- Restricting to inhabited carriers still does not make arbitrary selection
natural under equivalences: Bool negation has no fixed point. -/
theorem no_equivariant_choice
    (choose : (A : Type) → Nonempty A → A) :
    ¬ (∀ (A : Type) (h : Nonempty A) (e : A ≃ A), e (choose A h) = choose A h) := by
  intro h
  let e : Bool ≃ Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩
  have hh := h Bool ⟨false⟩ e
  cases hchoose : choose Bool ⟨false⟩ <;> simp [e, hchoose] at hh

end SquareKit
