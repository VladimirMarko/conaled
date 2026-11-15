import Mathlib.Data.Sigma.Basic
import Mathlib.Logic.Equiv.Defs

/-! Concrete dependent functions are exactly commuting squares between their
sum projections. This comparison concerns all fiber functions, with no chosen
cleavage to preserve. -/
namespace SquareKit.FamilySquares
universe u v w z
variable {Γ : Type u} {Δ : Type v} {Θ : Type w}
variable {A : Γ → Type z} {B : Δ → Type z} {D : Θ → Type z}

structure Square (f : Γ → Δ) (A : Γ → Type z) (B : Δ → Type z) where
  total : Sigma A → Sigma B
  commutes : ∀ x, (total x).1 = f x.1

/-- A dependent function and its square carry exactly the same information. -/
def equivalence (f : Γ → Δ) : ((γ : Γ) → A γ → B (f γ)) ≃ Square f A B where
  toFun g := ⟨fun x => ⟨f x.1, g x.1 x.2⟩, fun _ => rfl⟩
  invFun s γ a := cast (congrArg B (s.commutes ⟨γ,a⟩)) (s.total ⟨γ,a⟩).2
  left_inv _ := rfl
  right_inv s := by
    cases s with
    | mk total commutes =>
      dsimp
      congr 1
      funext x
      apply Sigma.ext (commutes x).symm
      exact (cast_heq _ _)

def Square.comp {f : Γ → Δ} {g : Δ → Θ} (s : Square f A B) (t : Square g B D) :
    Square (g ∘ f) A D where
  total := t.total ∘ s.total
  commutes x := (t.commutes (s.total x)).trans (congrArg g (s.commutes x))

/-- The correspondence preserves composition of actual dependent functions. -/
theorem equivalence_comp (f : Γ → Δ) (g : Δ → Θ)
    (s : (γ : Γ) → A γ → B (f γ)) (t : (δ : Δ) → B δ → D (g δ)) :
    equivalence (g ∘ f) (fun γ a => t (f γ) (s γ a)) =
      (equivalence f s).comp (equivalence g t) := rfl

theorem equivalence_id : equivalence (id : Γ → Γ) (A := A) (fun _ a => a) =
    (⟨id, fun _ => rfl⟩ : Square id A A) := by
  rfl

end SquareKit.FamilySquares
