import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! Faithfulness of groupoid maps can be checked on vertical automorphisms. -/
namespace SquareKit.Internal.PathTransport.GroupoidFiberFaithful
open CategoryTheory
universe u v w z u₁ v₁ u₂ v₂
variable {C : Type u} [Groupoid.{v} C] {D : Type w} [Groupoid.{z} D]

/-- Trivial kernels on endomorphisms detect equality of arbitrary retained arrows. -/
theorem faithful_of_kernel (E : C ⥤ D)
    (kernel : ∀ (x : C) (f : x ⟶ x), E.map f = 𝟙 (E.obj x) → f = 𝟙 x) :
    E.Faithful where
  map_injective {x y} f g h := by
    have hk : f ≫ inv g = 𝟙 x := kernel x (f ≫ inv g) (by simp [h])
    have := congrArg (fun q => q ≫ g) hk
    simpa using this

variable {B : Type u₁} [Category.{v₁} B] {K : Type u₂} [Category.{v₂} K]

/-- With a faithful base comparison, only the vertical kernel remains.
The square is an equality of complete functors; no splitting-preservation or
strict naturality of extracted fiber maps is assumed. -/
theorem faithful_of_vertical_kernel (E : C ⥤ D) (P : C ⥤ B) (Q : D ⥤ K)
    (R : B ⥤ K) [R.Faithful] (square : E ⋙ Q = P ⋙ R)
    (kernel : ∀ (x : C) (f : x ⟶ x), P.map f = 𝟙 (P.obj x) →
      E.map f = 𝟙 (E.obj x) → f = 𝟙 x) : E.Faithful :=
  faithful_of_kernel E (fun x f hf => by
    have h : (E ⋙ Q).map f = (E ⋙ Q).map (𝟙 x) := by simp [hf]
    rw [square] at h
    have hp : P.map f = P.map (𝟙 x) := R.map_injective h
    exact kernel x f (by simpa using hp) hf)

end SquareKit.Internal.PathTransport.GroupoidFiberFaithful
