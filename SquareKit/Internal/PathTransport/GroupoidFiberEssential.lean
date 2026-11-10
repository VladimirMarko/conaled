import Mathlib.CategoryTheory.Equivalence

/-! Essential surjectivity follows by moving a target into a base-image fiber. -/
namespace SquareKit.Internal.PathTransport.GroupoidFiberEssential
open CategoryTheory
universe u v w z u₁ v₁ u₂ v₂
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
variable {B : Type u₁} [Category.{v₁} B] {K : Type u₂} [Category.{v₂} K]

/-- The target projection lifts base isomorphisms, and each fiber over a base
image lies in the total functor's essential image. No injectivity of base
objects or canonical representatives is required. -/
theorem essSurj_of_fibers (E : C ⥤ D) (Q : D ⥤ K) (R : B ⥤ K) [R.EssSurj]
    (lift : ∀ (y : D) (b : B), Nonempty (Q.obj y ≅ R.obj b) →
      ∃ z : D, Q.obj z = R.obj b ∧ Nonempty (y ≅ z))
    (fibers : ∀ (b : B) (z : D), Q.obj z = R.obj b → E.essImage z) : E.EssSurj where
  mem_essImage y := by
    obtain ⟨b, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage R (Q.obj y)
    obtain ⟨z,h,⟨i⟩⟩ := lift y b ⟨e.symm⟩
    obtain ⟨x,⟨j⟩⟩ := fibers b z h
    exact ⟨x,⟨j ≪≫ i.symm⟩⟩

end SquareKit.Internal.PathTransport.GroupoidFiberEssential
