import Mathlib.CategoryTheory.Subfunctor.Basic

/-! Distributivity of subfunctors is computed pointwise. No Boolean complement
or decision procedure for a subfunctor is required. -/
set_option autoImplicit false
namespace CategoryTheory.Subfunctor
universe u v w
variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
instance : DistribLattice (Subfunctor F) where
  le_sup_inf _ _ _ j x h := by
    rcases h with ⟨h | h, k | k⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inl k
    · exact Or.inr ⟨h, k⟩
end CategoryTheory.Subfunctor
