import SquareKit.Internal.ArrowPushout
import SquareKit.Internal.SierpinskiGeneric
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! The pushout interpretation fixes constant arrows and interprets the generic
proposition as its parameter. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.ArrowPushout
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPushouts C]
variable (P : C)

/-- A constant arrow's pushout is its common endpoint. -/
def diagonalObj (X : C) :
    (interpretation P).obj ((ArrowGeometry.diagonal C).obj X) ≅ X where
  hom := pushout.desc (𝟙 X) (snd P X) (by simp [ArrowGeometry.diagonal])
  inv := pushout.inl _ _
  hom_inv_id := by
    apply pushout.hom_ext
    · simp [interpretation]
    · simp only [pushout.inr_desc_assoc]
      simpa [ArrowGeometry.diagonal, interpretation] using (pushout.condition
        (f := snd P X) (g := P ◁ ((ArrowGeometry.diagonal C).obj X).hom))
  inv_hom_id := by simp

@[reassoc (attr := simp)] theorem diagonalObj_inl (X : C) :
    pushout.inl (snd P X) (P ◁ (𝟙 X)) ≫ (diagonalObj P X).hom = 𝟙 X := by
  simp [diagonalObj, ArrowGeometry.diagonal]

/-- The base comparison is natural in the common endpoint. -/
def diagonalIso : ArrowGeometry.diagonal C ⋙ interpretation P ≅ 𝟭 C :=
  NatIso.ofComponents (diagonalObj P) (by
    intro X Y f
    apply pushout.hom_ext <;>
      simp [diagonalObj, interpretation, ArrowGeometry.diagonal, Category.assoc])

/-- Changing the parameter leaves the specified base comparison unchanged. -/
theorem changeParameter_over {Q : C} (f : P ⟶ Q) :
    CategoryTheory.Functor.whiskerLeft (ArrowGeometry.diagonal C) (changeParameter P f) ≫ (diagonalIso Q).hom =
      (diagonalIso P).hom := by
  ext X
  apply pushout.hom_ext <;>
    simp [changeParameter, diagonalIso, diagonalObj, ArrowGeometry.diagonal, Category.assoc]

variable [HasInitial C] [HasTerminal C] [HasStrictInitialObjects C]

/-- A product with a terminal object is canonically the other factor. -/
def tensorTerminalIso : P ⊗ (⊤_ C) ≅ P where
  hom := fst P (⊤_ C)
  inv := lift (𝟙 P) (terminal.from P)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · exact terminal.hom_ext _ _
  inv_hom_id := by simp

/-- The generic arrow's interpretation recovers the actual parameter carrier. -/
def genericIso : (interpretation P).obj (Sierpinski.generic C) ≅ P := by
  have : IsIso (snd P (⊥_ C)) := inferInstance
  exact (asIso (pushout.inr (snd P (⊥_ C))
    (P ◁ (Sierpinski.generic C).hom))).symm ≪≫ tensorTerminalIso P

end SquareKit.Internal.ArrowPushout
