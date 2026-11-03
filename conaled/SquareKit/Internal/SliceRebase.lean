import SquareKit.Internal.SliceUniversal

/-! Replacing the specified base inverse image by an isomorphic one retains
the geometric lift and transports only its comparison. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} C]
variable {h h' : GeometricMorphism F B} {π : GeometricMorphism C B}

/-- Rebase along a specified inverse-image isomorphism. -/
def Lift.rebase (e : h.inverseImage ≅ h'.inverseImage) (k : Lift h π) : Lift h' π :=
  ⟨k.morphism, k.comparison ≪≫ e⟩

def Lift.rebaseFunctor (e : h.inverseImage ≅ h'.inverseImage) : Lift h π ⥤ Lift h' π where
  obj := Lift.rebase e
  map α := {
    transformation := α.transformation
    over := by
      change whiskerLeft π.inverseImage α.transformation ≫ (_ ≫ _) = _ ≫ _
      rw [← Category.assoc, α.over] }
  map_id _ := rfl
  map_comp _ _ := rfl

open CategoryTheory.MonoidalCategory
variable [HasTerminal F] [CartesianMonoidalCategory B] [HasPullbacks B]
variable {a : B} [Closed a]

/-- Rebase changes the extracted section by the same comparison map. -/
theorem Lift.rebase_section (e : h.inverseImage ≅ h'.inverseImage) (k : Lift h (slice a)) :
    (k.rebase e).section = k.section ≫ e.hom.app a := by
  simp [Lift.section, Lift.rebase, Lift.terminalIso, Category.assoc]
end SquareKit.Internal.GeometricMorphism
