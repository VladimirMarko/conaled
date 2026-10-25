import SquareKit.Internal.ArrowGeometry
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Subobject.MonoOver

/-! The generic subterminal of the relative Sierpiński arrow category, and
its interpretation by arbitrary geometric morphisms and transformations. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.Sierpinski
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
variable (B : Type u₁) [Category.{v₁} B] [HasInitial B] [HasTerminal B]

/-- The generic proposition has carrier `0 → 1`. -/
def generic : Arrow B := Arrow.mk (initial.to (⊤_ B))

instance [HasStrictInitialObjects B] : Mono (terminal.from (generic B)) where
  right_cancellation f g _ := by
    apply Arrow.hom_ext
    · exact initial.strict_hom_ext _ _
    · exact terminal.hom_ext _ _

/-- The generic proposition as an actual mono into the terminal arrow. -/
def genericModel [HasStrictInitialObjects B] : MonoOver (⊤_ (Arrow B)) :=
  MonoOver.mk (terminal.from (generic B))

variable {B}
variable {F : Type u₂} [Category.{v₂} F] [HasFiniteLimits F]
variable [HasFiniteLimits B] [HasStrictInitialObjects B]

/-- Actual inverse image of the generic carrier, with normalized terminal codomain. -/
def interpret (k : GeometricMorphism F (Arrow B)) : MonoOver (⊤_ F) := by
  let m := k.inverseImage.map (terminal.from (generic B)) ≫ terminalComparison k.inverseImage
  have hm : Mono m := inferInstance
  exact MonoOver.mk m

/-- Evaluation retains every inverse-image transformation, in the same direction. -/
def interpretation : GeometricMorphism F (Arrow B) ⥤ MonoOver (⊤_ F) where
  obj k := interpret k
  map α := MonoOver.homMk (α.app (generic B)) (terminal.hom_ext _ _)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Fixed-base lifts use the same generic-model evaluation. -/
def liftInterpretation (h : GeometricMorphism F B) :
    GeometricMorphism.Lift h (ArrowGeometry.projection B) ⥤ MonoOver (⊤_ F) :=
  GeometricMorphism.Lift.forget _ _ ⋙ interpretation

omit [HasStrictInitialObjects B] in
/-- A geometric inverse image preserves the initial and terminal endpoints of the generic arrow. -/
def genericImageIso [HasInitial F] (h : GeometricMorphism F B) :
    h.inverseImage.mapArrow.obj (generic B) ≅ generic F :=
  Arrow.isoMk (PreservesInitial.iso h.inverseImage) (PreservesTerminal.iso h.inverseImage)
    (by apply terminal.hom_ext)

end SquareKit.Internal.Sierpinski

