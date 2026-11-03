import SquareKit.Internal.SliceUniversal

/-! Reindexing global sections along geometric morphisms. Terminal comparisons
make the identity, composition and transformation variance explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} C]
variable [HasTerminal F] [HasTerminal B] [HasTerminal C]

/-- Pull back a global section using the canonical terminal comparison. -/
def pullSection (h : GeometricMorphism F B) {X : B} (s : ⊤_ B ⟶ X) :
    ⊤_ F ⟶ h.inverseImage.obj X :=
  (PreservesTerminal.iso h.inverseImage).inv ≫ h.inverseImage.map s

/-- The normalized terminal map is the unique arrow into the preserved terminal. -/
theorem terminal_inv_unique (h : GeometricMorphism F B)
    (t : ⊤_ F ⟶ h.inverseImage.obj (⊤_ B)) :
    t = (PreservesTerminal.iso h.inverseImage).inv :=
  (terminalIsTerminal.isTerminalObj h.inverseImage).hom_ext _ _

@[simp] theorem pullSection_identity {X : B} (s : ⊤_ B ⟶ X) :
    (identity B).pullSection s = s := by
  have ht : (PreservesTerminal.iso (identity B).inverseImage).inv = 𝟙 (⊤_ B) :=
    terminal.hom_ext _ _
  unfold pullSection
  rw [ht]
  exact Category.id_comp s

/-- Reindexing reverses source morphisms, with the same order as inverse-image composition. -/
theorem pullSection_comp (f : GeometricMorphism F B) (g : GeometricMorphism B C)
    {X : C} (s : ⊤_ C ⟶ X) :
    (f.comp g).pullSection s = f.pullSection (g.pullSection s) := by
  have ht : (PreservesTerminal.iso (f.comp g).inverseImage).inv =
      (PreservesTerminal.iso f.inverseImage).inv ≫
        f.inverseImage.map (PreservesTerminal.iso g.inverseImage).inv :=
    (terminalIsTerminal.isTerminalObj (f.comp g).inverseImage).hom_ext _ _
  simp only [pullSection, ht, f.inverseImage.map_comp, Category.assoc]
  rfl

/-- Inverse-image transformations act in their own direction on global sections. -/
theorem pullSection_transformation {h k : GeometricMorphism F B} (α : h ⟶ k)
    {X : B} (s : ⊤_ B ⟶ X) : h.pullSection s ≫ α.app X = k.pullSection s := by
  have ht : (PreservesTerminal.iso h.inverseImage).inv ≫ α.app (⊤_ B) =
      (PreservesTerminal.iso k.inverseImage).inv := terminal_inv_unique k _
  dsimp only [pullSection]
  rw [Category.assoc, α.naturality, ← Category.assoc, ht]
end SquareKit.Internal.GeometricMorphism
