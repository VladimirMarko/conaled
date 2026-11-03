import SquareKit.Internal.GeometricSections

/-! Precomposition of pseudo-slice morphisms and its action on the extracted
generic section. Comparison isomorphisms are retained throughout. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {F : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
variable {h : GeometricMorphism F B} {π : GeometricMorphism C B}

/-- Precompose a lift, retaining the composed comparison with the base. -/
def Lift.precomp (k : Lift h π) (f : GeometricMorphism D F) : Lift (f.comp h) π where
  morphism := f.comp k.morphism
  comparison := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight k.comparison f.inverseImage

/-- Source substitution acts on all compatible geometric transformations. -/
def Lift.precompFunctor (f : GeometricMorphism D F) : Lift h π ⥤ Lift (f.comp h) π where
  obj k := k.precomp f
  map α := {
    transformation := whiskerRight α.transformation f.inverseImage
    over := by
      apply NatTrans.ext
      funext X
      have ho := congrArg (fun t => f.inverseImage.map (t.app X)) α.over
      change f.inverseImage.map (α.transformation.app (π.inverseImage.obj X)) ≫
        (𝟙 _ ≫ f.inverseImage.map _) = 𝟙 _ ≫ f.inverseImage.map _
      simp only [Category.id_comp, ← f.inverseImage.map_comp]
      exact ho }
  map_id k := by apply Lift.Hom.ext; apply NatTrans.ext; funext X; exact f.inverseImage.map_id _
  map_comp α β := by apply Lift.Hom.ext; apply NatTrans.ext; funext X; exact f.inverseImage.map_comp _ _

section Sections
open CategoryTheory.MonoidalCategory
variable [HasTerminal F] [HasTerminal D] [CartesianMonoidalCategory B] [HasPullbacks B]
variable {a : B} [Closed a]

/-- Extraction commutes with source substitution, via the actual generic diagonal. -/
theorem Lift.precomp_section (k : Lift h (slice a)) (f : GeometricMorphism D F) :
    (k.precomp f).section = f.pullSection k.section := by
  have ht : (k.precomp f).terminalIso.inv =
      (PreservesTerminal.iso f.inverseImage).inv ≫ f.inverseImage.map k.terminalIso.inv :=
    ((Over.mkIdTerminal.isTerminalObj k.morphism.inverseImage).isTerminalObj f.inverseImage).hom_ext _ _
  dsimp only [Lift.section, pullSection]
  rw [ht]
  simp [Lift.precomp, comp, f.inverseImage.map_comp, Category.assoc]
end Sections
end SquareKit.Internal.GeometricMorphism
