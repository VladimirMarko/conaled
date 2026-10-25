import SquareKit.Internal.SierpinskiGeneric

/-! Geometric reindexing of actual subterminal carriers, with coherent terminal
normalization and unrestricted inverse-image transformations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.SubterminalChange
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {G : Type u₂} {H : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} G] [Category.{v₃} H]
variable [HasFiniteLimits F] [HasFiniteLimits G] [HasFiniteLimits H]

/-- Reindex an actual mono and normalize its terminal codomain. -/
def pull (f : GeometricMorphism G F) : MonoOver (⊤_ F) ⥤ MonoOver (⊤_ G) where
  obj P := MonoOver.mk (f.inverseImage.map P.arrow ≫ terminalComparison f.inverseImage)
  map α := MonoOver.homMk (f.inverseImage.map α.hom.left) (terminal.hom_ext _ _)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Identity reindexing is canonically the original model. -/
def identity : pull (GeometricMorphism.identity F) ≅ 𝟭 (MonoOver (⊤_ F)) :=
  NatIso.ofComponents (fun _ => MonoOver.isoMk (Iso.refl _) (terminal.hom_ext _ _))
    (by intros; apply Subsingleton.elim)

/-- Two source substitutions agree with their geometric composite. -/
def comp (f : GeometricMorphism G F) (g : GeometricMorphism H G) :
    pull f ⋙ pull g ≅ pull (g.comp f) :=
  NatIso.ofComponents (fun _ => MonoOver.isoMk (Iso.refl _) (terminal.hom_ext _ _))
    (by intros; apply Subsingleton.elim)

/-- A geometric transformation acts on the actual model carrier in its given direction. -/
def transformation {f g : GeometricMorphism G F} (α : f ⟶ g) : pull f ⟶ pull g where
  app P := MonoOver.homMk (α.app P.obj.left) (terminal.hom_ext _ _)
  naturality := by intros; apply Subsingleton.elim

@[simp] theorem transformation_id (f : GeometricMorphism G F) :
    transformation (𝟙 f) = 𝟙 (pull f) := Subsingleton.elim _ _

@[simp] theorem transformation_comp {f g h : GeometricMorphism G F} (α : f ⟶ g) (β : g ⟶ h) :
    transformation (α ≫ β) = transformation α ≫ transformation β := Subsingleton.elim _ _

/-- The unit comparison is compatible with all model homomorphisms. -/
theorem identity_natural {P Q : MonoOver (⊤_ F)} (α : P ⟶ Q) :
    (pull (GeometricMorphism.identity F)).map α ≫ identity.hom.app Q =
      identity.hom.app P ≫ α := Subsingleton.elim _ _

/-- The composite comparison is compatible with all model homomorphisms. -/
theorem comp_natural (f : GeometricMorphism G F) (g : GeometricMorphism H G)
    {P Q : MonoOver (⊤_ F)} (α : P ⟶ Q) :
    (pull f ⋙ pull g).map α ≫ (comp f g).hom.app Q =
      (comp f g).hom.app P ≫ (pull (g.comp f)).map α := Subsingleton.elim _ _

end SquareKit.Internal.SubterminalChange
