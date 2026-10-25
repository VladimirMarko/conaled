import SquareKit.Internal.SliceGenericSection

/-! Fullness and faithfulness of extraction of the generic section. Geometric
transformations are recovered from equality of sections, using the proved
pullback reconstruction of their inverse images. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasPullbacks F] [CartesianMonoidalCategory B] [HasPullbacks B]
variable {h : GeometricMorphism F B} {a : B} [Closed a]

/-- The section construction on inverse images before choosing a right adjoint. -/
def sectionInverse (h : GeometricMorphism F B) (a : B) (s : ⊤_ F ⟶ h.inverseImage.obj a) :
    Over a ⥤ F := Over.post h.inverseImage ⋙ Over.pullback s ⋙ Over.forget (⊤_ F)

private theorem sectionInverse_eq_fst {s t : ⊤_ F ⟶ h.inverseImage.obj a} (e : s = t) (Y : Over a) :
    (eqToHom (congrArg (sectionInverse h a) e)).app Y ≫
      pullback.fst (h.inverseImage.map Y.hom) t = pullback.fst (h.inverseImage.map Y.hom) s := by
  cases e
  exact Category.id_comp _

/-- Equal generic sections yield an isomorphism of actual inverse-image functors. -/
def Lift.sectionComparison {k l : Lift h (slice a)} (e : k.section = l.section) :
    k.morphism.inverseImage ≅ l.morphism.inverseImage :=
  k.reconstruction ≪≫ eqToIso (congrArg (sectionInverse h a) e) ≪≫ l.reconstruction.symm

/-- The reconstructed transformation preserves the interpreted underlying objects. -/
theorem Lift.sectionComparison_value {k l : Lift h (slice a)}
    (e : k.section = l.section) (Y : Over a) :
    (Lift.sectionComparison e).hom.app Y ≫ l.value Y = k.value Y := by
  change ((k.section_isPullback Y).isoPullback.hom ≫
    (eqToHom (congrArg (sectionInverse h a) e)).app Y ≫
    (l.section_isPullback Y).isoPullback.inv) ≫ l.value Y = k.value Y
  simp only [Category.assoc, IsPullback.isoPullback_inv_fst]
  rw [sectionInverse_eq_fst (h := h) e Y, IsPullback.isoPullback_hom_fst]

/-- A natural transformation preserving values is compatible with the base comparison. -/
def Lift.homOfValues {k l : Lift h (slice a)}
    (α : k.morphism.inverseImage ⟶ l.morphism.inverseImage)
    (hv : ∀ Y, α.app Y ≫ l.value Y = k.value Y) : k ⟶ l where
  transformation := α
  over := by
    apply NatTrans.ext
    funext X
    have e := congrArg (fun f => f ≫ h.inverseImage.map prod.snd) (hv ((Over.star a).obj X))
    change α.app ((Over.star a).obj X) ≫ l.comparison.hom.app X = k.comparison.hom.app X
    simpa only [Category.assoc, Lift.value_star_snd] using e

/-- Fullness: equality of sections produces a compatible geometric transformation. -/
def Lift.homOfSection {k l : Lift h (slice a)} (e : k.section = l.section) : k ⟶ l :=
  Lift.homOfValues (Lift.sectionComparison e).hom (Lift.sectionComparison_value e)

/-- Extraction preserves all morphisms, with the stated inverse-image variance. -/
def sectionFunctor (h : GeometricMorphism F B) (a : B) [Closed a] :
    Lift h (slice a) ⥤ Discrete (⊤_ F ⟶ h.inverseImage.obj a) where
  obj k := Discrete.mk k.section
  map α := Discrete.eqToHom (Lift.section_natural α)

instance : (sectionFunctor h a).Faithful where
  map_injective := fun _ => Subsingleton.elim _ _

instance : (sectionFunctor h a).Full where
  map_surjective f := ⟨Lift.homOfSection (Discrete.eq_of_hom f), Subsingleton.elim _ _⟩
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasBinaryProducts F] [HasTerminal F] [HasPullbacks F]
variable [CartesianMonoidalCategory B] [HasPullbacks B]
variable (h : GeometricMorphism F B) (a : B) [Closed a]
variable (s : ⊤_ F ⟶ h.inverseImage.obj a)
local instance sliceUniversalLocal1 : CartesianMonoidalCategory (Over (h.inverseImage.obj a)) :=
  Over.cartesianMonoidalCategory _
variable [Closed (Over.mk s)]

/-- Extracting the generic section of the constructed lift returns the original section. -/
theorem fromSectionLift_section : (fromSectionLift h a s).section = s := by
  dsimp only [Lift.section]
  rw [fromSectionLift_comparison_hom]
  change (fromSectionLift h a s).terminalIso.inv ≫
    (pullback.lift (pullback.fst _ _ ≫ h.inverseImage.map (prod.lift (𝟙 a) (𝟙 a)))
      (pullback.snd _ _) _) ≫ pullback.fst _ _ ≫ h.inverseImage.map prod.snd = s
  rw [pullback.lift_fst_assoc, Category.assoc, ← h.inverseImage.map_comp, prod.lift_snd]
  change (fromSectionLift h a s).terminalIso.inv ≫
    pullback.fst (h.inverseImage.map (𝟙 a)) s ≫ h.inverseImage.map (𝟙 a) = s
  rw [pullback.condition, ← Category.assoc]
  have ht : (fromSectionLift h a s).terminalIso.inv ≫
      pullback.snd (h.inverseImage.map (𝟙 a)) s = 𝟙 (⊤_ F) := terminal.hom_ext _ _
  rw [ht, Category.id_comp]
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasBinaryProducts F] [HasTerminal F] [HasPullbacks F]
variable [CartesianMonoidalCategory B] [HasPullbacks B]
variable (h : GeometricMorphism F B) (a : B) [Closed a]
local instance sliceUniversalLocal2 : CartesianMonoidalCategory (Over (h.inverseImage.obj a)) :=
  Over.cartesianMonoidalCategory _
variable [MonoidalClosed (Over (h.inverseImage.obj a))]

/-- The slice universal property, including every compatible transformation.
Closure of this one source slice constructs the dependent-product right adjoints. -/
def sectionEquivalence : Lift h (slice a) ≌ Discrete (⊤_ F ⟶ h.inverseImage.obj a) where
  functor := sectionFunctor h a
  inverse := Discrete.functor (fun s => fromSectionLift h a s)
  unitIso := NatIso.ofComponents (fun k => {
    hom := Lift.homOfSection (fromSectionLift_section h a k.section).symm
    inv := Lift.homOfSection (fromSectionLift_section h a k.section)
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents
    (fun s => Discrete.eqToIso (fromSectionLift_section h a s.as)) (by intros; apply Subsingleton.elim)
end SquareKit.Internal.GeometricMorphism
