import SquareKit.Internal.SliceUniversal

/-! Transformations between slice lifts with a varying morphism to the base.
The base transformation need not be invertible. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [CartesianMonoidalCategory B] [HasPullbacks B]
variable {h h' : GeometricMorphism F B} {a : B} [Closed a]
variable {k : Lift h (slice a)} {l : Lift h' (slice a)}

/-- The value map forces the component of a transformation over the given base map. -/
def Lift.mapOfSectionsApp (α : h ⟶ h') (e : k.section ≫ α.app a = l.section) (Y : Over a) :
    k.morphism.inverseImage.obj Y ⟶ l.morphism.inverseImage.obj Y :=
  (l.section_isPullback Y).lift (k.value Y ≫ α.app Y.left) (terminal.from _) (by
    rw [Category.assoc, ← α.naturality Y.hom, ← Category.assoc,
      (k.section_isPullback Y).w, Category.assoc, e])

@[reassoc (attr := simp)] theorem Lift.mapOfSectionsApp_value
    (α : h ⟶ h') (e : k.section ≫ α.app a = l.section) (Y : Over a) :
    Lift.mapOfSectionsApp α e Y ≫ l.value Y = k.value Y ≫ α.app Y.left :=
  IsPullback.lift_fst _ _ _ _

/-- Compatible sections reconstruct a natural transformation of actual inverse images. -/
def Lift.mapOfSections (α : h ⟶ h') (e : k.section ≫ α.app a = l.section) :
    k.morphism ⟶ l.morphism where
  app := Lift.mapOfSectionsApp α e
  naturality Y Z f := by
    apply (l.section_isPullback Z).hom_ext
    · rw [Category.assoc, Lift.mapOfSectionsApp_value, ← Category.assoc, Lift.value_natural,
        Category.assoc, α.naturality f.left, ← Category.assoc,
        ← Lift.mapOfSectionsApp_value, Category.assoc, ← Lift.value_natural, ← Category.assoc]
    · exact terminal.hom_ext _ _

/-- Reconstruction retains the comparison with the varying base transformation. -/
theorem Lift.mapOfSections_over (α : h ⟶ h') (e : k.section ≫ α.app a = l.section) :
    Functor.whiskerLeft (slice a).inverseImage (Lift.mapOfSections α e) ≫ l.comparison.hom =
      k.comparison.hom ≫ α := by
  apply NatTrans.ext
  funext X
  have hv := Lift.mapOfSectionsApp_value α e ((Over.star a).obj X)
  have hh := congrArg (fun t => t ≫ h'.inverseImage.map prod.snd) hv
  change Lift.mapOfSectionsApp α e ((Over.star a).obj X) ≫ l.comparison.hom.app X =
    k.comparison.hom.app X ≫ α.app X
  simp only [Category.assoc, Lift.value_star_snd] at hh
  refine hh.trans ?_
  calc
    _ = k.value ((Over.star a).obj X) ≫ h.inverseImage.map (prod.snd : a ⨯ X ⟶ X) ≫ α.app X :=
      congrArg (fun t => k.value ((Over.star a).obj X) ≫ t) (α.naturality (prod.snd : a ⨯ X ⟶ X)).symm
    _ = _ := by rw [← Category.assoc, Lift.value_star_snd]
/-- A transformation over an arbitrary base transformation preserves the extracted section. -/
theorem Lift.section_over (α : h ⟶ h') (β : k.morphism ⟶ l.morphism)
    (over : Functor.whiskerLeft (slice a).inverseImage β ≫ l.comparison.hom = k.comparison.hom ≫ α) :
    k.section ≫ α.app a = l.section := by
  have ht : k.terminalIso.inv ≫ β.app (Over.mk (𝟙 a)) = l.terminalIso.inv :=
    (Over.mkIdTerminal.isTerminalObj l.morphism.inverseImage).hom_ext _ _
  have ho := congrArg (fun t => t.app a) over
  change β.app ((Over.star a).obj a) ≫ l.comparison.hom.app a = k.comparison.hom.app a ≫ α.app a at ho
  dsimp only [Lift.section]
  rw [Category.assoc, Category.assoc, ← ho,
    reassoc_of% (β.naturality (genericSection a)), ← Category.assoc, ht]

/-- Compatibility over the base determines every value map. -/
theorem Lift.value_over (α : h ⟶ h') (β : k.morphism ⟶ l.morphism)
    (over : Functor.whiskerLeft (slice a).inverseImage β ≫ l.comparison.hom = k.comparison.hom ≫ α)
    (Y : Over a) : β.app Y ≫ l.value Y = k.value Y ≫ α.app Y.left := by
  have ho := congrArg (fun t => t.app Y.left) over
  change β.app ((Over.star a).obj Y.left) ≫ l.comparison.hom.app Y.left =
    k.comparison.hom.app Y.left ≫ α.app Y.left at ho
  dsimp only [Lift.value]
  rw [Category.assoc, ← reassoc_of% (β.naturality (genericUnit Y)), ho, ← Category.assoc]

/-- Uniqueness holds over each specified base transformation, without assuming that it is invertible. -/
theorem Lift.transformation_ext (α : h ⟶ h') (β γ : k.morphism ⟶ l.morphism)
    (hβ : Functor.whiskerLeft (slice a).inverseImage β ≫ l.comparison.hom = k.comparison.hom ≫ α)
    (hγ : Functor.whiskerLeft (slice a).inverseImage γ ≫ l.comparison.hom = k.comparison.hom ≫ α) : β = γ := by
  apply NatTrans.ext
  funext Y
  apply (l.section_isPullback Y).hom_ext
  · exact (Lift.value_over α β hβ Y).trans (Lift.value_over α γ hγ Y).symm
  · exact terminal.hom_ext _ _
end SquareKit.Internal.GeometricMorphism
