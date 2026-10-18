import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import SquareKit.Family
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism

/-! Experimental dependent products from closed objects in ordinary slices.
The local tensor is the existing family pullback. Iterated slicing identifies
toOver with the ordinary pullback functor, without changing limit choices. -/
noncomputable section
namespace SquareKit.SliceDependentProduct
open CategoryTheory Limits MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A Γ : C} (f : A ⟶ Γ)
local instance : CartesianMonoidalCategory (Over Γ) := Over.cartesianMonoidalCategory Γ
local instance : BraidedCategory (Over Γ) := BraidedCategory.ofCartesianMonoidalCategory

/-- Flatten the slice of the display after adjoining a parameter. -/
def parameterFunctor : Over Γ ⥤ Over A :=
  toOver (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward

/-- Both sides use the same ordinary pullback object and projections. -/
def pullbackComparison : parameterFunctor f ≅ Over.pullback f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y k
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;>
      simp [parameterFunctor, Over.pullback, toOver, Over.iteratedSliceForward]
    · exact Over.whiskerRight_left_fst k
    · exact Over.whiskerRight_left_snd k)

@[reassoc (attr := simp)] theorem comparison_value (X : Over Γ) :
    ((pullbackComparison f).hom.app X).left ≫ pullback.fst X.hom f = pullback.fst X.hom f :=
  Category.id_comp _

@[reassoc (attr := simp)] theorem comparison_display (X : Over Γ) :
    ((pullbackComparison f).hom.app X).left ≫ Family.reindex X.hom f = Family.reindex X.hom f :=
  Category.id_comp _

variable [Closed (Over.mk f)]
local instance : ChosenPullbacksAlong (curryRightUnitorHom (Over.mk f)) :=
  ChosenPullbacksAlong.ofHasPullbacksAlong _

/-- Internal sections in the slice supply the dependent product. -/
def pi : Over A ⥤ Over Γ := (Over.mk f).iteratedSliceBackward ⋙ Over.sections (Over.mk f)

def adjunction : Over.pullback f ⊣ pi f :=
  ((Over.toOverSectionsAdj (Over.mk f)).comp (Over.mk f).iteratedSliceEquiv.toAdjunction).ofNatIsoLeft
    (pullbackComparison f)

/-- Mathlib exponentiability for the unchanged ordinary chosen pullbacks. -/
@[instance_reducible] def exponentiable :
    letI := ChosenPullbacksAlong.ofHasPullbacksAlong f
    ExponentiableMorphism f := by
  letI := ChosenPullbacksAlong.ofHasPullbacksAlong f
  exact ⟨pi f, adjunction f⟩

end SquareKit.SliceDependentProduct
