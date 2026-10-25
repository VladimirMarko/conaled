import SquareKit.Internal.SheafFiniteClassifier

/-! The relative finite classifier over E/X, for arbitrary represented sheaf
toposes E and arbitrary represented sheaf sources. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
variable {X U : Sheaf J (Type (max u v))} (u : U ⟶ X) [Mono u]
local instance relativeSheafSliceCartesian : CartesianMonoidalCategory (Over X) := Over.cartesianMonoidalCategory X
local instance relativeSheafSliceClosed : MonoidalClosed (Over X) := SquareKit.SheafSliceFunction.closed X

/-- A context predicate is exactly a subterminal in its context slice. -/
def relativeParameter : Over.mk u ⟶ ⊤_ (Over X) :=
  (Over.homMk u (by exact Category.comp_id _) : Over.mk u ⟶ Over.mk (𝟙 X)) ≫
    (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).hom

instance : Mono (relativeParameter u) := by
  unfold relativeParameter
  have : Mono (Over.homMk u (by exact Category.comp_id _) : Over.mk u ⟶ Over.mk (𝟙 X)) :=
    Over.mono_of_mono_left _
  infer_instance

/-- The classifier works over E/X for every geometric morphism from an arbitrary sheaf source. -/
def relativeSheafClassifier (h : GeometricMorphism (Sheaf K (Type (max u' v'))) (Over X)) :
    Lift h (slice (Over.mk u ⨿ ⊤_ (Over X))) ≌
      PartitionSection.Model (parameterPullback h (relativeParameter u)) :=
  sheafFiniteClassifier h (relativeParameter u)
end SquareKit.Internal.GeometricMorphism
