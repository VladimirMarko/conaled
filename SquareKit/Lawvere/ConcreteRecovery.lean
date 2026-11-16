import SquareKit.Lawvere.Concrete
import SquareKit.Lawvere.Skeleton

/-! Recovery of the existing concrete representations through the common equivalences. -/
noncomputable section
namespace SquareKit.Lawvere
open CategoryTheory

namespace DeMorgan
/-- The cube adapter preserves and recovers all substitutions. -/
def cubeFullyFaithful : cubeFunctor.FullyFaithful where
  preimage := fromCube
  map_preimage := to_from
  preimage_map {X Y} f := from_to (a := ⟨X.size⟩) (b := ⟨Y.size⟩) f

instance : cubeFunctor.IsEquivalence where
  faithful := cubeFullyFaithful.faithful
  full := cubeFullyFaithful.full
  essSurj := ⟨fun X => ⟨⟨X.dimension⟩, ⟨Iso.refl _⟩⟩⟩

/-- The existing cube category and shared De Morgan context category are equivalent. -/
def cubeEquivalence : operations.Context ≌ Cubical.Cube := cubeFunctor.asEquivalence
end DeMorgan

/-- Smooth maps use exactly the common algebra-homomorphism interpretation. -/
def smoothAlgebraHom {A B : Type u} [CommRing A] [Algebra ℝ A] [SmoothAlgebra.Structure A]
    [CommRing B] [Algebra ℝ B] [SmoothAlgebra.Structure B] (h : SmoothAlgebra.Hom A B) :
    smoothAlgebra A ⟶ smoothAlgebra B := ⟨h, h.map_act⟩

theorem smoothAlgebraHom_toNatTrans {A B : Type u} [CommRing A] [Algebra ℝ A]
    [SmoothAlgebra.Structure A] [CommRing B] [Algebra ℝ B] [SmoothAlgebra.Structure B]
    (h : SmoothAlgebra.Hom A B) : (smoothAlgebraHom h).toNatTrans = smoothHom h := rfl
end SquareKit.Lawvere
