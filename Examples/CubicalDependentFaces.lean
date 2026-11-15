import SquareKit.Internal.Cubical.IntervalSquare
import SquareKit.Internal.Cubical.DependentFaces
import Examples.CubicalPresheaf

/-! A face over a restricted context extends to that original support,
including cubes on which the original face is not globally full. -/
namespace Examples.CubicalDependentFaces
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf CubicalPresheaf

theorem full_restricted_face {Γ : Context} (φ : Cofibration Γ) :
    φ.dependent (Cofibration.top (restrictContext φ)) = φ := by
  apply Cofibration.ext_full
  intro x
  rw [Cofibration.dependent_full]
  exact ⟨fun ⟨h,_⟩ => h,fun h => ⟨h,rfl⟩⟩

theorem endpoint_support_retained :
    (intervalFace naturals false).dependent
      (Cofibration.top (restrictContext (intervalFace naturals false))) = intervalFace naturals false :=
  full_restricted_face _

end Examples.CubicalDependentFaces
