import SquareKit.SmoothPresentationGeometry

/-! Experimental finite-principal instance of shared presentation geometry.
The public objects retain their actual scalar and square-zero sections. -/
noncomputable section
namespace SquareKit.SmoothPresentationSite
open CategoryTheory Opposite SheafRelation SheafFunction

instance scalarSheafFact : Fact (Presieve.IsSheaf topology scalarData) := ⟨scalar_isSheaf⟩

abbrev ringMap := @PresentationGeometry.ringMap
abbrev infinitesimalData := PresentationGeometry.infinitesimalData
abbrev infinitesimal_isSheaf := PresentationGeometry.infinitesimal_isSheaf topology
abbrev infinitesimal := PresentationGeometry.infinitesimal topology
abbrev inclusion := PresentationGeometry.inclusion (J := topology)
abbrev add := PresentationGeometry.add (J := topology)
abbrev mul := PresentationGeometry.mul (J := topology)
abbrev affineBody := PresentationGeometry.affineBody (J := topology)
abbrev affine := PresentationGeometry.affine (J := topology)
abbrev affine_evaluation := PresentationGeometry.affine_evaluation (J := topology)
abbrev inclusion_injective := PresentationGeometry.inclusion_injective (J := topology)

theorem affine_parameters {X : Sheaf topology Type} (p : X ⟶ product scalar scalar) :
    curry (parameterMap infinitesimal p ≫ affineBody) = p ≫ affine :=
  PresentationGeometry.affine_parameters p

end SquareKit.SmoothPresentationSite
