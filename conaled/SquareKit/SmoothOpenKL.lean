import SquareKit.SmoothOpenScalar
import SquareKit.SmoothGeometricRepresentable
import SquareKit.SmoothGeometricDerivative
import SquareKit.SmoothGeometricLocality

/-! Experimental arbitrary-cover instance of the shared presentation-based KL
construction. The only scalar hypothesis is the sheafness proved for this site;
subcanonicity supplies the representable dual-product comparison. -/
noncomputable section
namespace SquareKit.SmoothOpenSite
open CategoryTheory SmoothPresentationSite SheafRelation SheafFunction

instance scalarSheafFact : Fact (Presieve.IsSheaf topology scalarData) := ⟨scalar_isSheaf⟩

abbrev infinitesimal := PresentationGeometry.infinitesimal topology
abbrev inclusion := PresentationGeometry.inclusion (J := topology)
abbrev add := PresentationGeometry.add (J := topology)
abbrev mul := PresentationGeometry.mul (J := topology)
abbrev affineBody := PresentationGeometry.affineBody (J := topology)
abbrev affine := PresentationGeometry.affine (J := topology)
abbrev functions := exponential infinitesimal scalar
abbrev kl : product scalar scalar ≅ functions := SmoothGeometricKL.kl
abbrev dualRepresentable := SmoothGeometricKL.dualRepresentable (J := topology)

/-- The stronger-model derivative still extracts through its actual exponential. -/
abbrev derivative (f : scalar ⟶ scalar) : scalar ⟶ scalar := SmoothGeometricDerivative.derivative f
abbrev interpret := SmoothGeometricDerivative.interpret (J := topology)

end SquareKit.SmoothOpenSite
