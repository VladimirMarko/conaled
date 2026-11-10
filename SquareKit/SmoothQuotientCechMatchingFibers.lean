import Mathlib.CategoryTheory.Whiskering
import SquareKit.SheafActionQuotientCechMatching
import SquareKit.SmoothQuotientCechFibers
import SquareKit.SmoothQuotientDeformationRestriction
import SquareKit.Internal.PathTransport.CechMatchingSetFamily

/-! Generic matching values specialize to the accepted primitive deformation
matching equation, including the action of every local quotient arrow. -/
noncomputable section
namespace SquareKit.SmoothQuotientDeformations.Cech
open CategoryTheory SheafActionQuotient SmoothOpenSite SplitSheaf.Cech
open Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

/-- This uses only local deformations and the actual overlap equation. -/
def matchingFamily : CechMatching.Datum (SheafActionQuotient.Cech.matchingDiagram a A) ⥤ Type :=
  CechMatching.SetFamily.family (D := SheafActionQuotient.Cech.matchingDiagram a A)
    (SmoothQuotientDeformations.family a (SplitSheaf.Ext A))
    (SmoothQuotientDeformations.family a (double A))
    (restrictionFamily (first A)) (restrictionFamily (second A))

/-- The primitive family is unchanged on local values and local-arrow actions. -/
theorem matchingFamily_eq : matchingFamily a A =
    SheafActionQuotient.Cech.fromMatching a A ⋙ family := rfl

/-- The primitive matching family agrees naturally with the established
cocycle deformation family on every actual matching arrow. -/
def matchingComparison
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom] :
    matchingFamily a A ≅
      SheafActionQuotient.Cech.fromMatching a A ⋙
        SheafActionQuotient.Cech.toDescent ⋙ CocycleDatum.fiberFamily :=
  Functor.isoWhiskerLeft (SheafActionQuotient.Cech.fromMatching a A) comparison

end SquareKit.SmoothQuotientDeformations.Cech
