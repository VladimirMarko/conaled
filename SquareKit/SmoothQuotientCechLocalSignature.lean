import SquareKit.SmoothQuotientCechMatchingFibers
import SquareKit.SmoothQuotientSource
import SquareKit.Internal.PathTransport.ComparisonUniverses

/-! Local evaluation of independently supplied quotient matching data, together
with its selected overlap comparison and primitive deformation square. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

/-- Forget the matching equation while retaining the supplied local deformation. -/
def localFiber : SmoothQuotientDeformations.Cech.family (a := a) (A := A) ⟶
    SheafActionQuotient.Cech.localFunctor ⋙ family a (SplitSheaf.Ext A) where
  app _ := ↾Subtype.val
  naturality {_ _} _ := rfl

/-- The local signature uses arbitrary primitive matching objects and values. -/
def signature := GroupoidModel.Comparison.alignedUniverseSignature
  (SheafActionQuotient.Cech.localFunctor (a := a) (A := A))
  (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
  (family a (SplitSheaf.Ext A)) (localFiber a A)

abbrev model := GroupoidModel.Instance.universeModel
  (SheafActionQuotient.Cech.Datum (a := a) A)
  (SmoothQuotientDeformations.Cech.family (a := a) (A := A))

/-- The actual overlap is a natural isomorphism on the complete local-arrow
category; its naturality is exactly the independently supplied overlap square. -/
def overlap : SheafActionQuotient.Cech.localFunctor (a := a) (A := A) ⋙
      restriction (SplitSheaf.Cech.first A) ≅
    SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.second A) :=
  NatIso.ofComponents (fun d => d.overlap) (fun {_ _} f => f.commutes)

def firstFiber : SmoothQuotientDeformations.Cech.family (a := a) (A := A) ⟶
    (SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.first A)) ⋙
      family a (SplitSheaf.Cech.double A) :=
  localFiber a A ≫ whiskerLeft SheafActionQuotient.Cech.localFunctor
    (restrictionFamily (SplitSheaf.Cech.first A))

def secondFiber : SmoothQuotientDeformations.Cech.family (a := a) (A := A) ⟶
    (SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.second A)) ⋙
      family a (SplitSheaf.Cech.double A) :=
  localFiber a A ≫ whiskerLeft SheafActionQuotient.Cech.localFunctor
    (restrictionFamily (SplitSheaf.Cech.second A))

/-- The fiber square is precisely each supplied deformation's overlap equation. -/
theorem overlap_square : firstFiber a A ≫
    whiskerRight (overlap a A).hom (family a (SplitSheaf.Cech.double A)) = secondFiber a A := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro b
  exact b.property

/-- Restricting the supplied overlap to the diagonal gives its identity. -/
theorem overlap_diagonal :
    isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.diagonal A)) =
      Iso.refl (SheafActionQuotient.Cech.localFunctor (a := a) (A := A)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext d
  exact d.diagonal

/-- The two supplied overlap arrows compose to the direct overlap on triples. -/
theorem overlap_cocycle :
    isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.firstSecond A)) ≪≫
      isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.secondThird A)) =
    isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.firstThird A)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext d
  exact d.cocycle

end SquareKit.SmoothQuotientCechLocal
