import SquareKit.SheafActionQuotientCechEquivalence
import SquareKit.SheafActionQuotientDescentCategory
import SquareKit.Internal.PathTransport.CechMatching

/-! The primitive quotient Čech data are precisely the generic independent
matching groupoid. The identification keeps local objects and arrows. -/
noncomputable section
namespace SquareKit.SheafActionQuotient.Cech
open CategoryTheory SplitSheaf.Cech
open Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X : Sheaf J (Type (max u v))}
variable (a : Action G M) (A : SplitSheaf.Ty X)

/-- The actual restriction diagram of quotient objects. -/
def matchingDiagram : CechMatching.Diagram.{max u v, max (u+1) (v+1)} where
  localCategory := Grpd.of (Object a (SplitSheaf.Ext A))
  doubleCategory := Grpd.of (Object a (double A))
  tripleCategory := Grpd.of (Object a (triple A))
  first := restriction (first A)
  second := restriction (second A)
  diagonal := restriction (diagonal A)
  firstSecond := restriction (firstSecond A)
  firstThird := restriction (firstThird A)
  secondThird := restriction (secondThird A)
  diagonalFirst := Iso.refl _
  diagonalSecond := Iso.refl _
  tripleFirst := Iso.refl _
  tripleMiddle := Iso.refl _
  tripleLast := Iso.refl _


/-- No local object or overlap arrow is changed by the identification. -/
def toMatching : Datum (a := a) A ⥤ CechMatching.Datum (matchingDiagram a A) where
  obj d := {
    localObject := d.localObject
    overlap := d.overlap
    diagonal := by
      apply Arrow.ext
      apply SheafTorsor.Arrow.ext
      exact congrArg (fun k => k.torsorArrow.iso.hom) d.diagonal
    cocycle := by
      apply Arrow.ext
      apply SheafTorsor.Arrow.ext
      exact congrArg (fun k => k.torsorArrow.iso.hom) d.cocycle }
  map h := ⟨h.localArrow, h.commutes⟩
  map_id _ := rfl
  map_comp _ _ := rfl


/-- The inverse reads off the same independently supplied matching data. -/
def fromMatching : CechMatching.Datum (matchingDiagram a A) ⥤ Datum (a := a) A where
  obj d := {
    localObject := d.localObject
    overlap := d.overlap
    diagonal := by
      apply Arrow.ext
      apply SheafTorsor.Arrow.ext
      exact congrArg (fun k => k.torsorArrow.iso.hom) d.diagonal
    cocycle := by
      apply Arrow.ext
      apply SheafTorsor.Arrow.ext
      exact congrArg (fun k => k.torsorArrow.iso.hom) d.cocycle }
  map h := ⟨h.localArrow, h.commutes⟩
  map_id _ := rfl
  map_comp _ _ := rfl


/-- Independent primitive data and generic matching agree strictly on objects
and arrows, with only proof fields reconstructed. -/
def matchingEquivalence : Datum (a := a) A ≌ CechMatching.Datum (matchingDiagram a A) where
  functor := toMatching a A
  inverse := fromMatching a A
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Primitive effectivity is inherited from the established quotient descent
construction, rather than assumed in the matching definition. -/
def matchingDescentEquivalence
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    CechMatching.Datum (matchingDiagram a A) ≌ Object a X :=
  (matchingEquivalence a A).symm.trans
    (equivalence.trans (Descent.quotientDescentEquivalence a A))

end SquareKit.SheafActionQuotient.Cech
