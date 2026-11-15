import SquareKit.SmoothQuotientDeformationDescentMaps
import SquareKit.GrothendieckEquivalence
import SquareKit.Internal.PathTransport.SplitFamily

/-! Descent of the quotient context extended by its deformation family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport.GroupoidModel
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- The generic extension comparison specializes to a local quotient cocycle
and an independently supplied compatible deformation. Its target contains all
quotient torsors with their deformations, not just globally trivial charts. -/
def CocycleDatum.extensionEquivalence :
    Extend (setFamily (fiberFamily (a := a) (A := A))) ≌
      Extend (setFamily (family a X)) := by
  let β := Functor.whiskerRight (fiberComparison (a := a) (A := A)).inv
    (discrete ⋙ Grpd.forgetToCat)
  letI (d : Descent.Datum (a := a) A) : (β.app d).toFunctor.IsEquivalence :=
    (Discrete.equivalence (fiberEquivalence d).symm).isEquivalence_functor
  exact GrothendieckEquivalence.extendEquivalence (Descent.quotientDescentEquivalence a A)
    (setFamily (family a X) ⋙ Grpd.forgetToCat) β

/-- The extension comparison's base is exactly the constructed descended
quotient object; an extra quotient or an isomorphism class is not substituted. -/
theorem CocycleDatum.extensionEquivalence_base
    (s : Extend (setFamily (fiberFamily (a := a) (A := A)))) :
    (extensionEquivalence.functor.obj s).base = s.base.object := rfl

end SquareKit.SmoothQuotientDeformations
