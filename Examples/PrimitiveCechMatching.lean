import SquareKit.SmoothQuotientCechMatchingFibers
import Examples.CechDeformationDescent

/-! Actual primitive torsors and arrows enter the generic matching interface
without replacing the locally supplied data by chosen global objects. -/
noncomputable section
namespace Examples.PrimitiveCechMatching
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite
open Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

example (d : SheafActionQuotient.Cech.Datum (a := a) A) :
    ((SheafActionQuotient.Cech.matchingEquivalence a A).functor.obj d).overlap =
      d.overlap := rfl

example {d e : SheafActionQuotient.Cech.Datum (a := a) A} (f g : d ⟶ e)
    (h : f ≠ g) :
    (SheafActionQuotient.Cech.toMatching a A).map f ≠
      (SheafActionQuotient.Cech.toMatching a A).map g := by
  intro he
  apply h
  apply SheafActionQuotient.Cech.Map.ext
  exact congrArg CechMatching.Datum.Hom.localArrow he

/-- Effectivity consumes arbitrary matching objects, with no chosen descent
object among its inputs. -/
example [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom] :
    CechMatching.Datum (SheafActionQuotient.Cech.matchingDiagram a A) ≌ Object a X :=
  SheafActionQuotient.Cech.matchingDescentEquivalence a A

variable (K : Type) [Group K] (c : K) (B : SplitSheaf.Ty SmoothClutching.base)

/-- The doubled-origin torsor supplies a generic independent matching value.
For c ≠ 1, the accepted torsor consumer rules out a global chart. -/
example : (SmoothQuotientDeformations.Cech.matchingFamily
    (ActionQuotientEvidence.ineffective K) B).obj
      ((SheafActionQuotient.Cech.toMatching _ B).obj
        (SheafActionQuotient.Cech.ofDescent
          (Descent.canonicalDatum B (ActionQuotientEvidence.nontrivialObject K c)))) :=
  CechDeformationDescent.nontrivialMatching K c B

end Examples.PrimitiveCechMatching
