import SquareKit.SmoothQuotientDeformationBaseChange
import Examples.GlobalSectionDescent

/-! Parameter change of matching deformation data uses the selected quotient
comparison, including on nontrivial torsor presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Examples.DeformationDescentBaseChange
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations

variable {H : Type} [Group H] {M X Y Z : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- Matching local deformations glue after an arbitrary further restriction.
No global deformation is among the inputs. -/
example (d : CocycleDatum (a := a) A) (f : Y ⟶ X) :
    transport (d.quotient.baseChangeComparison f) (restrict f d.descend) =
      (d.baseChange f).descend := d.baseChange_descend f

/-- The comparison is coherent under two successive restrictions, even for
an arbitrary deformation on the descended torsor. -/
example (d : Descent.Datum (a := a) A) (f : Y ⟶ X) (g : Z ⟶ Y)
    (s : CocycleDatum.Fiber d) :
    transport ((d.baseChange f).baseChangeComparison g)
      (restrict g (transport (d.baseChangeComparison f)
        (restrict f ((CocycleDatum.fiberEquivalence d).symm s)))) =
    transport (d.baseChangeComparison (g ≫ f))
      (restrict (g ≫ f) ((CocycleDatum.fiberEquivalence d).symm s)) :=
  CocycleDatum.comparison_transport_comp d f g _

/-- The nontrivial ineffective torsor is a usable instance of the fiber square.
The selected comparison is used rather than identifying its endpoints. -/
example (K : Type) [Group K] (c : K) (B : SplitSheaf.Ty SmoothClutching.base)
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p B).hom]
    {Y : Sheaf topology Type} (f : Y ⟶ SmoothClutching.base) :
    let d := Descent.canonicalDatum B (ActionQuotientEvidence.nontrivialObject K c)
    CocycleDatum.fiberEquivalence (d.baseChange f)
      (transport (d.baseChangeComparison f)
        (restrict f (SmoothQuotientDeformations.constant d.object))) =
    (CocycleDatum.fiberBaseChange f).app d
      (CocycleDatum.fiberEquivalence d (SmoothQuotientDeformations.constant d.object)) :=
  CocycleDatum.fiberBaseChange_comparison _ f _

end Examples.DeformationDescentBaseChange
