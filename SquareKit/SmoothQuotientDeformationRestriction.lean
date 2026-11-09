import SquareKit.SmoothQuotientDeformations

/-! Restriction as a map of the external base/fiber signature. -/
noncomputable section
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M}

/-- The fiber restriction is natural in actual quotient arrows. This is the
base/fiber input to generated-context restriction, not that closure theorem. -/
def restrictionFamily (f : Y ⟶ X) :
    family a X ⟶ SheafActionQuotient.restriction f ⋙ family a Y where
  app P := ↾(restrict f)
  naturality {P Q} c := by
    apply ConcreteCategory.hom_ext
    intro h
    exact transport_restrict f c h

end SquareKit.SmoothQuotientDeformations
