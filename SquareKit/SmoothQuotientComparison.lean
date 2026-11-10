import SquareKit.SmoothQuotientSource
import SquareKit.SmoothQuotientDeformationRestriction
import SquareKit.Internal.PathTransport.ComparisonInterpretation

/-! Ordinary-groupoid comparison for parameter restriction. This constructs
signature-aware generated interpretation maps. Parameter composition coherence
and gluing of generated sections remain separate obligations. -/
noncomputable section
namespace SquareKit.SmoothQuotientComparison
open CategoryTheory SheafActionQuotient SmoothOpenSite SmoothQuotientDeformations
open Internal.PathTransport
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M}

/-- Parameter restriction and deformation restriction supply the comparison
signature, without choosing trivializations of the quotient torsors. -/
def signature (f : Y ⟶ X) :=
  GroupoidModel.Comparison.alignedUniverseSignature (SheafActionQuotient.restriction (a := a) f)
    (family a X) (family a Y) (restrictionFamily f)

abbrev model (f : Y ⟶ X) := GroupoidModel.Comparison.fullModel (signature (a := a) f)

/-- Projection is to the existing all-torsor interpretation at the source
parameter, including its universe lift and primitive signature. -/
def source (f : Y ⟶ X) : Typed.SignatureMap (model (a := a) f)
    (SmoothQuotientSource.model a X) :=
  GroupoidModel.Comparison.leftSignatureMap (signature f)

/-- Projection is to the existing all-torsor interpretation at the restricted
parameter. No equivalence of restriction functors is assumed. -/
def target (f : Y ⟶ X) : Typed.SignatureMap (model (a := a) f)
    (SmoothQuotientSource.model a Y) :=
  GroupoidModel.Comparison.rightSignatureMap (signature f)

end SquareKit.SmoothQuotientComparison
