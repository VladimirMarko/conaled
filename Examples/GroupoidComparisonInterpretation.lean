import Examples.GroupoidComparisonJ
import SquareKit.Internal.PathTransport.ComparisonInterpretation
import SquareKit.Internal.PathTransport.UniversalTransfer

/-! Both projections preserve the unchanged original transport-composition
source proof in the noninvertible comparison fixture. -/
noncomputable section
namespace Examples.GroupoidComparisonInterpretation
open CategoryTheory SquareKit.Internal.PathTransport
open GroupoidModel Comparison GroupoidComparison
open Typed

example : HEq ((leftSignatureMap signature).mapTm
    (interpretTm (Comparison.fullModel signature) Authoring.UniversalTransfer.proof))
    (interpretTm (Instance.fullModel signature.base.left signature.leftFiber)
      Authoring.UniversalTransfer.proof) :=
  interpret_left signature Authoring.UniversalTransfer.proof

example : HEq ((rightSignatureMap signature).mapTm
    (interpretTm (Comparison.fullModel signature) Authoring.UniversalTransfer.proof))
    (interpretTm (Instance.fullModel signature.base.right signature.rightFiber)
      Authoring.UniversalTransfer.proof) :=
  interpret_right signature Authoring.UniversalTransfer.proof

/-- The outer lift retains the chosen C4 arrow rather than its action class. -/
example (g : FamilyMapElimination.p ⟶ FamilyMapElimination.p) :
    ((universeSignature signature.base.map signature.leftFiber signature.rightFiber
      signature.fiberMap).base.map.map (AsSmall.up.map (FamilyMapElimination.selected false g))).down =
      signature.base.map.map (FamilyMapElimination.selected false g) :=
  universeSignature_arrow _ _ _ _ _

end Examples.GroupoidComparisonInterpretation
