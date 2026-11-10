import SquareKit.SmoothQuotientComparison
import SquareKit.Internal.PathTransport.UniversalTransfer

/-! Parameter restriction has two projections preserving the unchanged source
proof. These are ordinary-groupoid interpretation comparisons, not a claim
that arbitrary sections already form parameter-natural descent data. -/
noncomputable section
namespace Examples.SmoothComparisonInterpretation
open CategoryTheory SquareKit SquareKit.Internal.PathTransport
open SmoothOpenSite SheafActionQuotient
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (f : Y ⟶ X)

example : HEq ((SmoothQuotientComparison.source (a := a) f).mapTm
    (Typed.interpretTm (SmoothQuotientComparison.model (a := a) f)
      Typed.Authoring.UniversalTransfer.proof))
    (Typed.interpretTm (SmoothQuotientSource.model a X)
      Typed.Authoring.UniversalTransfer.proof) :=
  (SmoothQuotientComparison.source f).interpretTm Typed.Authoring.UniversalTransfer.proof

example : HEq ((SmoothQuotientComparison.target (a := a) f).mapTm
    (Typed.interpretTm (SmoothQuotientComparison.model (a := a) f)
      Typed.Authoring.UniversalTransfer.proof))
    (Typed.interpretTm (SmoothQuotientSource.model a Y)
      Typed.Authoring.UniversalTransfer.proof) :=
  (SmoothQuotientComparison.target f).interpretTm Typed.Authoring.UniversalTransfer.proof

/-- Restriction keeps the given quotient arrow, including its torsor map. -/
example {P Q : Object a X} (c : P ⟶ Q) :
    ((SmoothQuotientComparison.signature f).base.map.map (AsSmall.up.map c)).down =
      (SheafActionQuotient.restriction f).map c := rfl

/-- The primitive comparison is the actual all-torsor deformation restriction. -/
example (P : Object a X) (h : SmoothQuotientDeformations.Deformation P) :
    ((SmoothQuotientComparison.signature f).fiberMap.app ⟨P⟩ ⟨h⟩).down =
      SmoothQuotientDeformations.restrict f h := rfl

end Examples.SmoothComparisonInterpretation
