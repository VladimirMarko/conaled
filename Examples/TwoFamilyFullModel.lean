import SquareKit.Internal.PathTransport.TwoFamilyFullModel
import Examples.TwoFamilyStructuralModel

/-! Contextual J and the selected higher identity belong to the same model. -/
noncomputable section
namespace Examples.TwoFamilyFullModel
open SquareKit.Internal.PathTransport
open HigherInterpretation
open Examples.TwoFamilyModelData Examples.TwoFamilyStructuralModel
open Examples.TwoFamilyEndpointSections
open CategoryTheory
abbrev completeModel := fullModel integerContext integerContext

def higherPoint : ((completeModel.identity display chosen chosen).data.obj totalPoint) :=
  modelIdentityPoint

def higherPath (n : ℤ) : higherPoint ⟶ higherPoint := modelHigherPath n

theorem higherPath_one_ne_zero : higherPath 1 ≠ higherPath 0 := by
  intro h
  have hi : Multiplicative.ofAdd (1:ℤ) = Multiplicative.ofAdd 0 := congrArg (fun p => p.as) h
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)

example {n} (T : Typed.StructuralModel.Telescope completeModel.toStructuralModel
    (completeModel.toStructuralModel.pathContext display chosen) n)
    (E : completeModel.Family (T.total completeModel.toStructuralModel))
    (d : completeModel.Section _ (completeModel.subTy E
      (T.liftSub completeModel.toStructuralModel (completeModel.toStructuralModel.rootSub display chosen)))) :
    HEq (completeModel.subTm (completeModel.j display chosen T E d)
      (T.liftSub completeModel.toStructuralModel (completeModel.toStructuralModel.rootSub display chosen))) d :=
  completeModel.j_beta display chosen T E d

end Examples.TwoFamilyFullModel
