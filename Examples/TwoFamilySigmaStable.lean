import SquareKit.Internal.PathTransport.TwoFamilySigmaStable
import Examples.TwoFamilySigmaCapability
noncomputable section
namespace Examples.TwoFamilySigmaStable
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
open Examples.TwoFamilyModelData Examples.TwoFamilyStructuralModel
abbrev stableSums := sigmaStable integerContext integerContext
example {Δ : model.Context} (σ : model.Substitution Δ integerContext) :
    model.compSub (stableSums.unpack integers later) (stableSums.sumMap integers later σ) =
      model.compSub (model.lift later (model.lift integers σ))
        (stableSums.unpack (model.subTy integers σ) (model.subTy later (model.lift integers σ))) :=
  stableSums.unpack_sub integers later σ

example {Δ : model.Context} (σ : model.Substitution Δ integerContext)
    (E : model.Family (model.extend integerContext (stableSums.sigma integers later)))
    (d : model.Section (model.extend integers.total later)
      (model.subTy E (stableSums.pack integers later))) :
    model.subTm (stableSums.toCapability.split integers later E d) (stableSums.sumMap integers later σ) =
      stableSums.toCapability.split (model.subTy integers σ) (model.subTy later (model.lift integers σ))
        (model.subTy E (stableSums.sumMap integers later σ)) (stableSums.branch integers later σ E d) :=
  stableSums.split_sub integers later σ E d
end Examples.TwoFamilySigmaStable
