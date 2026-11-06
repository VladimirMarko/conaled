import SquareKit.Internal.Cubical.ContextualModel
import SquareKit.Internal.Cubical.SumFillingSubstitution
import SquareKit.Internal.Cubical.SumElimination
import SquareKit.Internal.DependentJudgments.Sigma.Stability

/-! The selected cubical dependent sum supplies both comprehension inverses. -/
namespace SquareKit.Cubical.Contextual
open Presheaf SquareKit.Internal.PathTransport.Typed
universe u
noncomputable def sumFamily {Γ : Context.{u}} (A : LawfulFamily Γ)
    (B : LawfulFamily (total A.family)) : LawfulFamily Γ :=
  ⟨⟨Presheaf.sigma A.family B.family,sigmaFilling A.filling A.lawful B.filling⟩,
    sigmaFilling_lawful A.filling A.lawful B.filling B.lawful⟩

noncomputable def sumCapability (Base : LawfulFamily terminal.{u})
    (Fiber : LawfulFamily (total Base.family)) :
    SquareKit.Internal.DependentJudgments.Sigma.Capability (structuralModel Base Fiber) where
  sigma A B := sumFamily A B
  pack A B := ⟨sigmaPack A.family B.family⟩
  unpack A B := ⟨sigmaUnpack A.family B.family⟩
  pack_over _ _ := rfl
  unpack_pack _ _ := rfl
  pack_unpack _ _ := rfl

noncomputable def stableSums (Base : LawfulFamily terminal.{u})
    (Fiber : LawfulFamily (total Base.family)) :
    SquareKit.Internal.DependentJudgments.Sigma.Stable (structuralModel Base Fiber) where
  toCapability := sumCapability Base Fiber
  sigma_sub _ _ _ := rfl
  pack_sub _ _ _ := rfl

end SquareKit.Cubical.Contextual
