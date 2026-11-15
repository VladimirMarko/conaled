import SquareKit.Internal.DependentJudgments.PrimitiveSigma.ConstantContextual
import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Stability

/-! The separating interpretation includes substitution-stable primitive
elimination and contextual identity elimination for every finite tail. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma.ConstantFamilies
open PathTransport.Typed StructuralModel
universe u
variable (Base : Type u)

/-- Formation, constructor and chosen eliminator commute with every base map. -/
def stable : Stable (structuralModel Base) where
  toCapability := capability Base
  sigma_sub _ _ _ := rfl
  pack_sub _ _ _ := rfl
  split_sub _ _ _ _ _ := rfl

/-- Even with the full stable primitive contract and contextual J, repacking
need not equal the identity substitution in the host theory. -/
theorem stable_repack_ne_identity :
    (stable Base).toCapability.repack (Γ := PUnit) PUnit PUnit ≠
      (model Base).idSub ((model Base).extend PUnit
        ((stable Base).sigma (Γ := PUnit) PUnit PUnit)) :=
  repack_ne_identity Base

end SquareKit.Internal.DependentJudgments.PrimitiveSigma.ConstantFamilies
