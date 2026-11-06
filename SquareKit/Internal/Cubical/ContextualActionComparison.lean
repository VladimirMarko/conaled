import SquareKit.Internal.Cubical.ContextualPointwiseActionRoot
import SquareKit.Internal.DependentJudgments.OrdinaryActionComparison

/-! Actual J-derived ordinary action is joined to pointwise action by an identity in its motive. -/
noncomputable section
namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => model Base Fiber
variable {Γ : Presheaf.Context.{u}} (A C : LawfulFamily Γ)
  (t : Term (reindex C.family (projection A.family))) (x : Term A.family)

def ordinaryActionComparison :=
  ordinaryApComparison M A C ⟨t⟩ ⟨x⟩ (pointwiseApSection Base Fiber A C t x)
    (pointwiseApSection_root Base Fiber A C t x)

def pointwiseApValue (y : Term A.family) (p : Term (normalizedIdentity A.family x y)) :
    (M).Section Γ ((M).identity C (ordinaryApply M A C ⟨t⟩ ⟨x⟩) (ordinaryApply M A C ⟨t⟩ ⟨y⟩)) :=
  cast (congrArg ((M).Section Γ) (ordinaryApMotive_endpoint M A C ⟨t⟩ ⟨x⟩ ⟨y⟩ ⟨p⟩))
    ((M).subTm (pointwiseApSection Base Fiber A C t x)
      ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩))

theorem ordinaryActionComparison_endpointFamily (y : Term A.family)
    (p : Term (normalizedIdentity A.family x y)) :
    (M).subTy ((M).identity (ordinaryApMotive M A C ⟨t⟩ ⟨x⟩)
      (ordinaryApSection M A C ⟨t⟩ ⟨x⟩) (pointwiseApSection Base Fiber A C t x))
      ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩) =
    (M).identity ((M).identity C (ordinaryApply M A C ⟨t⟩ ⟨x⟩) (ordinaryApply M A C ⟨t⟩ ⟨y⟩))
      (ordinaryApValue M A C ⟨t⟩ ⟨x⟩ ⟨y⟩ ⟨p⟩) (pointwiseApValue Base Fiber A C t x y p) :=
  ((M).identity_sub _ _ _ _).trans ((M).toStructuralModel.identity_congr
    (ordinaryApMotive_endpoint M A C ⟨t⟩ ⟨x⟩ ⟨y⟩ ⟨p⟩) (cast_heq _ _).symm (cast_heq _ _).symm)

def ordinaryActionComparisonValue (y : Term A.family)
    (p : Term (normalizedIdentity A.family x y)) :
    (M).Section Γ ((M).identity ((M).identity C (ordinaryApply M A C ⟨t⟩ ⟨x⟩) (ordinaryApply M A C ⟨t⟩ ⟨y⟩))
      (ordinaryApValue M A C ⟨t⟩ ⟨x⟩ ⟨y⟩ ⟨p⟩) (pointwiseApValue Base Fiber A C t x y p)) :=
  cast (congrArg ((M).Section Γ) (ordinaryActionComparison_endpointFamily Base Fiber A C t x y p))
    ((M).subTm (ordinaryActionComparison Base Fiber A C t x)
      ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩))

end SquareKit.Cubical.Contextual
