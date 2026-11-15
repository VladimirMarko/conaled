import SquareKit.Internal.PathTransport.TwoFamilyModelComparisons
import SquareKit.Internal.PathTransport.TwoFamilySubstitution
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
theorem familySubstitution_down_eq {Γ Δ : Context.{u}} (E : Family Γ) (F : Family Δ)
    (σ : ULift.{u+1} (StrictPseudofunctor Δ Γ)) (e : F = E.reindex σ.down) :
    ((M).compSub ((M).lift E σ) ((M).familyComparison e)).down =
      TwoFamily.familySubstitution E.data σ.down (congrArg Family.data e) := by
  change (((M).familyComparison e).down).comp (((M).lift E σ).down) = _
  rw [familyComparison_eq_familyCast, lift_down_eq_reindexHigher]
  rfl
end SquareKit.Internal.PathTransport.HigherInterpretation
