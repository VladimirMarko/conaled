import SquareKit.Internal.PathTransport.TwoFamilyContractionRetraction
import SquareKit.Internal.PathTransport.TwoFamilyRetractionJ
import SquareKit.Internal.PathTransport.TwoFamilyMapComposition
import SquareKit.Internal.PathTransport.TwoFamilyCoherentLift
import SquareKit.Internal.PathTransport.TwoStrongInverseIdentity
import SquareKit.Internal.PathTransport.TwoStrongInverseCancellation
import SquareKit.Internal.PathTransport.TwoStrongInverseSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyContractionInverse
import Examples.TwoFamilyPathJBeta
noncomputable section
namespace Examples.TwoStrongInverse
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyPathContext
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩
local instance : ∀ x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀ x, IsLocallyGroupoid (integerFamily.obj x) := fun _ =>
  inferInstanceAs (IsLocallyGroupoid B)

abbrev contraction := TwoFamily.pathContraction integerFamily

/-- Reversing the actual path contraction admits every genuine integer boundary. -/
example (a b : ℤ) :
    (StrictPseudofunctor.id (TwoFamily.PathContext integerFamily)).map₂ (pathCell a b) ▷
        inv (contraction.app pathPoint) ≫ inverseComparison contraction (pathArrow b) =
      inverseComparison contraction (pathArrow a) ≫ inv (contraction.app pathPoint) ◁
        (TwoFamily.contractionRetract integerFamily).map₂ (pathCell a b) :=
  inverseComparison_naturality contraction (pathCell a b)

/-- The inverse comparison recovers the chosen square, including its integer observer. -/
theorem recovered_integer (k : ℤ) :
    ((mateEquiv (TwoIdentityTransport.inverseAdjunction (contraction.app pathPoint))
      (TwoIdentityTransport.inverseAdjunction (contraction.app pathPoint))).symm
        (inv (inverseComparison contraction (pathArrow k)))).base.fiber.2 =
          Multiplicative.ofAdd (-k) := by
  rw [inverseComparison_recover]
  exact Examples.TwoFamilyPathContraction.actual_naturality_retains_integer k

/-- Recovery from the inverse comparison still rejects replacing the selected square by zero. -/
theorem recovered_nonzero :
    ((mateEquiv (TwoIdentityTransport.inverseAdjunction (contraction.app pathPoint))
      (TwoIdentityTransport.inverseAdjunction (contraction.app pathPoint))).symm
        (inv (inverseComparison contraction (pathArrow 1)))).base.fiber.2 ≠
          Multiplicative.ofAdd 0 := by
  rw [recovered_integer]
  change (-1 : ℤ) ≠ 0
  decide

/-- Backward transport of the chosen higher motive recovers every supplied fiber element. -/
example (x : TwoFamily.Total TwoFamilyPathJBeta.motive) :
    (TwoFamilyPathJBeta.motive.map (contraction.app x.base)).obj
      ((TwoFamilyPathJBeta.motive.map (inv (contraction.app x.base))).obj x.fiber) = x.fiber :=
  TwoFamily.contractionLiftBoundary _ contraction TwoFamilyPathJBeta.motive x

/-- The actual higher path contraction cancels with its constructed inverse. -/
example : Pseudofunctor.StrongTrans.vcomp (strongInverse contraction) contraction =
    Pseudofunctor.StrongTrans.id (StrictPseudofunctor.id
      (TwoFamily.PathContext integerFamily)).toPseudofunctor :=
  strongInverse_vcomp contraction

/-- Backward then forward motive transport fixes the entire total higher context. -/
example :
    (TwoFamily.contractionBack (TwoFamily.contractionRetract integerFamily) contraction
      TwoFamilyPathJBeta.motive).comp
        (TwoFamily.StrongMap.toHigher (TwoFamily.forwardFamilyContraction
          (TwoFamily.contractionRetract integerFamily) contraction TwoFamilyPathJBeta.motive)) =
      StrictPseudofunctor.id (TwoFamily.Total TwoFamilyPathJBeta.motive) := by
  change (TwoFamily.StrongMap.toHigher (strongInverse _)).comp
    (TwoFamily.StrongMap.toHigher _) = _
  rw [TwoFamily.StrongMap.toHigher_vcomp, strongInverse_vcomp, TwoFamily.StrongMap.toHigher_id]

/-- Identity normalization does not change the higher path context. -/
example : strongInverse (Pseudofunctor.StrongTrans.id
    (StrictPseudofunctor.id (TwoFamily.PathContext integerFamily)).toPseudofunctor) =
      Pseudofunctor.StrongTrans.id
        (StrictPseudofunctor.id (TwoFamily.PathContext integerFamily)).toPseudofunctor :=
  strongInverse_id

/-- Adding a dependent element preserves the selected integer comparison in the base. -/
theorem lifted_comparison_retains_integer (k : ℤ)
    (a : TwoFamilyPathJBeta.motive.obj
      ((TwoFamily.contractionRetract integerFamily).obj pathPoint)) :
    ((TwoFamily.coherentLift contraction TwoFamilyPathJBeta.motive).naturality
      (TwoFamily.cartesianLift
        (TwoFamily.reindex (TwoFamily.contractionRetract integerFamily) TwoFamilyPathJBeta.motive)
        (pathArrow k) a)).hom.base.base.fiber.2 = Multiplicative.ofAdd (-k) :=
  Examples.TwoFamilyPathContraction.actual_naturality_retains_integer k

/-- The reflexive extended context retracts through the constructed backwards transport. -/
example :
    (TwoFamily.contractionRetraction (TwoFamily.pathReflexivity integerFamily)
      (TwoFamily.pathFirst integerFamily) contraction TwoFamilyPathJBeta.motive).comp
      (TwoFamily.reindexHigher TwoFamilyPathJBeta.motive (TwoFamily.pathReflexivity integerFamily)) =
        TwoFamily.contractionLift (TwoFamily.contractionRetract integerFamily)
          contraction TwoFamilyPathJBeta.motive :=
  TwoFamily.contractionRetraction_inclusion _ _ _ _

/-- Generic contraction elimination recovers the checked higher path eliminator. -/
example : TwoFamily.retractionJ (TwoFamily.pathReflexivity integerFamily)
    (TwoFamily.pathFirst integerFamily) contraction TwoFamilyPathJBeta.motive TwoFamilyPathJBeta.branch =
      TwoFamily.pathJ integerFamily TwoFamilyPathJBeta.motive TwoFamilyPathJBeta.branch := rfl

end Examples.TwoStrongInverse
