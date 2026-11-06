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

end Examples.TwoStrongInverse
