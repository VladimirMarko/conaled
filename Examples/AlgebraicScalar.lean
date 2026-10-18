import SquareKit.AlgebraicStage

/-! Experimental nonzero infinitesimal and affine-evaluation consumers.
These test the constructed candidate map, not its still-unproved invertibility.
-/
noncomputable section
namespace Examples.AlgebraicScalar
open CategoryTheory Opposite
open SquareKit.AlgebraicStage SquareKit.SheafFunction

abbrev dualIntegers := Stage.dual .integers

theorem epsilon_nonzero : (DualNumber.eps : Carrier dualIntegers) ≠ 0 := by
  intro h
  have := congrArg TrivSqZeroExt.snd h
  exact Int.one_ne_zero (show (1 : ℤ) = 0 from this)

theorem affine_at_epsilon (a b : ℤ) :
    (evaluation infinitesimal scalar).hom.app (op (op dualIntegers))
      (⟨DualNumber.eps, DualNumber.eps_mul_eps⟩,
        affine.hom.app (op (op dualIntegers))
          (algebraMap ℤ (Carrier dualIntegers) a, algebraMap ℤ (Carrier dualIntegers) b)) =
      (⟨a, b⟩ : DualNumber ℤ) := by
  erw [affine_evaluation]
  change algebraMap ℤ (DualNumber ℤ) a +
    algebraMap ℤ (DualNumber ℤ) b * (DualNumber.eps : DualNumber ℤ) = _
  apply TrivSqZeroExt.ext <;>
    simp

/-- The universal stage map is exercised on both coefficients, not only zero. -/
theorem extension_at_epsilon (a b : ℤ) :
    dualLift .integers dualIntegers
      (algebraMap ℤ (Carrier dualIntegers), ⟨DualNumber.eps, DualNumber.eps_mul_eps⟩)
      (⟨a, b⟩ : DualNumber ℤ) = (⟨a, b⟩ : DualNumber ℤ) := by
  erw [dualLift_apply]
  change algebraMap ℤ (DualNumber ℤ) a +
    algebraMap ℤ (DualNumber ℤ) b * (DualNumber.eps : DualNumber ℤ) = _
  apply TrivSqZeroExt.ext <;>
    simp

/-- Expected coefficient for a later synthetic squaring derivative.
This algebraic prerequisite alone is not the KL derivative construction. -/
theorem square_expansion (A : Stage) (x d : Carrier A) (hd : d * d = 0) :
    (x + d) * (x + d) = x * x + (2 * x) * d := by
  calc
    _ = x * x + (2 * x) * d + d * d := by ring
    _ = _ := by rw [hd, add_zero]

end Examples.AlgebraicScalar
