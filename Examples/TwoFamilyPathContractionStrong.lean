import SquareKit.Internal.PathTransport.TwoFamilyPathContractionStrong
import Examples.TwoFamilyPathContraction
import SquareKit.Internal.PathTransport.TwoFamilyPathFaithful
import Examples.TwoFamilyPathContext
noncomputable section
namespace Examples.TwoFamilyPathContractionStrong
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyPathContext
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩
local instance : ∀ x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀ x, IsLocallyGroupoid (integerFamily.obj x) := fun _ =>
  inferInstanceAs (IsLocallyGroupoid B)

/-- The assembled coherent transformation keeps the nontrivial integer comparison. -/
theorem strong_comparison_retains_integer (k : ℤ) :
    ((TwoFamily.pathContraction integerFamily).naturality (pathArrow k)).hom.base.fiber.2 =
      Multiplicative.ofAdd (-k) := by
  exact Examples.TwoFamilyPathContraction.actual_naturality_retains_integer k
/-- The actual strong comparison at one is not the strict zero shortcut. -/
theorem strong_comparison_nonzero :
    ((TwoFamily.pathContraction integerFamily).naturality (pathArrow 1)).hom.base.fiber.2 ≠
      Multiplicative.ofAdd 0 := by
  rw [strong_comparison_retains_integer]
  change (-1 : ℤ) ≠ 0
  decide
/-- Normalization is checked in this same context with genuine integer 2-cells. -/
example : ((TwoFamily.pathContraction integerFamily).naturality
    ((TwoFamily.pathReflexivity integerFamily).map sourceArrow)).hom =
      eqToHom ((TwoFamily.contraction_refl_left integerFamily sourceArrow).trans
        (TwoFamily.contraction_refl_right integerFamily sourceArrow).symm) := by
  with_reducible exact TwoFamily.pathContraction_naturality_refl integerFamily sourceArrow
end Examples.TwoFamilyPathContractionStrong
