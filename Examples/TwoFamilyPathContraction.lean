import SquareKit.Internal.PathTransport.TwoFamilyPathContractionArrows
import Examples.TwoFamilyPathContext
noncomputable section
namespace Examples.TwoFamilyPathContraction
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
/-- The actual endpoint comparison records the negative of the path-arrow integer. -/
theorem square_retains_integer (k : ℤ) :
    (TwoFamily.contractionEndpointSquare integerFamily (pathArrow k)).fiber.2 =
      Multiplicative.ofAdd (-k) := by
  simp [TwoFamily.contractionEndpointSquare, TwoIdentityTransport.pathSquare,
    TwoGroupoidHom.cell, pathArrow]
  change (inv (Multiplicative.ofAdd k) : arrow ⟶ arrow) = (Multiplicative.ofAdd k)⁻¹
  rw [← Groupoid.inv_eq_inv]
  rfl
/-- The comparison cannot be replaced by a zero endpoint cell. -/
theorem square_nonzero :
    (TwoFamily.contractionEndpointSquare integerFamily (pathArrow 1)).fiber.2 ≠
      Multiplicative.ofAdd 0 := by
  rw [square_retains_integer]
  change (-1 : ℤ) ≠ 0
  decide
/-- The lifted comparison retains the same integer endpoint cell. -/
theorem lifted_square_retains_integer (k : ℤ) :
    (TwoFamily.contractionLiftCell integerFamily (pathArrow k)).base.fiber.2 =
      Multiplicative.ofAdd (-k) :=
  square_retains_integer k

/-- Identity-fiber action cancels the supplied genuine path-arrow integer. -/
theorem square_fiber_action (k : ℤ) :
    (TwoFamily.openIdCell integerFamily
      (TwoFamily.contractionEndpointSquare integerFamily (pathArrow k))).app arrow =
        Multiplicative.ofAdd (-k) := by
  apply eq_of_heq
  apply HEq.trans (TwoFamily.contractionEndpointSquare_action integerFamily (pathArrow k))
  apply heq_of_eq
  change (inv (Multiplicative.ofAdd k) : arrow ⟶ arrow) = (Multiplicative.ofAdd k)⁻¹
  rw [← Groupoid.inv_eq_inv]
  rfl
theorem actual_naturality_retains_integer (k : ℤ) :
    (TwoFamily.contractionNaturalityCell integerFamily (pathArrow k)).base.fiber.2 =
      Multiplicative.ofAdd (-k) := by
  have h := eq_of_heq (TwoFamily.contractionNaturalityCell_endpoint_heq integerFamily (pathArrow k))
  exact (congrArg Prod.snd h).trans (square_retains_integer k)
end Examples.TwoFamilyPathContraction
