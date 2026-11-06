import SquareKit.Internal.PathTransport.TwoFamilyClosedReflexivitySubstitution
import SquareKit.Internal.PathTransport.TwoFamilyEndpointSubstitution
import Examples.TwoFamilyClosedIdentity
/-! Closed identity substitution along two actual context projections. -/
namespace Examples.TwoFamilyClosedIdentitySubstitution
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyEndpointSections
open TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g,h,k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g,h,k⟩⟩
local instance : ∀ x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀ x, IsLocallyGroupoid (integerFamily.obj x) := fun _ =>
  inferInstanceAs (IsLocallyGroupoid B)

abbrev σ := projectionHigher displayed
abbrev τ := projectionHigher (reindex σ displayed)

example : reindex τ (reindex σ (closedId displayed selected selected)) =
    closedId (reindex τ (reindex σ displayed))
      ((selected.reindex displayed σ).reindex _ τ)
      ((selected.reindex displayed σ).reindex _ τ) := by
  rw [closedId_reindex, closedId_reindex]

example : HEq (endpointPair (reindex σ displayed)
    (selected.reindex displayed σ) (selected.reindex displayed σ))
    ((endpointPair displayed selected selected).reindex _ σ) :=
  endpointPair_reindex_heq displayed selected selected σ

example : (endpointPair (reindex σ displayed)
    (selected.reindex displayed σ) (selected.reindex displayed σ)).lift.comp
      (endpointReindex displayed σ) = σ.comp (endpointPair displayed selected selected).lift :=
  endpointPair_lift_reindex displayed σ selected selected
example : HEq ((closedReflexivity displayed selected).reindex _ σ)
    (closedReflexivity (reindex σ displayed) (selected.reindex displayed σ)) :=
  closedReflexivity_reindex_heq displayed σ selected

end Examples.TwoFamilyClosedIdentitySubstitution
