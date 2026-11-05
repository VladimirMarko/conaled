import SquareKit.Internal.PathTransport.TwoFamilyPathContractionCoherence
import SquareKit.Internal.PathTransport.TwoFamilyPathFaithful
import Examples.TwoFamilyPathContext
noncomputable section
namespace Examples.TwoFamilyPathContractionCoherence
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
/-- The first endpoint projection is zero even when the actual second endpoint is nonzero. -/
theorem projected_comparison_zero (k : ℤ) :
    ((TwoFamily.pathFirst integerFamily).map₂
      (TwoFamily.contractionNaturalityCell integerFamily (pathArrow k))).fiber =
        Multiplicative.ofAdd 0 := by
  exact eq_of_heq (TwoFamily.contractionNaturalityCell_firstFiber integerFamily (pathArrow k))
/-- Strong composition coherence specializes to arbitrary integer path-context arrows. -/
example (k l : ℤ) :
    TwoFamily.contractionNaturalityCell integerFamily (pathArrow k ≫ pathArrow l) ≫
      TwoFamily.contractionComponent integerFamily pathPoint ◁
        ((StrictPseudofunctor.id (TwoFamily.PathContext integerFamily)).mapComp (pathArrow k) (pathArrow l)).hom =
    ((TwoFamily.contractionRetract integerFamily).mapComp (pathArrow k) (pathArrow l)).hom ▷
      TwoFamily.contractionComponent integerFamily pathPoint ≫
      (α_ _ _ _).hom ≫ (TwoFamily.contractionRetract integerFamily).map (pathArrow k) ◁
        TwoFamily.contractionNaturalityCell integerFamily (pathArrow l) ≫ (α_ _ _ _).inv ≫
      TwoFamily.contractionNaturalityCell integerFamily (pathArrow k) ▷ pathArrow l ≫ (α_ _ _ _).hom := by
  with_reducible exact TwoFamily.contractionNaturality_comp integerFamily (pathArrow k) (pathArrow l)
end Examples.TwoFamilyPathContractionCoherence
