import SquareKit.Internal.PathTransport.TwoFamilyReindex
import Examples.TwoFamily

/-! Reindexing and inverse laws preserve the selected integer path data. -/
namespace Examples.TwoFamilyReindex
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local instance : IsGroupoid TwoGroupoidPath.Base where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩

local instance : IsGroupoid (LocallyDiscrete TwoGroupoidPath.Fiber) where
  all_isIso f := by
    refine ⟨⟨Discrete.mk (inv f.as), ?_, ?_⟩⟩
    · apply Discrete.ext
      exact IsIso.hom_inv_id f.as
    · apply Discrete.ext
      exact IsIso.inv_hom_id f.as

local instance : ∀ x, IsGroupoid (pathFamily.obj x) := fun _ =>
  inferInstanceAs (IsGroupoid (LocallyDiscrete TwoGroupoidPath.Fiber))

/-- The derived total inverse cancels the actual selected integer arrow. -/
theorem integer_inverse (n : ℤ) :
    arrow n ≫ (TwoFamily.arrowIso pathFamily (arrow n)).inv = 𝟙 point :=
  (TwoFamily.arrowIso pathFamily (arrow n)).hom_inv_id

def reindexedPoint : TwoFamily.Total
    (TwoFamily.reindex (StrictPseudofunctor.id TwoGroupoidPath.Base) pathFamily) :=
  ⟨point.base, point.fiber⟩

def reindexedArrow (n : ℤ) : reindexedPoint ⟶ reindexedPoint :=
  ⟨DoubleDelooping.arrow _, Discrete.mk (Multiplicative.ofAdd n)⟩

/-- Identity substitution retains the selected fiber arrow, not just its base. -/
theorem identity_substitution (n : ℤ) :
    (TwoFamily.reindexFunctor pathFamily (StrictPseudofunctor.id TwoGroupoidPath.Base)).map
      (reindexedArrow n) = arrow n := rfl

end Examples.TwoFamilyReindex
