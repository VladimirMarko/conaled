import SquareKit.Internal.PathTransport.TwoFamilyPathJCells
import Examples.TwoFamilyPathContraction
import SquareKit.Internal.PathTransport.TwoFamilyPathFaithful
import Examples.TwoFamilyPathContext
noncomputable section
namespace Examples.TwoFamilyPathJBeta
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


open TwoFamily
abbrev motive := reindex (pathFirst integerFamily)
  (reindex (projectionHigher integerFamily) integerFamily)

theorem reflexive_motive : reindex (pathReflexivity integerFamily) motive =
    reindex (projectionHigher integerFamily) integerFamily := by
  exact (reindex_comp _ (pathFirst integerFamily) (pathReflexivity integerFamily)).trans
    ((congrArg (fun H => reindex H (reindex (projectionHigher integerFamily) integerFamily))
      (pathReflexivity_first integerFamily)).trans (reindex_id _))

/-- The branch is the actual generic variable, with only its family boundary cast. -/
def branch : Section (reindex (pathReflexivity integerFamily) motive) :=
  Section.cast reflexive_motive.symm (variableSection integerFamily)

/-- Whole-section computation retains the selected branch including higher action. -/
theorem recovered_branch :
    (pathJ integerFamily motive branch).reindex motive (pathReflexivity integerFamily) =
      branch := pathJ_beta integerFamily motive branch

/-- Every integer remains the fiber action of the constructed eliminator at reflexivity. -/
theorem retained_integer (k : ℤ) :
    HEq (((pathJ integerFamily motive branch).lift.map₂
      ((pathReflexivity integerFamily).map₂ (sourceCell k))).fiber)
      (Multiplicative.ofAdd k) := by
  have h1 := pathJ_cell_beta integerFamily motive branch (sourceCell k)
  have h2 := Section.cast_cell_fiber reflexive_motive.symm (variableSection integerFamily)
    (sourceCell k)
  exact h1.trans h2

/-- Erasing higher motive action loses a selected integer in this same interpretation. -/
theorem higher_erasure_rejected :
    ¬ HEq (((pathJ integerFamily motive branch).lift.map₂
      ((pathReflexivity integerFamily).map₂ (sourceCell 1))).fiber)
      (Multiplicative.ofAdd (0 : ℤ)) := by
  intro h
  have h10 : (Multiplicative.ofAdd (1 : ℤ)) = Multiplicative.ofAdd 0 :=
    eq_of_heq ((retained_integer 1).symm.trans h)
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd h10)
end Examples.TwoFamilyPathJBeta
