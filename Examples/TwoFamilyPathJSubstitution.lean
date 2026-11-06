import SquareKit.Internal.PathTransport.TwoFamilySectionMapReindex
import SquareKit.Internal.PathTransport.TwoFamilyPathJSubstitution
import Examples.TwoFamilyPathJBeta
import Examples.TwoFamilyPathSubstitution
noncomputable section
namespace Examples.TwoFamilyPathJSubstitution
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyPathContext
open Examples.TwoFamilyPathSubstitution
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
/-- Substitute the selected generic-variable branch along the actual context projection. -/
def branch := pathBranchReindex integerFamily substitution
  TwoFamilyPathJBeta.motive TwoFamilyPathJBeta.branch
/-- The substituted branch retains the supplied integer in its genuine cell action. -/
theorem branch_retains_integer (k : ℤ) :
    HEq (branch.lift.map₂ (liftedSourceCell k)).fiber (Multiplicative.ofAdd k) := by
  have h1 := pathBranchReindex_cell integerFamily substitution
    TwoFamilyPathJBeta.motive TwoFamilyPathJBeta.branch (liftedSourceCell k)
  have h2 := Section.cast_cell_fiber TwoFamilyPathJBeta.reflexive_motive.symm
    (variableSection integerFamily) ((reindexHigher integerFamily substitution).map₂ (liftedSourceCell k))
  exact h1.trans h2
/-- The substituted branch still distinguishes a nonzero genuine cell. -/
theorem branch_erasure_rejected :
    ¬ HEq (branch.lift.map₂ (liftedSourceCell 1)).fiber (Multiplicative.ofAdd (0 : ℤ)) := by
  intro h
  have h10 := eq_of_heq ((branch_retains_integer 1).symm.trans h)
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd h10)
/-- The supplied variable branch pulled back to the whole path context. -/
def pulledBranch : Section (reindex (contractionRetract integerFamily) TwoFamilyPathJBeta.motive) :=
  Section.cast (reindex_comp TwoFamilyPathJBeta.motive (pathReflexivity integerFamily)
    (pathFirst integerFamily))
    (TwoFamilyPathJBeta.branch.reindex _ (pathFirst integerFamily))

/-- Coherent contraction transport of this actual branch commutes with context pullback. -/
example :
    (pulledBranch.map (strongPostcomp (pathContraction integerFamily) TwoFamilyPathJBeta.motive)).reindex _
      (pathReindex integerFamily substitution) =
    (pulledBranch.reindex _ (pathReindex integerFamily substitution)).map
      (strongPrecomp (strongPostcomp (pathContraction integerFamily) TwoFamilyPathJBeta.motive)
        (pathReindex integerFamily substitution)) :=
  Section.map_reindex _ _ pulledBranch
end Examples.TwoFamilyPathJSubstitution
