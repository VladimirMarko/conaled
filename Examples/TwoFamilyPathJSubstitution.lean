import SquareKit.Internal.PathTransport.TwoFamilyPathJReindex
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
/-- The actual contraction comparison for any integer arrow is preserved by substitution. -/
example (k : ℤ) : HEq
    ((pathReindex integerFamily substitution).map₂
      (contractionNaturalityCell pulledFamily (liftedPathArrow k)))
    (contractionNaturalityCell integerFamily
      ((pathReindex integerFamily substitution).map (liftedPathArrow k))) :=
  contractionNaturalityCell_reindex integerFamily substitution (liftedPathArrow k)
/-- The constructed eliminator itself commutes with the nonidentity context projection. -/
theorem j_reindexes :
    (pathJ integerFamily TwoFamilyPathJBeta.motive TwoFamilyPathJBeta.branch).reindex _
      (pathReindex integerFamily substitution) =
    pathJ pulledFamily (reindex (pathReindex integerFamily substitution) TwoFamilyPathJBeta.motive) branch :=
  pathJ_reindex integerFamily substitution TwoFamilyPathJBeta.motive TwoFamilyPathJBeta.branch

/-- J after substitution still retains every selected integer in its higher action. -/
theorem substituted_j_retains_integer (k : ℤ) :
    HEq ((pathJ pulledFamily (reindex (pathReindex integerFamily substitution) TwoFamilyPathJBeta.motive)
      branch).lift.map₂ ((pathReflexivity pulledFamily).map₂ (liftedSourceCell k))).fiber
      (Multiplicative.ofAdd k) := by
  exact (pathJ_cell_beta pulledFamily _ branch (liftedSourceCell k)).trans (branch_retains_integer k)

/-- The same substituted eliminator rejects higher erasure. -/
theorem substituted_j_erasure_rejected :
    ¬ HEq ((pathJ pulledFamily (reindex (pathReindex integerFamily substitution) TwoFamilyPathJBeta.motive)
      branch).lift.map₂ ((pathReflexivity pulledFamily).map₂ (liftedSourceCell 1))).fiber
      (Multiplicative.ofAdd (0 : ℤ)) := by
  intro h
  have h10 := eq_of_heq ((substituted_j_retains_integer 1).symm.trans h)
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd h10)
end Examples.TwoFamilyPathJSubstitution
