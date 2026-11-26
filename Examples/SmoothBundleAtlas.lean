import SquareKit.SmoothBundleRecovery
import Mathlib.Algebra.Module.PUnit

/-! Noncompact manifold specializations of the derived represented atlas. -/
noncomputable section
namespace Examples.SmoothBundleAtlas
open CategoryTheory SquareKit SquareKit.ManifoldRealization EuclideanOpen
open scoped Manifold ContDiff

/-- The real line is admitted without compactness or a supplied represented atlas. -/
def realLineAtlas := (ChartFamily.preferred (n := 1) (M := Space 1)).representedAtlas

/-- Its intersections are actual sheaf pullbacks, including at nonreduced stages. -/
theorem realLineAtlas_isPullback (i j : Space 1) :
    IsPullback (embedding.map (realLineAtlas.left i j)) (embedding.map (realLineAtlas.right i j))
      (realLineAtlas.chart i) (realLineAtlas.chart j) :=
  realLineAtlas.square i j

end Examples.SmoothBundleAtlas

namespace Examples.SmoothBundleAtlas
open CategoryTheory SquareKit SquareKit.ManifoldRealization EuclideanOpen SmoothManifoldAction SmoothCech
open scoped Manifold ContDiff

def realLineBundle := SmoothPrincipalBundle.identityBundle (n := 1) (G := PUnit) (B := Space 1)
def realLineObject := realLineBundle.quotientObject realLineBundle.smooth_action id contMDiff_id
  (fun _ _ => rfl)
def realLineRecovery := realLineBundle.quotientRecovery realLineBundle.smooth_action id contMDiff_id
  (fun _ _ => rfl)
def realLineTotalComparison := realLineBundle.totalSpaceIso
def realLineCompleteArrows := derivedArrowEquiv realLineBundle.smooth_action realLineBundle.baseCharts
  realLineObject realLineObject

theorem realLineCompleteArrows_apply_symm_apply (f : SheafActionQuotient.Arrow realLineObject realLineObject) :
    realLineCompleteArrows (realLineCompleteArrows.symm f) = f :=
  realLineCompleteArrows.apply_symm_apply f

def scale (a : ℝ) (x : Space 1) : Space 1 := a • x
theorem scale_smooth (a : ℝ) : ContMDiff (modelWithCorners 1) (modelWithCorners 1) ∞ (scale a) := by
  have h : ContDiff ℝ ∞ (fun x : Space 1 => a • x) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space 1 => a)).smul
      (contDiff_id : ContDiff ℝ ∞ (fun x : Space 1 => x))
  exact h.contMDiff

def firstRestriction := realLineBundle.baseCharts.inverseTarget realLineBundle.baseCharts (scale 2) (scale_smooth 2)
def secondRestriction := realLineBundle.baseCharts.inverseSecond realLineBundle.baseCharts realLineBundle.baseCharts
  (scale 2) (scale_smooth 2) (scale 3) (scale_smooth 3)

theorem interpret_scale_two_ne_id :
    realLineBundle.baseCharts.interpret realLineBundle.baseCharts (scale 2) (scale_smooth 2) ≠ 𝟙 _ := by
  intro h
  have he := congrArg (realLineBundle.baseCharts.reconstruct realLineBundle.baseCharts) h
  rw [ChartFamily.reconstruct_interpret, ChartFamily.reconstruct_id] at he
  have hx := congrArg (fun f : Space 1 → Space 1 => f (fun _ => 1) 0) he
  norm_num [scale] at hx

theorem composite_base :
    (realLineBundle.baseCharts.interpret
      (realLineBundle.baseCharts.inverseCharts realLineBundle.baseCharts (scale 2) (scale_smooth 2))
      (scale 3) (scale_smooth 3) ≫
      ((realLineBundle.baseCharts.inverseCharts realLineBundle.baseCharts (scale 2) (scale_smooth 2)).comparison
        realLineBundle.baseCharts).hom) ≫
      realLineBundle.baseCharts.interpret realLineBundle.baseCharts (scale 2) (scale_smooth 2) =
    realLineBundle.baseCharts.interpret realLineBundle.baseCharts (scale 2 ∘ scale 3)
      ((scale_smooth 2).comp (scale_smooth 3)) :=
  realLineBundle.baseCharts.inverseSecond_base_comp realLineBundle.baseCharts realLineBundle.baseCharts
    (scale 2) (scale_smooth 2) (scale 3) (scale_smooth 3)

/-- Sequential nonidentity restrictions retain the complete datum equality. -/
theorem composite_datum :
    (realLineBundle.ordinaryDatum.restrict firstRestriction).restrict secondRestriction =
      realLineBundle.ordinaryDatum.restrict (firstRestriction.comp secondRestriction) :=
  realLineBundle.ordinaryDatum.restrict_comp firstRestriction secondRestriction

/-- The selected global comparisons compose only after the displayed equality transport. -/
theorem composite_comparison :
    (((realLineBundle.ordinaryDatum.restrictComparison firstRestriction realLineBundle.smooth_action).reindex _).comp
      ((realLineBundle.ordinaryDatum.restrict firstRestriction).restrictComparison secondRestriction
        realLineBundle.smooth_action)).comp
      (eqToHom (congrArg (fun p => p.interpreted realLineBundle.smooth_action) composite_datum)) =
    realLineBundle.ordinaryDatum.restrictComparison (firstRestriction.comp secondRestriction)
      realLineBundle.smooth_action :=
  realLineBundle.ordinaryDatum.restrictComparison_comp firstRestriction secondRestriction realLineBundle.smooth_action
end Examples.SmoothBundleAtlas

namespace Examples.SmoothBundleAtlas
open CategoryTheory SquareKit SquareKit.ManifoldRealization EuclideanOpen SmoothManifoldAction SmoothCech
open scoped Manifold ContDiff

def realLineChartChoice := chartChoiceComparison realLineBundle.smooth_action realLineBundle.baseCharts
  realLineBundle.ordinaryDatum

def threeObjects (_ : Fin 3) := realLineObject
def simultaneousTrivialization := jointTrivialized realLineBundle.smooth_action realLineBundle.baseCharts threeObjects

theorem simultaneous_composition
    (f : Hom (simultaneousTrivialization 0).extractedDatum (simultaneousTrivialization 1).extractedDatum)
    (g : Hom (simultaneousTrivialization 1).extractedDatum (simultaneousTrivialization 2).extractedDatum) :
    jointArrowEquiv realLineBundle.smooth_action realLineBundle.baseCharts threeObjects 0 2 (f.comp g) =
      (jointArrowEquiv realLineBundle.smooth_action realLineBundle.baseCharts threeObjects 0 1 f).comp
        (jointArrowEquiv realLineBundle.smooth_action realLineBundle.baseCharts threeObjects 1 2 g) :=
  joint_composition realLineBundle.smooth_action realLineBundle.baseCharts threeObjects 0 1 2 f g

/-- Empty represented domains are admitted by the same local-surjectivity construction. -/
def emptyDomain : Domain := ⟨1,0⟩
def emptyRecovery (P : SheafActionQuotient.Object (representation realLineBundle.smooth_action).action
    (embedding.obj emptyDomain)) :=
  (trivializedOnOpen realLineBundle.smooth_action emptyDomain P).extractedRecovery
end Examples.SmoothBundleAtlas
