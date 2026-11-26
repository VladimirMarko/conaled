import SquareKit.SmoothChartPullback
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! Chart inclusions cancel at arbitrary sheaf stages, using their represented overlaps. -/
noncomputable section

namespace SquareKit.ManifoldRealization.ChartFamily
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite SmoothAlgebra
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A : ChartFamily n M)

theorem self_left_eq_right (i : A.Index) : A.left i i = A.right i i := by
  apply OpenFunctions.Map.ext
  intro x
  apply (chartPoint_isOpenEmbedding (A.chart i)).injective
  exact A.agreement i i x

/-- The represented self-overlap proves cancellation against every sheaf test object. -/
instance chart_mono (i : A.Index) : Mono (A.charts.chart i) where
  right_cancellation {Z} u v h := by
    let hp := A.chart_pullback i i
    calc
      u = hp.lift u v h ≫ embedding.map (A.left i i) := (hp.lift_fst u v h).symm
      _ = hp.lift u v h ≫ embedding.map (A.right i i) :=
        congrArg (fun k => hp.lift u v h ≫ embedding.map k) (A.self_left_eq_right i)
      _ = v := hp.lift_snd u v h

/-- This includes infinitesimal presentation stages, not only real points. -/
theorem chart_stage_injective (i : A.Index) (V : SmoothPresentationSite.Site) :
    Function.Injective ((A.charts.chart i).hom.app (op V)) :=
  CategoryTheory.mono_iff_injective _ |>.mp inferInstance

theorem chart_stage_cancel (i : A.Index) (V : SmoothPresentationSite.Site)
    (x y : (embedding.obj (A.charts.domain i)).obj.obj (op V))
    (h : (A.charts.chart i).hom.app (op V) x = (A.charts.chart i).hom.app (op V) y) :
    x = y := A.chart_stage_injective i V h

section Saturation
open SmoothPresentationSite SmoothAlgebra.Localization
variable (i j : A.Index) (B : Code)
  (b : Hom (Principal (A.charts.domain j).defining) (Carrier B))
  (hb : ∀ h : Hom (Carrier B) ℝ,
    chartPoint (A.chart j) (realPoints (A.charts.domain j).defining (h.comp b)) ∈
      (A.chart i).source)

include hb in
/-- Real reductions detect the unit needed to enter the ordinary chart overlap. -/
theorem chartOverlap_unit :
    IsUnit (b (principalBase (A.charts.domain j).defining (A.overlapDefining j i))) := by
  apply unit_of_real_points B
  intro h
  change (h.comp b) (principalBase (A.charts.domain j).defining (A.overlapDefining j i)) ≠ 0
  rw [point_base]
  apply (coordinateDefining_iff (A.chart i) id continuous_id _).mpr
  refine ⟨?_, hb h⟩
  exact (chartDomain_locus (A.chart j)) ▸
    (realPoints (A.charts.domain j).defining (h.comp b)).property

def chartOverlapLift : Hom (Principal (A.pair j i).defining) (Carrier B) :=
  subLift (A.charts.domain j).defining (A.overlapDefining j i) b
    (A.chartOverlap_unit i j B b hb)

theorem chartOverlapLift_left :
    (A.chartOverlapLift i j B b hb).comp (Localization.pullback (A.left j i)) = b := by
  rw [nested_pullback]
  exact subLift_base _ _ _ _

/-- A full stage whose real images lie in a chart admits a section of that chart. -/
def chartSaturation : Hom (Principal (A.charts.domain i).defining) (Carrier B) :=
  (A.chartOverlapLift i j B b hb).comp (Localization.pullback (A.right j i))

theorem chartSaturation_chart :
    (A.charts.chart i).hom.app (op (op B))
        (show code (A.charts.domain i) ⟶ B from A.chartSaturation i j B b hb).op =
      (A.charts.chart j).hom.app (op (op B))
        (show code (A.charts.domain j) ⟶ B from b).op := by
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun k => k.hom) (A.chart_pullback j i).w) (op (op B)))
    (show code (A.pair j i) ⟶ B from A.chartOverlapLift i j B b hb).op
  change (A.charts.chart j).hom.app (op (op B))
      (show code (A.charts.domain j) ⟶ B from
        (A.chartOverlapLift i j B b hb).comp (Localization.pullback (A.left j i))).op =
    (A.charts.chart i).hom.app (op (op B))
      (show code (A.charts.domain i) ⟶ B from A.chartSaturation i j B b hb).op at he
  exact he.symm.trans (congrArg
    (fun d : Hom (Principal (A.charts.domain j).defining) (Carrier B) =>
      (A.charts.chart j).hom.app (op (op B))
        (show code (A.charts.domain j) ⟶ B from d).op)
    (A.chartOverlapLift_left i j B b hb))

theorem chartSaturation_unique
    (c : Hom (Principal (A.charts.domain i).defining) (Carrier B))
    (hc : (A.charts.chart i).hom.app (op (op B))
      (show code (A.charts.domain i) ⟶ B from c).op =
      (A.charts.chart j).hom.app (op (op B))
        (show code (A.charts.domain j) ⟶ B from b).op) :
    c = A.chartSaturation i j B b hb := by
  exact congrArg Quiver.Hom.unop
    (A.chart_stage_injective i (op B) (hc.trans (A.chartSaturation_chart i j B b hb).symm))

end Saturation

end SquareKit.ManifoldRealization.ChartFamily
