import SquareKit.SmoothLocalChartLaws
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Experimental ordinary finite-dimensional real manifold charts. The model
is the full Euclidean space, so boundary charts are excluded. No Hausdorff or
second-countability assumption is needed for these local constructions. -/
noncomputable section
open CategoryTheory Set IsManifold
open scoped Manifold ContDiff
namespace SquareKit.ManifoldRealization
open EuclideanOpen SmoothAlgebra

abbrev Space (n : ℕ) := Fin n → ℝ
abbrev Model (n : ℕ) := 𝓘(ℝ, Space n)

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]

/-- An arbitrary small covering family of actual smooth manifold charts. -/
structure ChartFamily (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Space n) M] where
  Index : Type
  chart : Index → OpenPartialHomeomorph M (Space n)
  smooth : ∀ i, chart i ∈ maximalAtlas (Model n) ∞ M
  covers : ∀ x, ∃ i, x ∈ (chart i).source

namespace ChartFamily

variable [ChartedSpace (Space n) M]

abbrev preferred [IsManifold (Model n) ∞ M] : ChartFamily n M where
  Index := M
  chart := chartAt (Space n)
  smooth := chart_mem_maximalAtlas
  covers x := ⟨x,mem_chart_source _ x⟩

end ChartFamily

variable (e : OpenPartialHomeomorph M (Space n))

abbrev chartDomain : Domain := ⟨n,openDefining e.target e.open_target⟩

theorem chartDomain_locus : Points (chartDomain e) = e.target :=
  openDefining_locus e.target e.open_target

def chartPoint (x : Points (chartDomain e)) : M := e.symm x.val

def chartTargetEquiv : Points (chartDomain e) ≃ₜ e.target := Homeomorph.setCongr (chartDomain_locus e)

theorem chartPoint_openEmbedding : Topology.IsOpenEmbedding (chartPoint e) :=
  e.symm.isOpenEmbedding_restrict.comp (chartTargetEquiv e).isOpenEmbedding

theorem chartPoint_source (x : Points (chartDomain e)) : chartPoint e x ∈ e.source :=
  e.map_target ((chartDomain_locus e) ▸ x.property)

variable {e} (d : OpenPartialHomeomorph N (Space m)) (f : M → N) (hf : Continuous f)

def coordinateOpen : Set (Space n) := e.target ∩ e.symm ⁻¹' (f ⁻¹' d.source)

include hf in
theorem coordinateOpen_open : IsOpen (coordinateOpen (e := e) d f) :=
  e.isOpen_inter_preimage_symm (d.open_source.preimage hf)

def coordinateDefining : Free n :=
  openDefining (coordinateOpen (e := e) d f) (coordinateOpen_open d f hf)

theorem coordinateDefining_iff (x : Space n) :
    (coordinateDefining (e := e) d f hf).val x ≠ 0 ↔ x ∈ e.target ∧ f (e.symm x) ∈ d.source := by
  change x ∈ Localization.locus (openDefining _ _) ↔ _
  rw [openDefining_locus]
  rfl

variable [ChartedSpace (Space n) M] [ChartedSpace (Space m) N]

variable (he : e ∈ maximalAtlas (Model n) ∞ M) (hd : d ∈ maximalAtlas (Model m) ∞ N)
    (hs : ContMDiff (Model n) (Model m) ∞ f)

def coordinateMap : subdomain (chartDomain e) (coordinateDefining (e := e) d f hs.continuous) ⟶ chartDomain d where
  toFun x := ⟨d (f (e.symm x.val)), by
    change d (f (e.symm x.val)) ∈ Points (chartDomain d)
    rw [chartDomain_locus]
    exact d.map_source ((coordinateDefining_iff d f hs.continuous x.val).mp
      (right_ne_zero_of_mul x.property)).2⟩
  smooth i := by
    apply (OpenFunctions.representative_iff _ (fun x => d (f (e.symm x)) i) (fun _ => rfl)).mpr
    intro x hx
    have hp := (coordinateDefining_iff d f hs.continuous x).mp (right_ne_zero_of_mul hx)
    have h₁ := contMDiffAt_symm_of_mem_maximalAtlas he hp.1
    have h₂ := (hs (e.symm x)).comp x h₁
    have h₃ := (contMDiffAt_of_mem_maximalAtlas hd hp.2).comp x h₂
    exact ((contDiff_apply ℝ (fun _ : Fin m => ℝ) i).contDiffAt.comp x h₃.contDiffAt).contDiffWithinAt

theorem coordinateMap_agreement (x : Points (subdomain (chartDomain e)
    (coordinateDefining (e := e) d f hs.continuous))) :
    f (chartPoint e ((show EuclideanOpen.Map _ _ from subInclusion _ _) x)) =
      chartPoint d ((show EuclideanOpen.Map _ _ from coordinateMap d f he hd hs) x) :=
  (d.left_inv ((coordinateDefining_iff d f hs.continuous x.val).mp
    (right_ne_zero_of_mul x.property)).2).symm

namespace ChartFamily
variable (A : ChartFamily n M)

abbrev charts : EuclideanOpen.Charts M where
  Index := A.Index
  domain i := chartDomain (A.chart i)
  coordinate i := chartPoint (A.chart i)

abbrev atlas : EuclideanOpen.Atlas M where
  toCharts := A.charts
  openEmbedding i := chartPoint_openEmbedding (A.chart i)
  covers x := by
    obtain ⟨i,hi⟩ := A.covers x
    refine ⟨i,⟨A.chart i x,?_⟩, (A.chart i).left_inv hi⟩
    rw [chartDomain_locus]
    exact (A.chart i).map_source hi
  transition i j x y h := by
    have hs : ContMDiff (Model n) (Model n) ∞ (id : M → M) := contMDiff_id
    refine ⟨coordinateDefining (A.chart j) id hs.continuous,?_,
      coordinateMap (A.chart j) id (A.smooth i) (A.smooth j) hs,?_⟩
    · apply (coordinateDefining_iff (A.chart j) id hs.continuous x.val).mpr
      refine ⟨(chartDomain_locus (A.chart i)) ▸ x.property,?_⟩
      change chartPoint (A.chart i) x ∈ (A.chart j).source
      change chartPoint (A.chart i) x = chartPoint (A.chart j) y at h
      rw [h]
      exact chartPoint_source (A.chart j) y
    · exact coordinateMap_agreement (A.chart j) id (A.smooth i) (A.smooth j) hs

/-- Every Mathlib smooth map supplies local ordinary coordinates, with a cover
indexed by target charts. No source chart needs a single target chart. -/
def localMap (B : ChartFamily m N) (f : M → N) (hs : ContMDiff (Model n) (Model m) ∞ f) :
    EuclideanOpen.Charts.LocalMap A.charts B.charts f where
  Cover _ := B.Index
  defining i j := coordinateDefining (e := A.chart i) (B.chart j) f hs.continuous
  covers i x := by
    obtain ⟨j,hj⟩ := B.covers (f (chartPoint (A.chart i) x))
    exact ⟨j,(coordinateDefining_iff (B.chart j) f hs.continuous x.val).mpr
      ⟨(chartDomain_locus (A.chart i)) ▸ x.property,hj⟩⟩
  index _ j := j
  coordinate i j := coordinateMap (B.chart j) f (A.smooth i) (B.smooth j) hs
  agreement i j := coordinateMap_agreement (B.chart j) f (A.smooth i) (B.smooth j) hs

end ChartFamily
end SquareKit.ManifoldRealization
