import SquareKit.SmoothPrincipalBundle
import SquareKit.SmoothManifoldRepresentedAtlas
import SquareKit.SmoothManifoldPrincipalMaps

/-! Ordinary base and total-space charts derived from local bundle sheets. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory ManifoldRealization EuclideanOpen SmoothAlgebra IsManifold
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

def localAt (b : B) : LocalTrivialization (n := n) (G := G) P.projection :=
  (P.triviality b).choose
omit [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] in
theorem localAt_mem (b : B) : b ∈ (P.localAt b).base := (P.triviality b).choose_spec

def chartDefining (b : B) : freeAlgebra n :=
  openDefining ((chartAt (Space n) b).target ∩ (chartAt (Space n) b).symm ⁻¹' (P.localAt b).base)
    ((chartAt (Space n) b).isOpen_inter_preimage_symm (P.localAt b).isOpen_base)
def baseChart (b : B) : OpenPartialHomeomorph B (Space n) :=
  restrictChart (chartAt (Space n) b) (P.chartDefining b)
omit [IsManifold (modelWithCorners n) ∞ E] in
theorem baseChart_smooth (b : B) : P.baseChart b ∈ maximalAtlas (modelWithCorners n) ∞ B :=
  restrictChart_smooth _ _ (chart_mem_maximalAtlas b)
omit [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] in
theorem baseChart_source (b x : B) (hx : x ∈ (P.baseChart b).source) : x ∈ (P.localAt b).base := by
  change x ∈ (chartAt (Space n) b).source ∧ _ at hx
  have hq : (chartAt (Space n) b) x ∈ Localization.locus (P.chartDefining b) := hx.2
  rw [chartDefining, openDefining_locus] at hq
  have hs := hq.2
  change (chartAt (Space n) b).symm ((chartAt (Space n) b) x) ∈ (P.localAt b).base at hs
  rw [(chartAt (Space n) b).left_inv hx.1] at hs
  exact hs
omit [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] in
theorem baseChart_mem (b : B) : b ∈ (P.baseChart b).source := by
  refine ⟨mem_chart_source _ b, ?_⟩
  change (chartAt (Space n) b) b ∈ Localization.locus (P.chartDefining b)
  rw [chartDefining, openDefining_locus]
  refine ⟨mem_chart_target _ b, ?_⟩
  change (chartAt (Space n) b).symm ((chartAt (Space n) b) b) ∈ (P.localAt b).base
  rw [(chartAt (Space n) b).left_inv (mem_chart_source _ b)]
  exact P.localAt_mem b

def baseCharts : ChartFamily n B where
  Index := B
  chart := P.baseChart
  smooth := P.baseChart_smooth
  covers b := ⟨b,P.baseChart_mem b⟩

def totalChart (b : B) (g : G) : OpenPartialHomeomorph E (Space n) :=
  ((P.localAt b).sheet g).trans (P.baseChart b)

theorem totalChart_smooth (b : B) (g : G) : P.totalChart b g ∈ maximalAtlas (modelWithCorners n) ∞ E := by
  have hs : ContMDiffOn (modelWithCorners n) (modelWithCorners n) ∞ ((P.localAt b).sheet g)
      ((P.localAt b).sheet g).source :=
    P.smooth_projection.contMDiffOn.congr (fun x hx => (P.localAt b).projection g x hx)
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas (P.baseChart_smooth b)).comp
      (hs.mono (fun _ h => h.1)) (fun _ h => h.2)
  · exact ((P.localAt b).smooth_inverse g).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas (P.baseChart_smooth b)).mono (fun _ h => h.1))
      (fun x hx => (P.localAt b).target g ▸ hx.2)

def totalCharts : ChartFamily n E where
  Index := B × G
  chart bg := P.totalChart bg.1 bg.2
  smooth bg := P.totalChart_smooth bg.1 bg.2
  covers e := by
    obtain ⟨g,hg,_⟩ := (P.localAt (P.projection e)).sheets e (P.localAt_mem (P.projection e))
    refine ⟨(P.projection e,g),hg,?_⟩
    change ((P.localAt (P.projection e)).sheet g) e ∈ (P.baseChart (P.projection e)).source
    rw [(P.localAt (P.projection e)).projection g e hg]
    exact P.baseChart_mem (P.projection e)

end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory ManifoldRealization EuclideanOpen SmoothAlgebra IsManifold
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

omit [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] in
theorem totalChart_target (b : B) (g : G) : (P.totalChart b g).target = (P.baseChart b).target := by
  ext x
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx,?_⟩
    change (P.baseChart b).symm x ∈ ((P.localAt b).sheet g).target
    rw [(P.localAt b).target g]
    exact P.baseChart_source b _ ((P.baseChart b).map_target hx)

def sheetDomainIso (b : B) (g : G) : chartDomain (P.totalChart b g) ≅ chartDomain (P.baseChart b) where
  hom := domainInclusion _ _ (by
    intro x hx
    change x ∈ Points (chartDomain (P.totalChart b g)) at hx
    change x ∈ Points (chartDomain (P.baseChart b))
    rw [chartDomain_locus, P.totalChart_target] at hx
    rw [chartDomain_locus]
    exact hx)
  inv := domainInclusion _ _ (by
    intro x hx
    change x ∈ Points (chartDomain (P.baseChart b)) at hx
    change x ∈ Points (chartDomain (P.totalChart b g))
    rw [chartDomain_locus] at hx
    rw [chartDomain_locus, P.totalChart_target]
    exact hx)
  hom_inv_id := OpenFunctions.Map.ext (fun _ => rfl)
  inv_hom_id := OpenFunctions.Map.ext (fun _ => rfl)

omit [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] in
theorem chart_projection (b : B) (g : G) (x : Points (chartDomain (P.totalChart b g))) :
    P.projection (chartPoint (P.totalChart b g) x) =
      chartPoint (P.baseChart b) ((show Map _ _ from (P.sheetDomainIso b g).hom) x) := by
  have hx : x.val ∈ (P.baseChart b).target := by
    exact (congrArg (fun s : Set (Space n) => x.val ∈ s)
      ((chartDomain_locus (P.totalChart b g)).trans (P.totalChart_target b g))).mp x.property
  exact (P.localAt b).projection_inverse g ((P.baseChart b).symm x.val)
    (P.baseChart_source b _ ((P.baseChart b).map_target hx))

/-- The actual interpretation of the given projection, using derived chart families. -/
def realizedProjection : P.totalCharts.realization ⟶ P.baseCharts.realization :=
  P.totalCharts.interpret P.baseCharts P.projection P.smooth_projection

theorem realizedProjection_naturality :
    (atlasIso P.totalCharts).hom ≫ P.realizedProjection =
      ManifoldRealization.map P.projection P.smooth_projection ≫ (atlasIso P.baseCharts).hom :=
  atlas_naturality P.totalCharts P.baseCharts P.projection P.smooth_projection

def sheet (b : B) (g : G) : embedding.obj (chartDomain (P.baseChart b)) ⟶ P.totalCharts.realization :=
  embedding.map (P.sheetDomainIso b g).inv ≫ P.totalCharts.charts.chart (b,g)

theorem sheet_projection (b : B) (g : G) :
    P.sheet b g ≫ P.realizedProjection = P.baseCharts.charts.chart b := by
  have h := (P.totalCharts.localMap P.baseCharts P.projection P.smooth_projection).test (b,g) b
    _ (𝟙 _) (P.sheetDomainIso b g).hom (P.chart_projection b g)
  simp only [embedding.map_id, Category.id_comp] at h
  change (embedding.map (P.sheetDomainIso b g).inv ≫ P.totalCharts.charts.chart (b,g)) ≫
    P.realizedProjection = _
  dsimp only [totalCharts, baseCharts, realizedProjection, ChartFamily.interpret] at h ⊢
  rw [Category.assoc, h, ← Category.assoc, ← embedding.map_comp,
    (P.sheetDomainIso b g).inv_hom_id, embedding.map_id, Category.id_comp]

end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.ManifoldRealization
open EuclideanOpen IsManifold
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
theorem chartPoint_contMDiff (e : OpenPartialHomeomorph M (Space n))
    (he : e ∈ maximalAtlas (modelWithCorners n) ∞ M) :
    ContMDiff (modelWithCorners n) (modelWithCorners n) ∞ (fun x : ordinaryOpen (chartDomain e) => chartPoint e x) := by
  intro x
  have hx : x.val ∈ e.target := (congrArg (fun s : Set (Space n) => x.val ∈ s)
    (chartDomain_locus e)).mp x.property
  exact (contMDiffAt_symm_of_mem_maximalAtlas he hx).comp x (contMDiff_subtype_val x)
end SquareKit.ManifoldRealization
namespace SquareKit.SmoothPrincipalBundle.Bundle
open ManifoldRealization EuclideanOpen IsManifold
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
def ordinarySheet (b : B) (g : G) (x : ordinaryOpen (chartDomain (P.baseChart b))) : E :=
  ((P.localAt b).sheet g).symm (chartPoint (P.baseChart b) x)
omit [IsManifold (modelWithCorners n) ∞ E] in
theorem ordinarySheet_smooth (b : B) (g : G) :
    ContMDiff (modelWithCorners n) (modelWithCorners n) ∞ (P.ordinarySheet b g) := by
  intro x
  have hx := P.baseChart_source b _ (chartPoint_source (P.baseChart b) x)
  exact (((P.localAt b).smooth_inverse g).contMDiffAt ((P.localAt b).isOpen_base.mem_nhds hx)).comp x
    (chartPoint_contMDiff (P.baseChart b) (P.baseChart_smooth b) x)
omit [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] in
theorem ordinarySheet_projection (b : B) (g : G) (x : ordinaryOpen (chartDomain (P.baseChart b))) :
    P.projection (P.ordinarySheet b g x) = chartPoint (P.baseChart b) x :=
  (P.localAt b).projection_inverse g _
    (P.baseChart_source b _ (chartPoint_source (P.baseChart b) x))
end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothPrincipalBundle.Bundle
open ManifoldRealization EuclideanOpen IsManifold
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (modelWithCorners n) ∞ E] in
theorem overlap_base (i j : B) (x : Points (P.baseCharts.pair i j)) :
    P.projection (P.ordinarySheet j 1 ((show Map _ _ from P.baseCharts.right i j) x)) ∈
      (P.localAt i).base := by
  rw [P.ordinarySheet_projection]
  have h : chartPoint (P.baseChart i) ((show Map _ _ from P.baseCharts.left i j) x) =
      chartPoint (P.baseChart j) ((show Map _ _ from P.baseCharts.right i j) x) :=
    P.baseCharts.agreement i j x
  exact h ▸ P.baseChart_source i _ (chartPoint_source _ _)

def transitionLabel (i j : B) : LocallyConstant (Points (P.baseCharts.pair i j)) G :=
  ⟨fun x => (P.localAt i).label
     (P.ordinarySheet j 1 ((show Map _ _ from P.baseCharts.right i j) x)) (P.overlap_base i j x),
   (IsLocallyConstant.iff_continuous _).mpr ((P.localAt i).continuous_label.comp
     (((P.ordinarySheet_smooth j 1).comp (openMap_contMDiff (P.baseCharts.right i j))).continuous.subtype_mk (P.overlap_base i j)))⟩

omit [IsManifold (modelWithCorners n) ∞ E] in
theorem transitionLabel_action (i j : B) (x : Points (P.baseCharts.pair i j)) :
    P.transitionLabel i j x • P.ordinarySheet i 1 ((show Map _ _ from P.baseCharts.left i j) x) =
      P.ordinarySheet j 1 ((show Map _ _ from P.baseCharts.right i j) x) := by
  let e := P.ordinarySheet j 1 ((show Map _ _ from P.baseCharts.right i j) x)
  have hb := P.baseChart_source i _ (chartPoint_source (P.baseChart i)
    ((show Map _ _ from P.baseCharts.left i j) x))
  change _ • ((P.localAt i).sheet 1).symm _ = _
  rw [← (P.localAt i).equivariant _ 1 _ hb, mul_one]
  have hp : P.projection e = chartPoint (P.baseChart i) ((show Map _ _ from P.baseCharts.left i j) x) :=
    (P.ordinarySheet_projection j 1 _).trans (P.baseCharts.agreement i j x).symm
  rw [← hp]
  exact (P.localAt i).inverse_projection _ e ((P.localAt i).label_source e (P.overlap_base i j x))
end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.ManifoldRealization.ChartFamily
open CategoryTheory EuclideanOpen SmoothManifoldAction
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
  [IsManifold (modelWithCorners n) ∞ M]
variable (A : ChartFamily n M)

/-- The ordinary chart parameterization is the actual chart arrow after the
explicit preferred-atlas comparison. -/
theorem chart_hat (i : A.Index) :
    hat (fun x : ordinaryOpen (chartDomain (A.chart i)) => chartPoint (A.chart i) x)
      (chartPoint_contMDiff (A.chart i) (A.smooth i)) =
      A.charts.chart i ≫ (atlasIso A).inv := by
  apply SmoothManifoldAction.hom_ext
  intro x
  apply pointEquiv.injective
  rw [hat_eval]
  have h := A.charts.realMap_chart (ChartFamily.preferred (n := n) (M := M)).charts
    A.atlas.covers (ChartFamily.preferred (n := n) (M := M)).atlas.covers (atlasIso A).inv i x
  have hi := congrFun (A.reconstruct_interpret (ChartFamily.preferred (n := n) (M := M)) id contMDiff_id)
    (chartPoint (A.chart i) x)
  exact hi.symm.trans h
end SquareKit.ManifoldRealization.ChartFamily
