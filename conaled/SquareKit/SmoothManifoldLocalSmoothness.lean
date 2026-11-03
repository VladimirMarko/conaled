import SquareKit.SmoothManifoldModel

/-! Smoothness recovered from ordinary local coordinate descriptions.
The covers may split a source chart across several target charts. -/
noncomputable section
open CategoryTheory Set Filter IsManifold
open scoped Manifold ContDiff Topology
namespace SquareKit.ManifoldRealization.ChartFamily
open EuclideanOpen SmoothAlgebra
variable {n m : ℕ} {M N : Type}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (Space n) M] [ChartedSpace (Space m) N]
    (A : ChartFamily n M) (B : ChartFamily m N)

/-- A covered local coordinate description implies actual Mathlib smoothness,
without assuming continuity of the underlying function in advance. -/
theorem contMDiff_of_localMap {f : M → N} (l : Charts.LocalMap A.charts B.charts f) :
    ContMDiff (Model n) (Model m) ∞ f := by
  intro x
  obtain ⟨i, hi⟩ := A.covers x
  let e := A.chart i
  have hx : e x ∈ Points (chartDomain e) := by
    rw [chartDomain_locus]
    exact e.map_source hi
  obtain ⟨k, hk⟩ := l.covers i ⟨e x, hx⟩
  let U := subdomain (A.charts.domain i) (l.defining i k)
  let d := B.chart (l.index i k)
  let c : EuclideanOpen.Map U (chartDomain d) := l.coordinate i k
  have hu : e x ∈ Points U := mul_ne_zero hx hk
  have he : ContMDiffAt (Model n) (Model n) ∞ e x :=
    contMDiffAt_of_mem_maximalAtlas (A.smooth i) hi
  have hc := c.smooth_representative.contDiffAt ((domain_open U).mem_nhds hu)
  have hd : c.representative (e x) ∈ d.target := by
    rw [c.representative_mem ⟨e x, hu⟩]
    exact (chartDomain_locus d) ▸ (c ⟨e x, hu⟩).property
  have hs := (contMDiffAt_symm_of_mem_maximalAtlas (B.smooth (l.index i k)) hd).comp x
    (hc.contMDiffAt.comp x he)
  apply hs.congr_of_eventuallyEq
  have hn : ∀ᶠ y in 𝓝 x, e y ∈ Points U :=
    he.continuousAt.preimage_mem_nhds ((domain_open U).mem_nhds hu)
  filter_upwards [hn, e.open_source.mem_nhds hi] with y hy hys
  have h := l.agreement i k ⟨e y, hy⟩
  change f (e.symm (e y)) = d.symm (c ⟨e y, hy⟩).val at h
  simpa only [Function.comp_apply, c.representative_mem ⟨e y, hy⟩, e.left_inv hys] using h

/-- Local coordinate data characterize smooth maps for any two covering smooth
chart families, including manifolds of different finite dimensions. -/
theorem contMDiff_iff_localMap (f : M → N) :
    ContMDiff (Model n) (Model m) ∞ f ↔ Nonempty (Charts.LocalMap A.charts B.charts f) :=
  ⟨fun hf => ⟨A.localMap B f hf⟩, fun ⟨l⟩ => A.contMDiff_of_localMap B l⟩

end SquareKit.ManifoldRealization.ChartFamily
