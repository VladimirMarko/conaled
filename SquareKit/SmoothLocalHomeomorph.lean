import SquareKit.SmoothManifoldModel

/-! Smooth structures induced by local projection sheets over a manifold. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothLocalHomeomorph
open ManifoldRealization Set Topology
open scoped Manifold ContDiff
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- Local homeomorphisms covering the total space whose forward maps are a fixed
projection. No separation or nonemptiness assumption on the total space is needed. -/
structure ProjectionSheets (p : E → B) where
  sheet : E → OpenPartialHomeomorph E B
  mem_source : ∀ x, x ∈ (sheet x).source
  projection : ∀ x, ⇑(sheet x) = p

namespace ProjectionSheets
variable {n : ℕ} [ChartedSpace (Space n) B] {p : E → B} (S : ProjectionSheets p)

def chart (z : E) : OpenPartialHomeomorph E (Space n) :=
  (S.sheet z).trans (chartAt (Space n) (p z))

@[instance_reducible]
def chartedSpace : ChartedSpace (Space n) E where
  atlas := Set.range (chart (n := n) S)
  chartAt := chart (n := n) S
  mem_chart_source z := by
    refine ⟨S.mem_source z, ?_⟩
    change S.sheet z z ∈ (chartAt (Space n) (p z)).source
    rw [S.projection]
    exact mem_chart_source _ _
  chart_mem_atlas z := ⟨z, rfl⟩

theorem proj_chart_symm (z : E) {x : Space n}
    (hx : x ∈ (chart (n := n) S z).target) :
    p ((chart (n := n) S z).symm x) = (chartAt (Space n) (p z)).symm x := by
  change p ((S.sheet z).symm ((chartAt (Space n) (p z)).symm x)) = _
  simpa only [S.projection] using (S.sheet z).right_inv hx.2

theorem chart_transition (z w : E) {x : Space n}
    (hx : x ∈ ((chart (n := n) S z).symm.trans (chart (n := n) S w)).source) :
    ((chart (n := n) S z).symm.trans (chart (n := n) S w)) x =
      ((chartAt (Space n) (p z)).symm.trans (chartAt (Space n) (p w))) x := by
  change (chartAt (Space n) (p w)) (S.sheet w ((chart (n := n) S z).symm x)) = _
  rw [S.projection]
  rw [proj_chart_symm (n := n) S z hx.1]
  rfl

theorem chart_transition_source (z w : E) :
    ((chart (n := n) S z).symm.trans (chart (n := n) S w)).source ⊆
      ((chartAt (Space n) (p z)).symm.trans (chartAt (Space n) (p w))).source := by
  intro x hx
  refine ⟨hx.1.1, ?_⟩
  have h := hx.2.2
  change S.sheet w ((chart (n := n) S z).symm x) ∈ (chartAt (Space n) (p w)).source at h
  rw [S.projection] at h
  rwa [proj_chart_symm (n := n) S z hx.1] at h

theorem isManifold [IsManifold (modelWithCorners n) ∞ B] :
    letI := chartedSpace (n := n) S
    IsManifold (modelWithCorners n) ∞ E := by
  let := chartedSpace (n := n) S
  apply isManifold_of_contDiffOn (modelWithCorners n) ∞ E
  rintro e e' ⟨z, rfl⟩ ⟨w, rfl⟩
  have h := contMDiffOn_of_mem_contDiffGroupoid
    ((contDiffGroupoid ∞ (modelWithCorners n)).compatible
      (chart_mem_atlas (Space n) (p z)) (chart_mem_atlas (Space n) (p w)))
  have hd := h.contDiffOn.mono (chart_transition_source (n := n) S z w)
  simpa only [modelWithCorners, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using
    hd.congr (fun x hx => chart_transition (n := n) S z w hx)

theorem smooth_of_proj_at [IsManifold (modelWithCorners n) ∞ B] {k : ℕ} {N : Type}
    [TopologicalSpace N] [ChartedSpace (Space k) N]
    (h : N → E) (x : N) (hc : ContinuousAt h x)
    (hs : ContMDiffAt (modelWithCorners k) (modelWithCorners n) ∞ (p ∘ h) x) :
    letI := chartedSpace (n := n) S
    ContMDiffAt (modelWithCorners k) (modelWithCorners n) ∞ h x := by
  let := chartedSpace (n := n) S
  apply contMDiffAt_iff_target.mpr
  refine ⟨hc, ?_⟩
  change ContMDiffAt (modelWithCorners k) (modelWithCorners n) ∞
    ((chartAt (Space n) (p (h x))) ∘ (S.sheet (h x) ∘ h)) x
  rw [S.projection]
  exact (contMDiffOn_chart (I := modelWithCorners n) (x := p (h x))).contMDiffAt
    ((chartAt (Space n) (p (h x))).open_source.mem_nhds
      (mem_chart_source _ _)) |>.comp x hs

theorem smooth_of_proj [IsManifold (modelWithCorners n) ∞ B] {k : ℕ} {N : Type}
    [TopologicalSpace N] [ChartedSpace (Space k) N]
    (h : N → E) (hc : Continuous h)
    (hs : ContMDiff (modelWithCorners k) (modelWithCorners n) ∞ (p ∘ h)) :
    letI := chartedSpace (n := n) S
    ContMDiff (modelWithCorners k) (modelWithCorners n) ∞ h :=
  fun x => smooth_of_proj_at S h x hc.continuousAt (hs x)

theorem smooth_proj [IsManifold (modelWithCorners n) ∞ B] :
    letI := chartedSpace (n := n) S
    ContMDiff (modelWithCorners n) (modelWithCorners n) ∞ p := by
  let := chartedSpace (n := n) S
  intro z
  apply contMDiffAt_iff_source.mpr
  have hb := (contMDiffOn_chart_symm (I := modelWithCorners n) (n := ∞) (x := p z)).contMDiffAt
    ((chartAt (Space n) (p z)).open_target.mem_nhds (mem_chart_target _ _))
  have he : (p ∘ (chart (n := n) S z).symm) =ᶠ[
      nhds ((chart (n := n) S z) z)] (chartAt (Space n) (p z)).symm :=
    Filter.eventually_of_mem ((chart (n := n) S z).open_target.mem_nhds
      ((chart (n := n) S z).map_source (mem_chart_source (Space n) z)))
      (fun _ hx => proj_chart_symm (n := n) S z hx)
  have hz : (chart (n := n) S z) z = (chartAt (Space n) (p z)) (p z) := by
    change (chartAt (Space n) (p z)) (S.sheet z z) = _
    rw [S.projection]
  rw [hz] at he
  change ContMDiffWithinAt (modelWithCorners n) (modelWithCorners n) ∞
    (p ∘ (chart (n := n) S z).symm) _ ((chart (n := n) S z) z)
  rw [hz]
  exact (hb.congr_of_eventuallyEq he).contMDiffWithinAt

theorem smooth_iff_proj [IsManifold (modelWithCorners n) ∞ B] {k : ℕ} {N : Type}
    [TopologicalSpace N] [ChartedSpace (Space k) N] (h : N → E) :
    letI := chartedSpace (n := n) S
    ContMDiff (modelWithCorners k) (modelWithCorners n) ∞ h ↔
      Continuous h ∧ ContMDiff (modelWithCorners k) (modelWithCorners n) ∞ (p ∘ h) := by
  let := chartedSpace (n := n) S
  exact ⟨fun hs => ⟨hs.continuous, (smooth_proj S).comp hs⟩,
    fun hs => smooth_of_proj S h hs.1 hs.2⟩

end ProjectionSheets
end SquareKit.SmoothLocalHomeomorph
