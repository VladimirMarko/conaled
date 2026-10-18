/-
Adapted from CatDG/Diffeology/Manifolds.lean, lean-catdg revision
1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4, by peabrainiac.
Released under Apache 2.0 license; see https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/LICENSE.
-/
import Applications.Diffeology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section
open Set Diffeology
open scoped Manifold ContDiff Topology

open OpenPartialHomeomorph in
/-- The diffeology defined by a manifold structure on M, with the plots given by the maps
that are smooth in the sense of mathlib's `ContMDiff`-API.
This can not be an instance because `IsManifold I M` depends on `I` while
`DiffeologicalSpace M` does not, and because it would probably lead to instance diamonds on
things like products even if some workaround was found. -/
@[instance_reducible]
def IsManifold.toDiffeology {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    DiffeologicalSpace M :=
  DiffeologicalSpace.ofCorePlotsOn {
    isPlotOn := fun {n u} _ p ↦ ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I ∞ p u
    isPlotOn_congr := fun _ _ _ h ↦ contMDiffOn_congr h
    isPlot := fun {n} p ↦ ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I ∞ p
    isPlotOn_univ := contMDiffOn_univ
    isPlot_const := fun _ ↦ contMDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf ↦ hp.comp hf.contMDiffOn h.subset_preimage
    locality := fun _ _ h ↦ fun x hxu ↦ by
      let ⟨v,hv,hxv,hv'⟩ := h x hxu
      exact ((hv' x hxv).contMDiffAt (hv.mem_nhds hxv)).contMDiffWithinAt
  }

/-- The plots of a manifold are by definition precisely the smooth maps. -/
lemma isPlot_iff_contMDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M} : @IsPlot _ (IsManifold.toDiffeology I M) _ p ↔ ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I ∞ p := Iff.rfl

lemma IsManifold.toDiffeology_eq_normedSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    IsManifold.toDiffeology 𝓘(ℝ, E) E = NormedSpace.toDiffeology E := by
  ext n p; exact contMDiff_iff_contDiff

/-- Every smooth map between manifolds is also D-smooth, i.e. this construction defines a
functor of concrete categories. -/
theorem ContMDiff.dsmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    {f : M → N} (hf : ContMDiff I I' ∞ f) : @DSmooth M N (IsManifold.toDiffeology I M) (IsManifold.toDiffeology I' N) f :=
  fun _ _ ↦ hf.comp

open OpenPartialHomeomorph in
/-- Local smooth parameters with a smooth section, for a finite-dimensional
boundaryless source. The section also detects the ordinary topology. -/
theorem IsManifold.exists_plot_section {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] (x : M) :
    ∃ (n : ℕ) (p : EuclideanSpace ℝ (Fin n) → M)
      (q : M → EuclideanSpace ℝ (Fin n)) (s : Set M),
      IsOpen s ∧ x ∈ s ∧ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p ∧
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ q s ∧
      ∀ y ∈ s, p (q y) = y := by
  let x' := toEuclidean (extChartAt I x x); let n := Module.finrank ℝ E
  have ⟨ε, hε, hε'⟩ := (Metric.mem_nhds_iff (x := x')).1 <| toEuclidean.isOpenMap.image_mem_nhds <|
    mem_interior_iff_mem_nhds.1 <| I.isInteriorPoint_iff.1 <|
    BoundarylessManifold.isInteriorPoint (x := x)
  let e := (extChartAt I x).symm ∘ toEuclidean.symm ∘
    (univUnitBall.trans' (unitBallBall x' ε hε) rfl)
  have he : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I ∞ e := (contMDiffOn_extChartAt_symm x).comp_contMDiff
    (toEuclidean.symm.contDiff.comp <| (contDiff_unitBallBall hε).comp
    contDiff_univUnitBall).contMDiff fun x'' ↦ (mem_image_equiv (f := toEuclidean.toEquiv)).1 <|
    hε' <| (univUnitBall.trans' (unitBallBall x' ε hε) rfl).map_source <| mem_univ _
  let e' := (univUnitBall.trans' (unitBallBall x' ε hε) rfl).symm ∘ toEuclidean ∘ extChartAt I x
  have he' : ContMDiffOn I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ e' _ :=
    (contDiffOn_univUnitBall_symm.comp (contDiff_unitBallBall_symm hε).contDiffOn fun _ hx'' ↦
        mem_preimage.2 ((unitBallBall x' ε hε).symm.map_source hx'')).contMDiffOn.comp
      (toEuclidean.contDiff.contMDiff.comp_contMDiffOn <| contMDiffOn_extChartAt.mono <|
        inter_subset_right) inter_subset_left
  refine ⟨n, e, e', (toEuclidean ∘ extChartAt I x) ⁻¹' Metric.ball x' ε ∩ (chartAt H x).source, ?_, ⟨Metric.mem_ball_self hε, mem_chart_source H x⟩,
    he, he', ?_⟩
  · exact inter_comm _ _ ▸ extChartAt_source I x ▸ ContinuousOn.isOpen_inter_preimage
      (toEuclidean.continuous.comp_continuousOn (continuousOn_extChartAt x))
      (isOpen_extChartAt_source x) Metric.isOpen_ball
  · intro y hy
    simp_rw [e, e', Function.comp_apply]
    rw [(univUnitBall.trans' (unitBallBall x' ε hε) rfl).right_inv (by exact hy.1),
      toEuclidean.symm_apply_apply, (extChartAt I x).left_inv (extChartAt_source I x ▸ hy.2)]

/-- Every D-smooth map from a boundaryless manifold to another manifold is also smooth.
-/
theorem DSmooth.manifold_contMDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [hI : BoundarylessManifold I M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    {f : M → N} (hf : @DSmooth M N (IsManifold.toDiffeology I M) (IsManifold.toDiffeology I' N) f) : ContMDiff I I' ∞ f := by
  intro x
  obtain ⟨n, p, q, s, hs, hx, hp, hq, he⟩ := IsManifold.exists_plot_section I M x
  exact (((hf n p hp).comp_contMDiffOn hq).congr
    (fun y hy => congrArg f (he y hy).symm) x hx).contMDiffAt (hs.mem_nhds hx)

/-- Maps between boundaryless manifolds are smooth iff they are diffeologically smooth. -/
theorem contMDiff_iff_dsmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [hI : BoundarylessManifold I M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    {f : M → N} : ContMDiff I I' ∞ f ↔ @DSmooth M N (IsManifold.toDiffeology I M) (IsManifold.toDiffeology I' N) f :=
  ⟨ContMDiff.dsmooth, DSmooth.manifold_contMDiff⟩

/-- On finite-dimensional boundaryless manifolds, the D-topology is the given topology. -/
theorem IsManifold.dTopology_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type*) [t : TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] :
    @DiffeologicalSpace.dTopology M (IsManifold.toDiffeology I M) = t := by
  let := IsManifold.toDiffeology I M
  apply TopologicalSpace.ext
  funext u
  apply propext
  change (∀ (n : ℕ) (p : EuclideanSpace ℝ (Fin n) → M),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p → IsOpen (p ⁻¹' u)) ↔ IsOpen u
  constructor
  · intro hu
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨n, p, q, s, hs, hxs, hp, hq, he⟩ := IsManifold.exists_plot_section I M x
    have hpre := hu n p hp
    have hcont := (hq.continuousOn x hxs).continuousAt (hs.mem_nhds hxs)
    have hn := hcont (hpre.mem_nhds (show q x ∈ p ⁻¹' u by simpa [he x hxs]))
    exact Filter.mem_of_superset (Filter.inter_mem (hs.mem_nhds hxs) hn)
      (fun y hy => by simpa [he y hy.1] using hy.2)
  · intro hu n p hp
    exact hu.preimage hp.continuous

/-- Restricting the manifold to an open subset gives its induced diffeology. -/
theorem IsManifold.open_toDiffeology {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (U : TopologicalSpace.Opens M) :
    IsManifold.toDiffeology I U =
      DiffeologicalSpace.induced (Subtype.val : U → M) (IsManifold.toDiffeology I M) := by
  ext n p
  exact (ContMDiff.subtypeVal_comp_iff U p).symm
