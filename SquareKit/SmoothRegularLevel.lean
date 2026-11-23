import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Smooth regular-level normal forms derived from finite-real derivative surjectivity. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff
namespace SquareKit.SmoothRegularLevel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shrink a local inverse to an open region where both directions are smooth. -/
theorem exists_smooth_restriction [CompleteSpace E] (e : OpenPartialHomeomorph E F)
    {U : Set E} (hU : IsOpen U) {a : E} (haU : a ∈ U)
    (he : ContDiffOn ℝ ∞ e U) (hi : (fderiv ℝ e a).IsInvertible) :
    ∃ (V : Set E) (hV : IsOpen V), a ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ (e.restrOpen V hV).symm (e.restrOpen V hV).target := by
  have hc := (he a haU).contDiffAt (hU.mem_nhds haU)
  have hn : {x | (fderiv ℝ e x).IsInvertible} ∈ 𝓝 a :=
    (hc.continuousAt_fderiv (by simp)).preimage_mem_nhds hi.eventually_nhds
  obtain ⟨V, hVsub, hVopen, haV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds haU) hn)
  refine ⟨V, hVopen, haV, fun x hx => (hVsub hx).1, ?_⟩
  intro y hy
  let d := e.restrOpen V hVopen
  have hx : d.symm y ∈ d.source := d.map_target hy
  have hxu : d.symm y ∈ U := (hVsub hx.2).1
  obtain ⟨L, hL⟩ := (hVsub hx.2).2
  have hs : ContDiffAt ℝ ∞ d (d.symm y) :=
    (he _ hxu).contDiffAt (hU.mem_nhds hxu)
  have hd : HasFDerivAt d (L : E →L[ℝ] F) (d.symm y) := by
    rw [hL]
    exact hs.differentiableAt (by simp) |>.hasFDerivAt
  exact (d.contDiffAt_symm hy hd hs).contDiffWithinAt


/-- A regular-level chart, constructed with its actual projection coordinates. -/
structure NormalForm (f : E → F) (L : E →L[ℝ] F) (a : E) (U : Set E) where
  projection : E →L[ℝ] L.ker
  projection_ker : ∀ z : L.ker, projection z = z
  chart : OpenPartialHomeomorph E (F × L.ker)
  mem_source : a ∈ chart.source
  source_subset : chart.source ⊆ U
  chart_apply : ∀ x, chart x = (f x, projection (x - a))
  smooth : ContDiffOn ℝ ∞ chart chart.source
  smooth_symm : ContDiffOn ℝ ∞ chart.symm chart.target

/-- Surjective derivative and smoothness on an open neighborhood produce the
normal form; neither a desired chart nor its inverse is supplied. -/
theorem nonempty_normalForm [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {U : Set E} {a : E} {L : E →L[ℝ] F}
    (hU : IsOpen U) (ha : a ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hd : HasFDerivAt f L a) (hL : Function.Surjective L) :
    Nonempty (NormalForm f L a U) := by
  have hk := L.ker_closedComplemented_of_finiteDimensional_range
  have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr hL
  have hs := ((hf a ha).contDiffAt (hU.mem_nhds ha)).hasStrictFDerivAt' hd (by simp)
  let φ := hs.implicitFunctionDataOfComplemented f L hr hk
  let e := φ.toOpenPartialHomeomorph
  have he : ContDiffOn ℝ ∞ e U := by
    change ContDiffOn ℝ ∞ (fun x => (f x, Classical.choose hk (x - a))) U
    exact hf.prodMk ((Classical.choose hk).contDiff.comp_contDiffOn
      (contDiff_id.sub contDiff_const).contDiffOn)
  obtain ⟨V, hV, haV, hVU, hInv⟩ := exists_smooth_restriction e hU ha he
    φ.isInvertible_fderiv_prodFun
  refine ⟨⟨Classical.choose hk, Classical.choose_spec hk, e.restrOpen V hV,
    ⟨φ.pt_mem_toOpenPartialHomeomorph_source, haV⟩,
    fun x hx => hVU hx.2, fun x => rfl, ?_, hInv⟩⟩
  exact he.mono (fun x hx => hVU hx.2)

/-- The fderiv formulation of the primitive regularity hypothesis. -/
theorem nonempty_normalForm_fderiv [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {U : Set E} {a : E}
    (hU : IsOpen U) (ha : a ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hL : Function.Surjective (fderiv ℝ f a)) :
    Nonempty (NormalForm f (fderiv ℝ f a) a U) :=
  nonempty_normalForm hU ha hf
    (((hf a ha).contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt hL

namespace NormalForm
variable {f : E → F} {L : E →L[ℝ] F} {a : E} {U : Set E}
  (N : NormalForm f L a U)

/-- The derivative and the very same free-coordinate projection split the source. -/
def linearCoordinates [CompleteSpace E] [CompleteSpace F]
    (hL : Function.Surjective L) : E ≃L[ℝ] (F × L.ker) :=
  L.equivProdOfSurjectiveOfIsCompl N.projection (LinearMap.range_eq_top.mpr hL)
    (LinearMap.range_eq_of_proj N.projection_ker)
    (LinearMap.isCompl_of_proj N.projection_ker)

@[simp] theorem linearCoordinates_apply [CompleteSpace E] [CompleteSpace F]
    (hL : Function.Surjective L) (x : E) :
    N.linearCoordinates hL x = (L x, N.projection x) := rfl

@[simp] theorem chart_center : N.chart a = (f a, 0) := by simp [N.chart_apply]

theorem center_mem_target : (f a, 0) ∈ N.chart.target :=
  N.chart_center ▸ N.chart.map_source N.mem_source

@[simp] theorem inverse_center : N.chart.symm (f a, 0) = a := by
  rw [← N.chart_center]
  exact N.chart.left_inv N.mem_source

theorem inverse_coordinates {y : F × L.ker} (hy : y ∈ N.chart.target) :
    (f (N.chart.symm y), N.projection (N.chart.symm y - a)) = y :=
  (N.chart_apply _).symm.trans (N.chart.right_inv hy)

theorem inverse_first {y : F × L.ker} (hy : y ∈ N.chart.target) :
    f (N.chart.symm y) = y.1 := congrArg Prod.fst (N.inverse_coordinates hy)

theorem inverse_second {y : F × L.ker} (hy : y ∈ N.chart.target) :
    N.projection (N.chart.symm y - a) = y.2 :=
  congrArg Prod.snd (N.inverse_coordinates hy)

theorem inverse_unique {x : E} (hx : x ∈ N.chart.source) {y : F × L.ker}
    (h : (f x, N.projection (x - a)) = y) : N.chart.symm y = x := by
  rw [← h, ← N.chart_apply]
  exact N.chart.left_inv hx

/-- The actual open parameter domain of the level through the center. -/
def levelDomain : Set L.ker := {z | (f a, z) ∈ N.chart.target}

theorem isOpen_levelDomain : IsOpen N.levelDomain :=
  N.chart.open_target.preimage (continuous_const.prodMk continuous_id)

@[simp] theorem zero_mem_levelDomain : 0 ∈ N.levelDomain := N.center_mem_target

/-- Smooth parameterization of the local regular level. -/
def parameterize (z : L.ker) : E := N.chart.symm (f a, z)

theorem smooth_parameterize : ContDiffOn ℝ ∞ N.parameterize N.levelDomain :=
  N.smooth_symm.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)

@[simp] theorem parameterize_zero : N.parameterize 0 = a := N.inverse_center

theorem parameterize_mem_source {z : L.ker} (hz : z ∈ N.levelDomain) :
    N.parameterize z ∈ N.chart.source := N.chart.map_target hz

theorem parameterize_level {z : L.ker} (hz : z ∈ N.levelDomain) :
    f (N.parameterize z) = f a := N.inverse_first hz

theorem parameterize_coordinate {z : L.ker} (hz : z ∈ N.levelDomain) :
    N.projection (N.parameterize z - a) = z := N.inverse_second hz

theorem coordinate_mem_levelDomain {x : E} (hx : x ∈ N.chart.source) (hfx : f x = f a) :
    N.projection (x - a) ∈ N.levelDomain := by
  have h := N.chart.map_source hx
  simpa [levelDomain, N.chart_apply, hfx] using h

theorem parameterize_recovery {x : E} (hx : x ∈ N.chart.source) (hfx : f x = f a) :
    N.parameterize (N.projection (x - a)) = x :=
  N.inverse_unique hx (by rw [hfx])

/-- The regular level has its actual subspace topology, recovered by the free coordinates. -/
def levelHomeomorph : {x : E // x ∈ N.chart.source ∧ f x = f a} ≃ₜ
    {z : L.ker // z ∈ N.levelDomain} where
  toFun x := ⟨N.projection (x.val - a), N.coordinate_mem_levelDomain x.property.1 x.property.2⟩
  invFun z := ⟨N.parameterize z.val,
    N.parameterize_mem_source z.property, N.parameterize_level z.property⟩
  left_inv x := Subtype.ext (N.parameterize_recovery x.property.1 x.property.2)
  right_inv z := Subtype.ext (N.parameterize_coordinate z.property)
  continuous_toFun :=
    (N.projection.continuous.comp (continuous_subtype_val.sub continuous_const)).subtype_mk _
  continuous_invFun := N.smooth_parameterize.continuousOn.domRestrict.subtype_mk _

/-- Smoothness of a local level-valued lift is exactly smoothness of its free
coordinates. Continuity keeps the lift inside the constructed chart. -/
theorem smooth_lift_iff {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : H → E} {x : H} (hc : ContinuousAt k x) (hx : k x ∈ N.chart.source)
    (hlevel : ∀ᶠ y in 𝓝 x, f (k y) = f a) :
    ContDiffAt ℝ ∞ k x ↔ ContDiffAt ℝ ∞ (fun y => N.projection (k y - a)) x := by
  constructor
  · intro hk
    exact N.projection.contDiff.contDiffAt.comp x (hk.sub contDiffAt_const)
  · intro hk
    have he : f (k x) = f a := hlevel.self_of_nhds
    have hz := N.coordinate_mem_levelDomain hx he
    have hp := (N.smooth_parameterize _ hz).contDiffAt (N.isOpen_levelDomain.mem_nhds hz)
    apply (hp.comp x hk).congr_of_eventuallyEq
    filter_upwards [hc.preimage_mem_nhds (N.chart.open_source.mem_nhds hx), hlevel] with y hy hfy
    exact (N.parameterize_recovery hy hfy).symm

end NormalForm

/-- Rank-nullity for the actual kernel used in the normal form. -/
theorem kernel_finrank_add [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (hL : Function.Surjective L) :
    Module.finrank ℝ L.ker + Module.finrank ℝ F = Module.finrank ℝ E := by
  have h := L.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hL, finrank_top] at h
  simpa [add_comm] using h

theorem kernel_finrank [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (hL : Function.Surjective L) :
    Module.finrank ℝ L.ker = Module.finrank ℝ E - Module.finrank ℝ F := by
  have h := kernel_finrank_add L hL
  omega

/-- Finite full-space coordinates on the kernel, including dimension zero. -/
def kernelCoordinates [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (hL : Function.Surjective L) :
    L.ker ≃L[ℝ] (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [Module.finrank_fin_fun, kernel_finrank L hL])

end SquareKit.SmoothRegularLevel
