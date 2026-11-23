import SquareKit.SmoothTransversePullbackSheets
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
noncomputable section
set_option autoImplicit false
open SquareKit.ManifoldRealization SquareKit.SmoothTransversality
open scoped Manifold ContDiff
namespace Examples.SmoothTransversePullback

def parabola (z : Space 2) : Space 1 := fun _ => z 1 - z 0 ^ 2

theorem parabola_smooth : ContMDiff (Model 2) (Model 1) ∞ parabola := by
  apply ContDiff.contMDiff
  unfold parabola
  fun_prop

def parabolaDerivative (z : Space 2) : Space 2 →L[ℝ] Space 1 :=
  ContinuousLinearMap.pi fun _ =>
    ContinuousLinearMap.proj 1 - (2 * z 0) • ContinuousLinearMap.proj 0

theorem parabola_hasFDerivAt (z : Space 2) :
    HasFDerivAt parabola (parabolaDerivative z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  convert (hasFDerivAt_apply (𝕜 := ℝ) 1 z).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 z).pow 2) using 1 <;>
    first | (funext q; rfl) | simp [two_smul, two_mul]

theorem parabola_transverse (z : Space 2) (w : Space 0)
    (h : parabola z = (0 : Space 1)) :
    TransverseAt (m := 2) (n := 0) (p := 1) parabola (fun _ : Space 0 => 0) z w h := by
  intro v
  refine ⟨(fun i => if i = 1 then v 0 else 0, 0), ?_⟩
  simp only [tangentDifference, sub_apply, ContinuousLinearMap.comp_apply,
    mfderiv_const, zero_apply, ContinuousLinearEquiv.coe_coe,
    tangentTransport_apply]
  rw [show Model 2 = 𝓘(ℝ, Space 2) from rfl, show Model 1 = 𝓘(ℝ, Space 1) from rfl,
    mfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  change (fderiv ℝ parabola z) (fun i => if i = 1 then v 0 else 0) - 0 = v
  rw [(parabola_hasFDerivAt z).fderiv]
  ext i
  fin_cases i
  simp [parabolaDerivative]

def axisX : Space 1 →L[ℝ] Space 2 := ContinuousLinearMap.pi fun i =>
  if i = 0 then ContinuousLinearMap.proj 0 else 0

def axisY : Space 1 →L[ℝ] Space 2 := ContinuousLinearMap.pi fun i =>
  if i = 1 then ContinuousLinearMap.proj 0 else 0

theorem axisX_smooth : ContMDiff (Model 1) (Model 2) ∞ axisX :=
  axisX.contDiff.contMDiff

theorem axisY_smooth : ContMDiff (Model 1) (Model 2) ∞ axisY :=
  axisY.contDiff.contMDiff

theorem axes_transverse (x y : Space 1) (h : axisX x = axisY y) :
    TransverseAt (m := 1) (n := 1) (p := 2) axisX axisY x y h := by
  intro v
  refine ⟨(fun _ => v 0, fun _ => -v 1), ?_⟩
  simp only [tangentDifference, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, tangentTransport_apply]
  rw [show Model 1 = 𝓘(ℝ, Space 1) from rfl, show Model 2 = 𝓘(ℝ, Space 2) from rfl,
    mfderiv_eq_fderiv, mfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  change (fderiv ℝ axisX x) (fun _ => v 0) -
    (fderiv ℝ axisY y) (fun _ => -v 1) = v
  rw [axisX.fderiv, axisY.fderiv]
  ext i
  fin_cases i <;> simp [axisX, axisY]

def emptyLeft : Space 0 → Space 2 := fun _ => 0

def emptyRight : Space 1 → Space 2 := fun _ => fun _ => 1

theorem empty_disjoint (x : Space 0) (y : Space 1) : emptyLeft x ≠ emptyRight y := by
  intro h
  have h0 := congrFun h 0
  norm_num [emptyLeft, emptyRight] at h0

theorem empty_transverse (x : Space 0) (y : Space 1) (h : emptyLeft x = emptyRight y) :
    TransverseAt (m := 0) (n := 1) (p := 2) emptyLeft emptyRight x y h :=
  (empty_disjoint x y h).elim

def parabolaCurve (t : Space 1) : Space 2 := fun i => if i = 0 then t 0 else t 0 ^ 2

theorem parabolaCurve_smooth : ContMDiff (Model 1) (Model 2) ∞ parabolaCurve := by
  apply ContDiff.contMDiff
  apply contDiff_pi.mpr
  intro i
  unfold parabolaCurve
  split_ifs <;> fun_prop

theorem parabolaCurve_level (t : Space 1) : parabola (parabolaCurve t) = 0 := by
  ext i
  simp [parabola, parabolaCurve]

theorem axes_eq_zero {x y : Space 1} (h : axisX x = axisY y) : x = 0 ∧ y = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [axisX, axisY] at h0 h1
  constructor
  · ext i
    fin_cases i
    exact h0
  · ext i
    fin_cases i
    exact h1.symm

open SquareKit.SmoothTransversePullback

abbrev ParabolaFiber := Pullback parabola (fun _ : Space 0 => (0 : Space 1))

theorem parabola_transverse_all : Transverse (m := 2) (n := 0) (p := 1)
    parabola (fun _ : Space 0 => (0 : Space 1)) :=
  fun q => parabola_transverse q.val.1 q.val.2 q.property

def parabolaPoint (t : Space 1) : ParabolaFiber :=
  ⟨(parabolaCurve t, 0), parabolaCurve_level t⟩

def parabolaLocal (t : Space 1) :=
  localModel parabola_smooth contMDiff_const parabola_transverse_all (parabolaPoint t)

example (t : Space 1) : parabolaPoint t ∈ (parabolaLocal t).chart.source :=
  (parabolaLocal t).mem_source

example (t : Space 1) {q : ParabolaFiber} (hq : q ∈ (parabolaLocal t).chart.source) :
    (parabolaLocal t).chart.symm ((parabolaLocal t).chart q) = q :=
  (parabolaLocal t).chart.left_inv hq

abbrev AxesFiber := Pullback axisX axisY

def axesPoint : AxesFiber := ⟨(0, 0), by simp⟩

instance : Nonempty AxesFiber := ⟨axesPoint⟩

theorem axes_transverse_all : Transverse (m := 1) (n := 1) (p := 2) axisX axisY :=
  fun q => axes_transverse q.val.1 q.val.2 q.property

instance : Subsingleton AxesFiber := ⟨by
  intro q r
  apply Subtype.ext
  have hq := axes_eq_zero q.property
  have hr := axes_eq_zero r.property
  exact Prod.ext (hq.1.trans hr.1.symm) (hq.2.trans hr.2.symm)⟩

abbrev EmptyFiber := Pullback emptyLeft emptyRight

instance : IsEmpty EmptyFiber := ⟨fun q => empty_disjoint q.val.1 q.val.2 q.property⟩

theorem empty_transverse_all : Transverse (m := 0) (n := 1) (p := 2) emptyLeft emptyRight :=
  fun q => empty_transverse q.val.1 q.val.2 q.property

example : ¬ (2 ≤ 0 + 1) := by omega

local instance parabolaCharted : ChartedSpace (Space 1) ParabolaFiber :=
  chartedSpace parabola_smooth contMDiff_const parabola_transverse_all

local instance parabolaManifold : IsManifold (Model 1) ∞ ParabolaFiber :=
  isManifold parabola_smooth contMDiff_const parabola_transverse_all

example : T2Space ParabolaFiber := t2Space

example : SecondCountableTopology ParabolaFiber := secondCountableTopology

theorem parabolaPoint_smooth : ContMDiff (Model 1) (Model 1) ∞ parabolaPoint :=
  smooth_lift parabola_smooth contMDiff_const parabola_transverse_all
    parabolaCurve (fun _ => 0) parabolaCurve_level parabolaCurve_smooth contMDiff_const

example (t : Space 1) : fst (parabolaPoint t) 0 = t 0 := by
  simp [fst, parabolaPoint, parabolaCurve]

example {k : ℕ} (h : Space k → ParabolaFiber) :
    ContMDiff (Model k) (Model 1) ∞ h ↔
      ContMDiff (Model k) (Model 2) ∞ (fst ∘ h) ∧
      ContMDiff (Model k) (Model 0) ∞ (snd ∘ h) :=
  smooth_iff_components parabola_smooth contMDiff_const parabola_transverse_all h

local instance axesCharted : ChartedSpace (Space 0) AxesFiber :=
  chartedSpace axisX_smooth axisY_smooth axes_transverse_all

local instance axesManifold : IsManifold (Model 0) ∞ AxesFiber :=
  isManifold axisX_smooth axisY_smooth axes_transverse_all

example : ContMDiff (Model 0) (Model 1) ∞ (fst : AxesFiber → Space 1) :=
  smooth_fst axisX_smooth axisY_smooth axes_transverse_all

example : ContMDiff (Model 0) (Model 1) ∞ (snd : AxesFiber → Space 1) :=
  smooth_snd axisX_smooth axisY_smooth axes_transverse_all

local instance emptyCharted : ChartedSpace (Space 0) EmptyFiber :=
  chartedSpace contMDiff_const contMDiff_const empty_transverse_all

local instance emptyManifold : IsManifold (Model 0) ∞ EmptyFiber :=
  isManifold contMDiff_const contMDiff_const empty_transverse_all

example : ContMDiff (Model 0) (Model 0) ∞ (fst : EmptyFiber → Space 0) :=
  smooth_fst contMDiff_const contMDiff_const empty_transverse_all

example : ContMDiff (Model 0) (Model 1) ∞ (snd : EmptyFiber → Space 1) :=
  smooth_snd contMDiff_const contMDiff_const empty_transverse_all

/-- Base change of the identity on a line along the nonlinear plane map uses
both atlas constructions with their different source/target dimensions. -/
example {k : ℕ} (h : Space k → Pullback (id : Space 1 → Space 1) parabola) :
    (letI := chartedSpace contMDiff_id parabola_smooth (identity_transverse parabola);
      ContMDiff (Model k) (Model 2) ∞ h) ↔
    (letI := (identitySheets parabola parabola_smooth.continuous).chartedSpace (n := 2);
      ContMDiff (Model k) (Model 2) ∞ h) :=
  identity_atlas_comparison parabola parabola_smooth h

end Examples.SmoothTransversePullback
