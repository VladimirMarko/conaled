import SquareKit.SmoothRegularLevel
import SquareKit.SmoothTransversality
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! Regular-level charts from actual derivative calculations. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology ContDiff
namespace Examples.SmoothRegularLevel
open SquareKit.SmoothRegularLevel

def parabola (z : ℝ × ℝ) : ℝ := z.2 - z.1 ^ 2

theorem parabola_smooth : ContDiff ℝ ∞ parabola := by
  unfold parabola
  fun_prop

theorem parabola_derivative : HasFDerivAt parabola
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := by
  convert (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0, 0) : ℝ × ℝ))).sub
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := ((0, 0) : ℝ × ℝ))).pow 2) using 1 <;> first | rfl | simp

theorem snd_surjective : Function.Surjective (ContinuousLinearMap.snd ℝ ℝ ℝ) :=
  fun y => ⟨(0, y), rfl⟩

def parabolaNormal : NormalForm parabola (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) univ :=
  Classical.choice (nonempty_normalForm isOpen_univ (mem_univ _) parabola_smooth.contDiffOn
    parabola_derivative snd_surjective)

example : Module.finrank ℝ (ContinuousLinearMap.snd ℝ ℝ ℝ).ker = 1 := by
  simpa using kernel_finrank (ContinuousLinearMap.snd ℝ ℝ ℝ) snd_surjective

example {t : (ContinuousLinearMap.snd ℝ ℝ ℝ).ker} (ht : t ∈ parabolaNormal.levelDomain) :
    (parabolaNormal.parameterize t).2 = (parabolaNormal.parameterize t).1 ^ 2 := by
  have h := parabolaNormal.parameterize_level ht
  simpa [parabola, sub_eq_zero] using h

example : ContDiffOn ℝ ∞ parabolaNormal.parameterize parabolaNormal.levelDomain :=
  parabolaNormal.smooth_parameterize

example {z : ℝ × ℝ} (hz : z ∈ parabolaNormal.chart.source) (h : z.2 = z.1 ^ 2) :
    parabolaNormal.parameterize (parabolaNormal.projection z) = z := by
  simpa only [show (0, 0) = (0 : ℝ × ℝ) from rfl, sub_zero] using parabolaNormal.parameterize_recovery hz (by simp [parabola, h])

def projectionNormal : NormalForm (Prod.fst : ℝ × ℝ → ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 0) univ :=
  Classical.choice (nonempty_normalForm isOpen_univ (mem_univ _) contDiff_fst.contDiffOn
    (hasFDerivAt_fst (p := ((0, 0) : ℝ × ℝ))) (fun y => ⟨(y, 0), rfl⟩))

example : projectionNormal.chart (0, 0) = (0, 0) := projectionNormal.chart_center

def pointNormal : NormalForm (id : ℝ → ℝ) (ContinuousLinearMap.id ℝ ℝ) 0 univ :=
  Classical.choice (nonempty_normalForm isOpen_univ (mem_univ _) contDiff_id.contDiffOn
    (hasFDerivAt_id 0) Function.surjective_id)

example : Module.finrank ℝ (ContinuousLinearMap.id ℝ ℝ).ker = 0 := by
  simpa using kernel_finrank (ContinuousLinearMap.id ℝ ℝ) Function.surjective_id

example {t : (ContinuousLinearMap.id ℝ ℝ).ker} (ht : t ∈ pointNormal.levelDomain) :
    pointNormal.parameterize t = 0 := pointNormal.parameterize_level ht

/-- The square map at zero fails the primitive regularity hypothesis. This
makes no claim about all nonregular fibers or their sheaf interpretations. -/
theorem square_not_regular : ¬ Function.Surjective (fderiv ℝ (fun x : ℝ => x ^ 2) 0) := by
  have hd : HasFDerivAt (fun x : ℝ => x ^ 2) (0 : ℝ →L[ℝ] ℝ) 0 := by
    convert (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).pow 2 using 1 <;> simp
  rw [hd.fderiv]
  intro h
  obtain ⟨x, hx⟩ := h 1
  norm_num at hx


section ManifoldBridge
open SquareKit.ManifoldRealization SquareKit.SmoothTransversality
open scoped Manifold

/-- The identity and a point meet transversely, using the actual manifold derivative. -/
theorem point_transverse : TransverseAt (m := 1) (n := 0) (p := 1)
    (id : Space 1 → Space 1) (fun _ : Space 0 => (0 : Space 1)) 0 0 rfl := by
  intro z
  refine ⟨(z, 0), ?_⟩
  simp [tangentDifference, mfderiv_id, mfderiv_const]

/-- This exercises the entire tangent-to-chart-to-smooth-inverse construction. -/
def pointCoordinateNormal := Classical.choice (nonempty_coordinateNormalForm
  (m := 1) (n := 0) (p := 1)
  (f := (id : Space 1 → Space 1)) (g := fun _ : Space 0 => (0 : Space 1))
  contMDiff_id contMDiff_const (x := 0) (y := 0) rfl point_transverse)

example : ContDiffOn ℝ ∞ pointCoordinateNormal.chart.symm
    pointCoordinateNormal.chart.target := pointCoordinateNormal.smooth_symm

example : pointCoordinateNormal.chart.symm
    (0, 0) = coordinateCenter (m := 1) (n := 0) (0 : Space 1) (0 : Space 0) := by
  have h := pointCoordinateNormal.inverse_center
  rw [coordinateDifference_center (m := 1) (n := 0) (p := 1)
    (f := (id : Space 1 → Space 1)) (g := fun _ : Space 0 => (0 : Space 1))
    (x := 0) (y := 0) rfl] at h
  exact h

end ManifoldBridge
end Examples.SmoothRegularLevel
