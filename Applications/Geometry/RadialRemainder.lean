import Applications.Geometry.RadialExponential
import Mathlib.Analysis.Asymptotics.Prod
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.Normed.Operator.Asymptotics

/-! Remainder estimates from the exact selected-path integral equation. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RadialMetric.Variation
open Set Metric Asymptotics
open scoped Topology

def pathCubic (α : Paths) : Curve := conjugate α.1 * α.2 * α.2

def cubicLift : Curve →L[ℝ] Paths :=
  ((-(1/2 : ℝ)) • integralCLM.comp integralCLM).prod (-integralCLM)

theorem solutionPaths_fixed : ∀ᶠ p in 𝓝 (0 : State),
    solutionPaths p = initialPaths p + cubicLift (pathCubic (solutionPaths p)) := by
  filter_upwards [solutionPaths_equation] with p hp
  have hz := congrArg Prod.fst hp
  have hw := congrArg Prod.snd hp
  change (solutionPaths p).1 - constant p.1 - (1/2 : ℝ) • integralCLM (solutionPaths p).2 + 0 = 0 at hz
  rw [add_zero] at hz
  change (solutionPaths p).2 - constant p.2 + integralCLM (conjugate (solutionPaths p).1 * (solutionPaths p).2^2) = 0 at hw
  have hw' : (solutionPaths p).2 = constant p.2 - integralCLM (pathCubic (solutionPaths p)) := by
    simp only [pathCubic,pow_two,mul_assoc] at *
    linear_combination hw
  apply Prod.ext
  · change (solutionPaths p).1 = constant p.1 + (1/2 : ℝ) • integralCLM (constant p.2) +
      (-(1/2 : ℝ)) • integralCLM (integralCLM (pathCubic (solutionPaths p)))
    rw [hw',map_sub,smul_sub] at hz
    linear_combination (norm := module) hz
  · exact hw'

theorem solutionPaths_bigO : solutionPaths =O[𝓝 (0 : State)] (fun p => ‖p‖) := by
  have h := solutionPaths_derivative.isBigO_sub
  simpa only [solutionPaths_zero,sub_zero] using h.norm_right

theorem initialPaths_bigO : initialPaths =O[𝓝 (0 : State)] (fun p => ‖p‖) :=
  (initialPaths.isBigO_id _).norm_right

/-- Cubic multiplication of bounded path families has a genuine cubic bound. -/
theorem pathCubic_bigO {α : State → Paths}
    (h : α =O[𝓝 (0 : State)] (fun p => ‖p‖)) :
    (fun p => pathCubic (α p)) =O[𝓝 (0 : State)] (fun p => ‖p‖^3) := by
  have hz := (conjugate.isBigO_comp (fun p => (α p).1) _).trans h.prod_left_fst
  have hw := h.prod_left_snd
  convert (hz.mul hw).mul hw using 1
  · funext p; simp only [pathCubic]
  · funext p; ring

theorem path_deviation_cubic : (fun p => solutionPaths p - initialPaths p)
    =O[𝓝 (0 : State)] (fun p => ‖p‖^3) := by
  have hb := (cubicLift.isBigO_comp (fun p => pathCubic (solutionPaths p)) _).trans
    (pathCubic_bigO solutionPaths_bigO)
  apply hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [solutionPaths_fixed] with p hp
  conv_rhs => rw [hp]
  abel

theorem pathCubic_difference {α β : State → Paths}
    (ha : α =O[𝓝 (0 : State)] (fun p => ‖p‖))
    (hb : β =O[𝓝 (0 : State)] (fun p => ‖p‖))
    (hd : (fun p => α p - β p) =O[𝓝 (0 : State)] (fun p => ‖p‖^3)) :
    (fun p => pathCubic (α p) - pathCubic (β p))
      =O[𝓝 (0 : State)] (fun p => ‖p‖^5) := by
  have hdz := (conjugate.isBigO_comp (fun p => (α p - β p).1) _).trans hd.prod_left_fst
  have hdw := hd.prod_left_snd
  have hbz := (conjugate.isBigO_comp (fun p => (β p).1) _).trans hb.prod_left_fst
  have h1 : (fun p => conjugate ((α p).1-(β p).1)*(α p).2*(α p).2)
      =O[𝓝 (0 : State)] (fun p => ‖p‖^5) := by
    convert (hdz.mul ha.prod_left_snd).mul ha.prod_left_snd using 1
    funext p; ring
  have h2 : (fun p => conjugate (β p).1*((α p).2-(β p).2)*(α p).2)
      =O[𝓝 (0 : State)] (fun p => ‖p‖^5) := by
    convert (hbz.mul hdw).mul ha.prod_left_snd using 1
    funext p; ring
  have h3 : (fun p => conjugate (β p).1*(β p).2*((α p).2-(β p).2))
      =O[𝓝 (0 : State)] (fun p => ‖p‖^5) := by
    convert (hbz.mul hb.prod_left_snd).mul hdw using 1
    funext p; ring
  apply ((h1.add h2).add h3).congr_left
  intro p
  simp only [pathCubic,map_sub]
  ring

/-- The selected path has an actual fifth-order remainder after its cubic term. -/
theorem solutionPaths_remainder :
    (fun p => solutionPaths p - initialPaths p - cubicLift (pathCubic (initialPaths p)))
      =O[𝓝 (0 : State)] (fun p => ‖p‖^5) := by
  have hc := pathCubic_difference solutionPaths_bigO initialPaths_bigO path_deviation_cubic
  have hb := (cubicLift.isBigO_comp
    (fun p => pathCubic (solutionPaths p) - pathCubic (initialPaths p)) _).trans hc
  apply hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [solutionPaths_fixed] with p hp
  rw [map_sub]
  conv_rhs => rw [hp]
  abel

end RadialMetric.Variation
