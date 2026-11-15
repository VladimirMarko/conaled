import Applications.Geometry.RadialDivision
import Applications.Geometry.RadialAngular
import Applications.Geometry.RadialNonassociative

/-! Parenthesized local clients retain every intermediate domain. The theorem
below supplies a positive ordinary input; it does not assert associativity. -/
noncomputable section
namespace Examples.RadialDisplacement
open RadialMetric Complex Set Metric
open scoped Topology

def firstPair (t : ℝ) : State := (t,t*I)
def secondPair (t : ℝ) : State := (t*I,t*I)
def leftPair (t : ℝ) : State := (displacement (firstPair t),t*I)
def rightPair (t : ℝ) : State := (t,displacement (secondPair t))

theorem parenthesized_domains : ∀ᶠ t in 𝓝 (0 : ℝ),
    DisplacementDomain (firstPair t) ∧ DisplacementDomain (secondPair t) ∧
    DisplacementDomain (leftPair t) ∧ DisplacementDomain (rightPair t) := by
  have hf : ContinuousAt firstPair 0 := by unfold firstPair; fun_prop
  have hs : ContinuousAt secondPair 0 := by unfold secondPair; fun_prop
  have hf0 : firstPair 0 = 0 := by simp [firstPair]
  have hs0 : secondPair 0 = 0 := by simp [secondPair]
  have hm := displacement_smooth.continuousAt
  have hmf : ContinuousAt (fun t => displacement (firstPair t)) 0 := by
    apply hm.comp_of_eq hf
    exact hf0
  have hms : ContinuousAt (fun t => displacement (secondPair t)) 0 := by
    apply hm.comp_of_eq hs
    exact hs0
  have hl : ContinuousAt leftPair 0 := hmf.prodMk (by fun_prop)
  have hr : ContinuousAt rightPair 0 := (by fun_prop : ContinuousAt (fun t : ℝ => (t : ℂ)) 0).prodMk hms
  have hl0 : leftPair 0 = 0 := by simp [leftPair,hf0,displacement_zero]
  have hr0 : rightPair 0 = 0 := by simp [rightPair,hs0,displacement_zero]
  have h1 := hf.tendsto.eventually (hf0 ▸ displacement_domain_near_zero)
  have h2 := hs.tendsto.eventually (hs0 ▸ displacement_domain_near_zero)
  have h3 := hl.tendsto.eventually (hl0 ▸ displacement_domain_near_zero)
  have h4 := hr.tendsto.eventually (hr0 ▸ displacement_domain_near_zero)
  filter_upwards [h1,h2,h3,h4] with t h1 h2 h3 h4
  exact ⟨h1,h2,h3,h4⟩

theorem positive_parenthesized_client : ∃ t : ℝ, 0 < t ∧
    DisplacementDomain (firstPair t) ∧ DisplacementDomain (secondPair t) ∧
    DisplacementDomain (leftPair t) ∧ DisplacementDomain (rightPair t) := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp parenthesized_domains
  refine ⟨r/2,half_pos hr,hball ?_⟩
  rw [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos (half_pos hr)]
  linarith

/-- The exact selected origin geodesic, including its admitted-flow witness. -/
theorem selected_radial_transport {y : ℂ} (hy : (0,y) ∈ branch.target) (v : ℂ) :
    let p : Initial := ⟨weight (0,originLog y),(log_admitted hy).1⟩
    originParallel p 0 v = v ∧ originParallel p 1 v = radialParallel y v ∧
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => originParallel p s v)
      (-gamma (boundedFlow p t).1 ((boundedFlow p t).2/2) (originParallel p t v)) t := by
  dsimp only
  refine ⟨originParallel_initial _ rfl v,radialParallel_selected hy v,?_⟩
  intro t ht
  exact originParallel_derivative _ rfl v ht

/-- An ordinary three-input client, with both parenthesizations defined and unequal. -/
theorem nonassociative_client : ∃ t : ℝ, 0 < t ∧
    DisplacementDomain (firstPair t) ∧ DisplacementDomain (secondPair t) ∧
    DisplacementDomain (leftPair t) ∧ DisplacementDomain (rightPair t) ∧
    displacement (leftPair t) ≠ displacement (rightPair t) :=
  RadialMetric.Nonassociative.positive_nonassociative_client

end Examples.RadialDisplacement
