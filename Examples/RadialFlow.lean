import Applications.Geometry.RadialFlow

/-! Nonempty selected-flow clients for the radial variable-curvature metric.
These are existence/ODE clients, not inverse-branch or associativity claims. -/
noncomputable section
namespace Examples.RadialFlow
open RadialMetric

/-- A nonzero admitted velocity. Its unweighted velocity is 1/64. -/
def moving : Initial := ⟨(0,(1/32 : ℂ)), by
  norm_num [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]⟩

theorem moving_nonzero : moving.val ≠ 0 := by
  intro h
  have := congrArg Prod.snd h
  norm_num [moving] at this

theorem moving_initial : geodesicFlow moving 0 = (0,(1/64 : ℂ)) := by
  rw [geodesicFlow_initial]
  norm_num [unweight, moving]

theorem moving_time_one :
    HasDerivAt (geodesicFlow moving) (field (geodesicFlow moving 1)) 1 :=
  geodesicFlow_deriv moving (by norm_num)

theorem moving_bounded (t : ℝ) : ‖boundedFlow moving t‖ ≤ 1/4 := by
  simpa using boundedFlow_mem moving t

end Examples.RadialFlow
