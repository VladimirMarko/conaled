import Applications.Geometry.RadialBranches

/-! A nonzero ordinary client of the actual local exponential/log branch. -/
noncomputable section
namespace Examples.RadialExponential
open RadialMetric Set Metric
open scoped Topology

theorem endpoint_initial_derivative :
    HasFDerivAt expMap expDerivative (0 : State) := expMap_derivative

/-- The inverse domain is inhabited by a positive nonzero velocity, not only rest. -/
theorem moving_inverse_client : ∃ ε : ℝ, 0 < ε ∧
    (0,(ε : ℂ)) ∈ branch.source ∧
    Admitted (0,(ε : ℂ)) ∧
    logMap (0,expMap (0,(ε : ℂ))) = (ε : ℂ) := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp branch_neighborhoods.1
  have hpos : 0 < r/2 := half_pos hr
  have hm : (0,((r/2 : ℝ) : ℂ)) ∈ branch.source := by
    apply hball
    rw [mem_ball,dist_zero_right,Prod.norm_def]
    simp only [norm_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
      max_eq_right (le_of_lt hpos)]
    linarith
  exact ⟨r/2,hpos,hm,branch_source_actual hm,log_exp hm⟩

end Examples.RadialExponential
