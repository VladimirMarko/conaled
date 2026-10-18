import Applications.Orbifold.TransportFrames
open scoped ComplexConjugate
/-! Experimental analytic connection preservation for disk poses.
The second derivative is required to push parallel fields along a trajectory. -/
noncomputable section
namespace Orbifold
open DiskConnection

def Pose.secondDerivative (p : Pose) (z : ℂ) : ℂ :=
  -2 * (1 - (Complex.normSq p.a : ℂ)) * p.u * (conj p.a * p.u) /
    (1 + conj p.a * p.u * z)^3

theorem Pose.derivative_derivative (p : Pose) (z : Disk) :
    HasDerivAt p.derivative (p.secondDerivative z.val) z.val := by
  have hd := (hasDerivAt_const z.val ((1 - (Complex.normSq p.a : ℂ)) * p.u)).div
    (((hasDerivAt_const z.val (1 : ℂ)).add
      ((hasDerivAt_id z.val).const_mul (conj p.a * p.u))).pow 2)
      (pow_ne_zero 2 (p.act_denominator z))
  convert hd using 1
  · rfl
  · dsimp [derivative, secondDerivative]
    field_simp
    ring

theorem Pose.mobius_gap (p : Pose) (z : Disk) :
    gap (p.mobius z.val) = gap p.a * gap z.val /
      Complex.normSq (1 + conj p.a * p.u * z.val) := by
  have h := gyro_gap p.a (p.u * z.val) p.inside
    (by simpa [map_mul, p.unit] using (disk_mem _).mp z.property)
  simpa [gap, gyroAdd, mobius, map_mul, p.unit, mul_assoc] using h

theorem Pose.connection_preserved (p : Pose) (z : Disk) (v w : ℂ) :
    p.secondDerivative z.val * v * w +
      christoffel (p.mobius z.val) (p.derivative z.val * v) (p.derivative z.val * w) =
    p.derivative z.val * christoffel z.val v w := by
  have hd := p.act_denominator z
  have hdc : conj (1 + conj p.a * p.u * z.val) ≠ 0 := by
    intro h; apply hd; simpa using congrArg conj h
  have hx : (gap z.val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr ((disk_mem _).mp z.property))
  have ha : (gap p.a : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr p.inside)
  have hu : p.u * conj p.u = 1 := by rw [Complex.mul_conj, p.unit]; norm_num
  simp only [christoffel, coefficient, p.mobius_gap]
  push_cast
  rw [← Complex.mul_conj (1 + conj p.a * p.u * z.val)]
  simp only [mobius, derivative, secondDerivative, map_div₀, map_add, map_mul,
    map_one, starRingEnd_self_apply]
  have hdc' : 1 + p.a * conj p.u * conj z.val ≠ 0 := by
    simpa using hdc
  have hpa : 1 - (Complex.normSq p.a : ℂ) ≠ 0 := by simpa [gap] using ha
  have hzx : 1 - (Complex.normSq z.val : ℂ) ≠ 0 := by simpa [gap] using hx
  simp only [gap, Complex.ofReal_sub, Complex.ofReal_one]
  field_simp (disch := first | assumption | simpa only [mul_comm, mul_left_comm, mul_assoc] using hd | simpa only [mul_comm, mul_left_comm, mul_assoc] using hdc')
  rw [← Complex.mul_conj z.val]
  linear_combination 2 * p.u * v * w * conj z.val * hu

/-- Apply a complex derivative to a curve with a real clock. -/
theorem Pose.mobius_curve_derivative (p : Pose) {c : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hc : HasDerivAt c v t) (hin : Complex.normSq (c t) < 1) :
    HasDerivAt (fun r => p.mobius (c r)) (p.derivative (c t) * v) t := by
  have h := ((p.hasDerivAt_mobius ⟨c t, (disk_mem _).mpr hin⟩).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hc
  simpa [Function.comp_def, mul_comm] using! h

/-- Pushing a parallel field uses connection preservation, not pose composition alone. -/
theorem Pose.push_parallel (p : Pose) {c f : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hc : HasDerivAt c v t) (hin : Complex.normSq (c t) < 1)
    (hf : HasDerivAt f (-coefficient (c t) v * f t) t) :
    HasDerivAt (fun r => p.derivative (c r) * f r)
      (-coefficient (p.mobius (c t)) (p.derivative (c t) * v) *
        (p.derivative (c t) * f t)) t := by
  have h := ((p.derivative_derivative ⟨c t, (disk_mem _).mpr hin⟩).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hc
  have hd : HasDerivAt (fun r => p.derivative (c r)) (p.secondDerivative (c t) * v) t := by
    simpa [Function.comp_def, mul_comm] using! h
  convert hd.mul hf using 1
  have hp := p.connection_preserved ⟨c t, (disk_mem _).mpr hin⟩ v (f t)
  dsimp [christoffel] at hp
  linear_combination -hp
end Orbifold
