import Applications.Orbifold.Kinetic.ExactDiameter
import Applications.Orbifold.Kinetic.Equivariance

noncomputable section
open Set
namespace Orbifold.Kinetic
open DiskConnection

theorem rational_exact_increments : Real.artanh (4/5) = 2*Real.artanh (1/2) := by
  rw [Real.artanh_eq_half_log (by norm_num : (4/5 : ℝ) ∈ Icc (-1) 1),
    Real.artanh_eq_half_log (by norm_num : (1/2 : ℝ) ∈ Icc (-1) 1)]
  norm_num
  have H := Real.log_pow (3 : ℝ) 2
  norm_num at H
  linarith

theorem rational_exact_DEL : exactD2 1 0 (1/2) + exactD1 1 (1/2) (4/5) = 0 := by
  apply (exact_DEL_iff 1 0 (1/2) (4/5) (by norm_num) (by norm_num)).mpr
  rw [rational_exact_increments,Real.artanh_zero]
  ring

theorem native_exact_DEL (h s t : ℝ) (hh : 0 < h) :
    exactD2 h (DiskTransport.timedRadius s (t-h)) (DiskTransport.timedRadius s t) +
      exactD1 h (DiskTransport.timedRadius s t) (DiskTransport.timedRadius s (t+h)) = 0 := by
  apply (exact_DEL_iff _ _ _ _ hh ?_).mpr
  · simp only [DiskTransport.timedRadius,Real.artanh_tanh]
    ring
  · have H := Real.tanh_sq_lt_one (s*t/2)
    constructor <;> dsimp [DiskTransport.timedRadius] <;> nlinarith

theorem exact_equals_native_integral (p : Pose) (d : ℂ) (hd : Complex.normSq d = 1)
    (s t h : ℝ) (hh : 0 < h) :
    exactAction h (DiskTransport.timedRadius s t) (DiskTransport.timedRadius s (t+h)) =
      ∫ r in t..(t+h), lagrangian (DiskTransport.move p d hd s r).a
        ((DiskTransport.move p d hd s r).frame (d*(s : ℂ))) := by
  rw [native_exact_action h s t (ne_of_gt hh),native_action_integral]

/-- Signed radius retains the chosen diameter, including its passage through the apex. -/
theorem signed_apex_coordinates (s t : ℝ) :
    Real.artanh (DiskTransport.timedRadius s t) = s*t/2 := by
  exact Real.artanh_tanh _

theorem signed_apex_crossing (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    DiskTransport.timedRadius s (-t) < 0 ∧ 0 < DiskTransport.timedRadius s t := by
  have hp : 0 < s*t/2 := by positivity
  have hn : s*(-t)/2 < 0 := by nlinarith
  have hin (r : ℝ) : Real.tanh r ∈ Ioo (-1) 1 :=
    ⟨Real.neg_one_lt_tanh r,Real.tanh_lt_one r⟩
  constructor
  · apply (Real.artanh_lt_artanh_iff (hin _) (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1)).mp
    simpa [DiskTransport.timedRadius,Real.artanh_tanh] using hn
  · apply (Real.artanh_lt_artanh_iff (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1) (hin _)).mp
    simpa [DiskTransport.timedRadius,Real.artanh_tanh] using hp

theorem resting_energy (p : Pose) (d : ℂ) (hd : Complex.normSq d = 1) (t : ℝ) :
    lagrangian (DiskTransport.move p d hd 0 t).a
      ((DiskTransport.move p d hd 0 t).frame (d*(0 : ℂ))) = 0 := by
  simpa using native_energy p d hd 0 t

/-- Zero time is outside the branch construction's admission contract. -/
theorem zero_time_not_admitted : ¬ (0 < (0 : ℝ)) := lt_irrefl _

end Orbifold.Kinetic
