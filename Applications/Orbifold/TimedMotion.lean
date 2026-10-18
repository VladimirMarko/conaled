import Applications.Orbifold.PoseConnection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
open Set
open scoped ComplexConjugate
/-! Experimental timed diameter geodesics for the curvature -1 disk metric.
Body velocity is `d * s`, with unit complex direction `d` and signed speed `s`. -/
noncomputable section
namespace Orbifold.DiskTransport

theorem timed_radius_derivative (s t : ℝ) :
    HasDerivAt (fun t => Real.tanh (s * t / 2))
      (s / 2 * (1 - Real.tanh (s * t / 2) ^ 2)) t := by
  have hd := ((Real.hasDerivAt_sinh (s*t/2)).div
    (Real.hasDerivAt_cosh (s*t/2)) (ne_of_gt (Real.cosh_pos _))).comp t
      (((hasDerivAt_id t).const_mul s).div_const 2)
  convert hd using 1
  · funext t; exact Real.tanh_eq_sinh_div_cosh _
  · simp only [Real.tanh_eq_sinh_div_cosh, mul_one]
    field_simp

open DiskConnection

def timedRadius (s t : ℝ) := Real.tanh (s * t / 2)

theorem timedRadius_inside (s t : ℝ) : timedRadius s t ^ 2 < 1 :=
  Real.tanh_sq_lt_one _

def diameterPose (d : ℂ) (hd : Complex.normSq d = 1) (s t : ℝ) : Pose where
  a := d * (timedRadius s t : ℂ)
  u := 1
  inside := by simpa [map_mul, hd, Complex.normSq_ofReal, pow_two] using timedRadius_inside s t
  unit := by simp

theorem diameter_velocity (d : ℂ) (hd : Complex.normSq d = 1) (s t : ℝ) :
    HasDerivAt (fun t => (diameterPose d hd s t).a)
      ((diameterPose d hd s t).frame (d * (s : ℂ))) t := by
  convert (timed_radius_derivative s t).ofReal_comp.const_mul d using 1
  · rfl
  · simp only [diameterPose, Pose.frame, map_mul, hd, one_mul, mul_one,
      Complex.normSq_ofReal, timedRadius]
    push_cast
    ring

theorem diameter_parallel (d : ℂ) (hd : Complex.normSq d = 1) (s t : ℝ) (w : ℂ) :
    HasDerivAt (fun t => (diameterPose d hd s t).frame w)
      (-coefficient (diameterPose d hd s t).a
        ((diameterPose d hd s t).frame (d * (s : ℂ))) *
          (diameterPose d hd s t).frame w) t := by
  have hn : (1 - (timedRadius s t : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr (timedRadius_inside s t))
  have hu : conj d * d = 1 := by rw [mul_comm, Complex.mul_conj, hd]; norm_num
  have h := (((hasDerivAt_const t (1 : ℝ)).sub
    ((timed_radius_derivative s t).pow 2)).ofReal_comp.mul_const w).div_const 2
  convert h using 1
  · funext r
    simp only [Pose.frame, diameterPose, map_mul, hd, one_mul, mul_one,
      Complex.normSq_ofReal, timedRadius, Pi.sub_apply, Pi.mul_apply,
      Complex.ofReal_sub, Complex.ofReal_one, pow_two]
  · simp only [Pose.frame, diameterPose, map_mul, hd, one_mul, mul_one,
      coefficient, gap, Complex.normSq_ofReal]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_div,
      Nat.reduceSub, pow_one, zero_sub, Complex.ofReal_neg]
    dsimp [timedRadius] at hn ⊢
    field_simp
    simp only [Complex.conj_ofReal]
    linear_combination -(s : ℂ) * (Real.tanh (s * t / 2) : ℂ) * w * hu

/-- A timed move from any initial pose. -/
def move (p : Pose) (d : ℂ) (hd : Complex.normSq d = 1) (s t : ℝ) : Pose :=
  p.comp (diameterPose d hd s t)

theorem move_position (p : Pose) (d : ℂ) (hd) (s t : ℝ) :
    (move p d hd s t).a = p.mobius (diameterPose d hd s t).a := by
  simp [move, Pose.comp, Pose.mobius, gyroAdd, mul_assoc]

theorem move_frame (p : Pose) (d : ℂ) (hd) (s t : ℝ) (w : ℂ) :
    (move p d hd s t).frame w =
      p.derivative (diameterPose d hd s t).a * (diameterPose d hd s t).frame w :=
  p.frame_comp _ w

@[simp] theorem move_initial (p : Pose) (d : ℂ) (hd) (s : ℝ) :
    move p d hd s 0 = p := by
  have h : diameterPose d hd s 0 = Pose.identity := by
    unfold diameterPose timedRadius Pose.identity
    simp only [mul_zero, zero_div, Real.tanh_zero, Complex.ofReal_zero]
  rw [move, h]
  apply Pose.motion_injective
  simp [Pose.motion_comp]

theorem move_velocity (p : Pose) (d : ℂ) (hd) (s t : ℝ) :
    HasDerivAt (fun t => (move p d hd s t).a)
      ((move p d hd s t).frame (d * (s : ℂ))) t := by
  simpa only [move_position, move_frame] using p.mobius_curve_derivative
    (diameter_velocity d hd s t) (diameterPose d hd s t).inside

theorem move_parallel (p : Pose) (d : ℂ) (hd) (s t : ℝ) (w : ℂ) :
    HasDerivAt (fun t => (move p d hd s t).frame w)
      (-coefficient (move p d hd s t).a
        ((move p d hd s t).frame (d * (s : ℂ))) * (move p d hd s t).frame w) t := by
  simpa only [move_position, move_frame] using p.push_parallel
    (diameter_velocity d hd s t) (diameterPose d hd s t).inside
    (diameter_parallel d hd s t w)

/-- The velocity itself is parallel, so the trajectory is geodesic. -/
theorem move_geodesic (p : Pose) (d : ℂ) (hd) (s t : ℝ) :
    HasDerivAt (fun t => (move p d hd s t).frame (d * (s : ℂ)))
      (-christoffel (move p d hd s t).a
        ((move p d hd s t).frame (d * (s : ℂ)))
        ((move p d hd s t).frame (d * (s : ℂ)))) t := by
  simpa only [christoffel, neg_mul] using move_parallel p d hd s t (d * (s : ℂ))

/-- Squared metric speed is the squared body speed at every real time. -/
theorem move_speed (p : Pose) (d : ℂ) (hd) (s t : ℝ) :
    metric (move p d hd s t).a ((move p d hd s t).frame (d * (s : ℂ)))
      ((move p d hd s t).frame (d * (s : ℂ))) = s ^ 2 := by
  simpa [metric, gap, map_mul, hd, Complex.normSq_ofReal, Complex.normSq_apply, pow_two] using
    ConnectionAssessment.pose_frame_norm (move p d hd s t) (d * (s : ℂ))

theorem frame_one_nonzero (p : Pose) : p.frame 1 ≠ 0 := by
  have ha : 1 - (Complex.normSq p.a : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr p.inside)
  have hu : p.u ≠ 0 := by intro h; have := p.unit; simp [h] at this
  simpa [Pose.frame] using div_ne_zero (mul_ne_zero ha hu) (by norm_num : (2 : ℂ) ≠ 0)

/-- The analytic path certificate is constructed from the solved moving frame. -/
def moveSegment (p : Pose) (d : ℂ) (hd) (s T : ℝ) (hT : 0 ≤ T) :
    Segment (QuarterTurn.position p) (QuarterTurn.position (move p d hd s T)) where
  duration := T
  nonneg := hT
  curve := fun t => (move p d hd s t).a
  velocity := fun t => (move p d hd s t).frame (d * (s : ℂ))
  source := by simp [QuarterTurn.position]
  target := rfl
  inside := fun t _ => (move p d hd s t).inside
  derivative := fun t _ => move_velocity p d hd s t
  factor := fun t => (move p d hd s t).frame 1
  nonzero := fun t _ => frame_one_nonzero _
  equation := fun t _ => move_parallel p d hd s t 1

/-- Agreement is along the actual timed path, for every frame vector. -/
theorem move_transport (p : Pose) (d : ℂ) (hd) (s T : ℝ) (hT : 0 ≤ T) (w : ℂ) :
    (moveSegment p d hd s T hT).transport (p.frame w) = (move p d hd s T).frame w := by
  have h := (moveSegment p d hd s T hT).field_unique
    (fun t => (move p d hd s t).frame w)
    (fun t _ => move_parallel p d hd s t w) T ⟨hT, le_rfl⟩
  simpa only [move_initial, Segment.field, Segment.transport, ParallelTransport.scalar_apply, moveSegment] using! h.symm

/-- A vertical turn at a fixed disk point, with angular velocity in radians per unit time. -/
def spin (p : Pose) (omega t : ℝ) : Pose where
  a := p.a
  u := p.u * turn (omega * t)
  inside := p.inside
  unit := by simp [map_mul, p.unit]

@[simp] theorem spin_initial (p : Pose) (omega : ℝ) : spin p omega 0 = p := by
  cases p; simp [spin]

theorem spin_frame (p : Pose) (omega t : ℝ) (w : ℂ) :
    (spin p omega t).frame w = p.frame w * turn (omega * t) := by
  simp [spin, Pose.frame]; ring

theorem spin_velocity (p : Pose) (omega t : ℝ) :
    HasDerivAt (fun t => (spin p omega t).a) ((spin p omega t).frame 0) t := by
  simpa [Pose.frame, spin] using! hasDerivAt_const t p.a

theorem spin_equation (p : Pose) (omega t : ℝ) (w : ℂ) :
    HasDerivAt (fun t => (spin p omega t).frame w)
      ((spin p omega t).frame ((omega : ℂ) * Complex.I * w) -
        christoffel (spin p omega t).a ((spin p omega t).frame 0)
          ((spin p omega t).frame w)) t := by
  have h := ((turn_derivative (omega*t)).scomp t
    ((hasDerivAt_id t).const_mul omega)).const_mul (p.frame w)
  convert h using 1
  · funext r; exact spin_frame p omega r w
  · simp [Pose.frame, spin, christoffel, coefficient, Complex.real_smul]; ring

/-- Every pose constructed here carries the original metric-unit frame. -/
theorem frame_metric (p : Pose) (w : ℂ) :
    metric p.a (p.frame w) (p.frame w) = Complex.normSq w := by
  simpa [metric, gap, Complex.normSq_apply] using ConnectionAssessment.pose_frame_norm p w

/-- The entire real inner product is preserved by the normalized frame. -/
theorem frame_pair (p : Pose) (v w : ℂ) :
    metric p.a (p.frame v) (p.frame w) = (conj v * w).re := by
  have h := frame_metric p (v + w)
  have hv := frame_metric p v
  have hw := frame_metric p w
  have hp : metric p.a (p.frame (v + w)) (p.frame (v + w)) =
      metric p.a (p.frame v) (p.frame v) + 2 * metric p.a (p.frame v) (p.frame w) +
      metric p.a (p.frame w) (p.frame w) := by
    have hadd : p.frame (v + w) = p.frame v + p.frame w := by
      simp only [Pose.frame]; ring
    rw [hadd]
    simp [metric, Complex.mul_re]
    ring
  rw [hp] at h
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im] at h hv hw ⊢
  linear_combination (h - hv - hw) / 2

/-- A half turn changes the frame although transport along its fixed position is identity. -/
theorem spin_half_turn (p : Pose) :
    (spin p 1 Real.pi).frame 1 ≠
      (Segment.hold (QuarterTurn.position p) Real.pi (le_of_lt Real.pi_pos)).transport (p.frame 1) := by
  rw [spin_frame, Segment.hold_transport]
  have ht : turn Real.pi = -1 := by simp [turn]
  simp only [one_mul, ht, LinearEquiv.refl_apply, mul_neg_one]
  intro h
  have hz : p.frame 1 = 0 := by linear_combination -h / 2
  exact frame_one_nonzero p hz
end Orbifold.DiskTransport
