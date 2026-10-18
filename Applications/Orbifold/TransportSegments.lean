import Applications.Orbifold.DiskTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Experimental explicit radial and circular solutions for disk transport. -/
noncomputable section
open Set
open scoped ComplexConjugate
namespace Orbifold.DiskTransport
open DiskConnection

def turn (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

@[simp] theorem turn_zero : turn 0 = 1 := by simp [turn]
@[simp] theorem turn_nonzero (t : ℝ) : turn t ≠ 0 := Complex.exp_ne_zero _
@[simp] theorem turn_unit (t : ℝ) : Complex.normSq (turn t) = 1 := by
  simp [turn, Complex.normSq_eq_norm_sq, Complex.norm_exp]

theorem turn_derivative (t : ℝ) : HasDerivAt turn (Complex.I * turn t) t := by
  convert (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).cexp using 1
  · funext s; simp [turn, mul_comm]
  · simp [turn, mul_comm]

/-- Rotation of a fixed disk point stays in the disk. -/
def turnPoint (x : Disk) (t : ℝ) : Disk :=
  ⟨x.val * turn t, (disk_mem _).mpr (by
    simpa [map_mul] using (disk_mem _).mp x.property)⟩

theorem circle_coefficient (z : ℂ) (hr : Complex.normSq z = 1 / 5) :
    coefficient z (Complex.I * z) = Complex.I / 2 := by
  have hh : conj z * z = (1 / 5 : ℂ) := by rw [mul_comm, Complex.mul_conj, hr]; norm_num
  simp only [coefficient, gap, hr]
  rw [show 2 * conj z * (Complex.I * z) = 2 * Complex.I * (conj z * z) by ring, hh]
  norm_num; ring

/-- Radius `sqrt(1/5)` makes full-turn holonomy exactly minus identity. -/
def circle (x : Disk) (hr : Complex.normSq x.val = 1 / 5)
    (T : ℝ) (hT : 0 ≤ T) : Segment x (turnPoint x T) where
  duration := T
  nonneg := hT
  curve := fun t => x.val * turn t
  velocity := fun t => Complex.I * (x.val * turn t)
  source := by simp
  target := rfl
  inside := fun t _ => by simpa [map_mul] using (disk_mem _).mp x.property
  derivative := fun t _ => by convert (turn_derivative t).const_mul x.val using 1 <;> ring
  factor := fun t => turn (-t / 2)
  nonzero := fun t _ => turn_nonzero _
  equation := by
    intro t ht
    have hc : Complex.normSq (x.val * turn t) = 1 / 5 := by simp [map_mul, hr]
    rw [circle_coefficient _ hc]
    convert (turn_derivative (-t / 2)).scomp t
      (((hasDerivAt_id t).neg).div_const 2) using 1
    · rfl
    · simp [Complex.real_smul]; ring

@[simp] theorem circle_transport (x : Disk) (hr) (T : ℝ) (hT) (v : ℂ) :
    (circle x hr T hT).transport v = turn (-T / 2) * v := by
  simp [Segment.transport, circle, ParallelTransport.scalar]

/-- A point on the selected circle, with its domain proof. -/
def loopPoint : Disk := ⟨(Real.sqrt (1 / 5) : ℂ), (disk_mem _).mpr (by
  simp [Complex.normSq_ofReal, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 5)]
  norm_num)⟩

theorem loopPoint_radius : Complex.normSq loopPoint.val = 1 / 5 := by
  simp [loopPoint, Complex.normSq_ofReal, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 5)]

@[simp] theorem turn_full : turn (2 * Real.pi) = 1 := by
  simpa [turn] using Complex.exp_two_pi_mul_I

theorem loop_endpoint : turnPoint loopPoint (2 * Real.pi) = loopPoint := by
  apply Subtype.ext; simp [turnPoint]

theorem loop_transport (v : ℂ) :
    (circle loopPoint loopPoint_radius (2 * Real.pi) (by positivity)).transport v = -v := by
  rw [circle_transport]
  have h : turn (-(2 * Real.pi) / 2) = -1 := by
    rw [show -(2 * Real.pi) / 2 = -Real.pi by ring]
    simpa [turn] using Complex.exp_neg_pi_mul_I
  rw [h]; ring

/-- The loop and a hold have the same endpoints and different transport. -/
theorem path_dependence :
    turnPoint loopPoint (2 * Real.pi) = loopPoint ∧
    (circle loopPoint loopPoint_radius (2 * Real.pi) (by positivity)).transport 1 ≠
      (Segment.hold loopPoint (2 * Real.pi) (by positivity)).transport 1 := by
  refine ⟨loop_endpoint, ?_⟩
  rw [loop_transport, Segment.hold_transport]
  norm_num

/-- A real-axis disk coordinate. -/
def realPoint (r : ℝ) (hr : r ^ 2 < 1) : Disk :=
  ⟨r, (disk_mem _).mpr (by simpa only [Complex.normSq_ofReal, pow_two] using hr)⟩

/-- Radial segments on the real diameter, with an explicit affine clock.
Rotated copies are obtained by the C4/phase coordinate adapter. -/
def radial (a speed T : ℝ) (hT : 0 ≤ T)
    (hin : ∀ t ∈ Icc 0 T, (a + speed * t) ^ 2 < 1) :
    Segment (realPoint a (by simpa using hin 0 ⟨le_rfl, hT⟩))
      (realPoint (a + speed * T) (hin T ⟨hT, le_rfl⟩)) where
  duration := T
  nonneg := hT
  curve := fun t => ((a + speed * t : ℝ) : ℂ)
  velocity := fun _ => (speed : ℂ)
  source := by simp [realPoint]
  target := rfl
  inside := fun t ht => by simpa only [Complex.normSq_ofReal, pow_two] using hin t ht
  derivative := by
    intro t ht
    simpa using (((hasDerivAt_id t).const_mul speed).const_add a).ofReal_comp
  factor := fun t => ((1 - (a + speed * t) ^ 2 : ℝ) : ℂ)
  nonzero := by
    intro t ht
    exact_mod_cast ne_of_gt (sub_pos.mpr (hin t ht))
  equation := by
    intro t ht
    have hg : (1 - (a + speed * t) ^ 2 : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (hin t ht))
    have hgc : ((1 - (a + speed * t) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hg
    have hd : HasDerivAt (fun s : ℝ => ((1 - (a + speed * s) ^ 2 : ℝ) : ℂ))
        ((-2 * (a + speed * t) * speed : ℝ) : ℂ) t := by
      convert ((hasDerivAt_const t (1 : ℝ)).sub
        ((((hasDerivAt_id t).const_mul speed).const_add a).pow 2)).ofReal_comp using 1
      · rfl
      · push_cast; simp only [id_eq]; norm_num
    convert hd using 1
    simp only [coefficient, gap, Complex.normSq_ofReal]
    push_cast
    have hh : (1 - ((a + speed * t : ℝ) : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hg
    push_cast at hh
    field_simp
    simp only [map_add, map_mul, Complex.conj_ofReal]

@[simp] theorem radial_transport (a speed T : ℝ) (hT hin) (v : ℂ) :
    (radial a speed T hT hin).transport v =
      (((1 - (a + speed * T) ^ 2) / (1 - a ^ 2) : ℝ) : ℂ) * v := by
  simp [Segment.transport, radial, ParallelTransport.scalar]

def halfRadial := radial 0 1 (1 / 2) (by norm_num) (by
  intro t ht
  simp only [zero_add, one_mul]
  have h0 := ht.1
  have h1 := ht.2
  nlinarith [sq_nonneg t])

theorem halfRadial_transport (v : ℂ) : halfRadial.transport v = (3 / 4 : ℂ) * v := by
  rw [halfRadial, radial_transport]; norm_num

theorem halfRadial_nonconstant : halfRadial.curve 0 ≠ halfRadial.curve halfRadial.duration := by
  norm_num [halfRadial, radial]

end Orbifold.DiskTransport
