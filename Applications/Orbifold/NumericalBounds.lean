import Applications.Orbifold.MotionUniqueness
import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative coordinate bounds for the experimental disk motion backend.
The product norm is the maximum of the complex position and frame norms. -/
noncomputable section
open Set
open scoped ComplexConjugate
namespace Orbifold.DiskTransport.Numerical
open DiskConnection

def Domain (q : ℂ × ℂ) : Prop := ‖q.1‖ ≤ 1 / 2 ∧ ‖q.2‖ ≤ 1

theorem gap_lower {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : 3 / 4 ≤ gap z := by
  unfold gap
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z]

theorem gap_difference {z w : ℂ} (hz : ‖z‖ ≤ 1 / 2) (hw : ‖w‖ ≤ 1 / 2) :
    |gap z - gap w| ≤ ‖z - w‖ := by
  have h := abs_norm_sub_norm_le z w
  have hn : 0 ≤ ‖z‖ + ‖w‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    |gap z - gap w| = |‖z‖ - ‖w‖| * (‖z‖ + ‖w‖) := by
      simp only [gap, Complex.normSq_eq_norm_sq]
      rw [show 1 - ‖z‖ ^ 2 - (1 - ‖w‖ ^ 2) =
        -(‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) by ring, abs_mul, abs_neg, abs_of_nonneg hn]
    _ ≤ ‖z - w‖ * (‖z‖ + ‖w‖) := mul_le_mul_of_nonneg_right h hn
    _ ≤ ‖z - w‖ := by nlinarith [norm_nonneg (z-w)]

def factor (z : ℂ) : ℂ := 2 * conj z / (gap z : ℂ)

theorem factor_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖factor z‖ ≤ 2 := by
  have hg := gap_lower hz
  have hp : 0 < gap z := by linarith
  simp only [factor, norm_div, norm_mul, Complex.norm_conj, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  linarith

theorem factor_difference {z w : ℂ} (hz : ‖z‖ ≤ 1 / 2) (hw : ‖w‖ ≤ 1 / 2) :
    ‖factor z - factor w‖ ≤ 8 * ‖z - w‖ := by
  have hgz := gap_lower hz
  have hgw := gap_lower hw
  have hpz : 0 < gap z := by linarith
  have hpw : 0 < gap w := by linarith
  have hnz : (gap z : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpz
  have hnw : (gap w : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpw
  have he : factor z - factor w = 2 * (conj z - conj w) / (gap z : ℂ) +
      2 * conj w * ((gap w : ℂ) - (gap z : ℂ)) / ((gap z : ℂ) * (gap w : ℂ)) := by
    unfold factor
    field_simp
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hd := gap_difference hw hz
  rw [norm_sub_rev w z] at hd
  have h1 : ‖2 * (conj z - conj w) / (gap z : ℂ)‖ ≤ 3 * ‖z-w‖ := by
    simp only [norm_div, norm_mul, Complex.norm_ofNat, ← map_sub,
      Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpz]
    apply (div_le_iff₀ hpz).mpr
    nlinarith [norm_nonneg (z-w)]
  have h2 : ‖2 * conj w * ((gap w : ℂ) - (gap z : ℂ)) /
      ((gap z : ℂ) * (gap w : ℂ))‖ ≤ 5 * ‖z-w‖ := by
    simp only [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_conj,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpz, abs_of_pos hpw]
    apply (div_le_iff₀ (mul_pos hpz hpw)).mpr
    have hm : 9 / 16 ≤ gap z * gap w := by nlinarith
    have ha := abs_nonneg (gap w - gap z)
    have hx : 2 * ‖w‖ * |gap w - gap z| ≤ ‖z-w‖ := by nlinarith
    nlinarith [norm_nonneg (z-w)]
  linarith

theorem motionField_factor (v : ℂ) (omega : ℝ) (q : ℂ × ℂ) :
    motionField v omega q =
      (q.2 * v, -factor q.1 * q.2 ^ 2 * v + q.2 * (omega : ℂ) * Complex.I) := by
  simp only [motionField, coefficient, factor]
  congr 1
  ring

theorem field_bound {v : ℂ} {omega : ℝ} {q : ℂ × ℂ}
    (hv : ‖v‖ ≤ 1) (ho : |omega| ≤ 1) (hq : Domain q) :
    ‖motionField v omega q‖ ≤ 3 := by
  rw [motionField_factor]
  apply norm_prod_le_iff.mpr
  constructor
  · simp only [norm_mul]
    nlinarith [norm_nonneg q.2, norm_nonneg v, hq.2]
  · apply (norm_add_le _ _).trans
    simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one]
    have hf := factor_bound hq.1
    have hsq : ‖q.2‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg q.2, hq.2]
    have ha : ‖factor q.1‖ * ‖q.2‖ ^ 2 * ‖v‖ ≤ 2 := by
      calc
        ‖factor q.1‖ * ‖q.2‖ ^ 2 * ‖v‖ ≤ 2 * 1 * 1 := by gcongr
        _ = 2 := by norm_num
    have hb : ‖q.2‖ * |omega| ≤ 1 := by
      calc
        ‖q.2‖ * |omega| ≤ 1 * 1 := by gcongr; exact hq.2
        _ = 1 := by norm_num
    linarith

theorem field_difference {v : ℂ} {omega : ℝ} {q r : ℂ × ℂ}
    (hv : ‖v‖ ≤ 1) (ho : |omega| ≤ 1) (hq : Domain q) (hr : Domain r) :
    ‖motionField v omega q - motionField v omega r‖ ≤ 13 * ‖q-r‖ := by
  have hz : ‖q.1-r.1‖ ≤ ‖q-r‖ := norm_fst_le (q-r)
  have hh : ‖q.2-r.2‖ ≤ ‖q-r‖ := norm_snd_le (q-r)
  have hn := norm_nonneg (q-r)
  have hs : ‖q.2 ^ 2 - r.2 ^ 2‖ ≤ 2 * ‖q-r‖ := by
    rw [show q.2 ^ 2 - r.2 ^ 2 = (q.2-r.2)*(q.2+r.2) by ring, norm_mul]
    have ha : ‖q.2+r.2‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [hq.2, hr.2])
    nlinarith [norm_nonneg (q.2-r.2), norm_nonneg (q.2+r.2)]
  have hf : ‖factor q.1-factor r.1‖ ≤ 8 * ‖q-r‖ :=
    (factor_difference hq.1 hr.1).trans (by gcongr)
  have hb := factor_bound hr.1
  have hsq : ‖q.2‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg q.2, hq.2]
  have ht : ‖factor q.1 * q.2^2 - factor r.1 * r.2^2‖ ≤ 12 * ‖q-r‖ := by
    rw [show factor q.1 * q.2^2 - factor r.1 * r.2^2 =
      (factor q.1-factor r.1)*q.2^2 + factor r.1*(q.2^2-r.2^2) by ring]
    apply (norm_add_le _ _).trans
    simp only [norm_mul, norm_pow]
    calc
      _ ≤ (8 * ‖q-r‖) * 1 + 2 * (2 * ‖q-r‖) := by gcongr
      _ = _ := by ring
  rw [motionField_factor, motionField_factor]
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖q.2*v-r.2*v‖ ≤ _
    rw [← sub_mul, norm_mul]
    nlinarith [norm_nonneg (q.2-r.2), norm_nonneg v]
  · change ‖(-factor q.1*q.2^2*v + q.2*(omega : ℂ)*Complex.I) -
      (-factor r.1*r.2^2*v + r.2*(omega : ℂ)*Complex.I)‖ ≤ _
    rw [show (-factor q.1*q.2^2*v + q.2*(omega : ℂ)*Complex.I) -
        (-factor r.1*r.2^2*v + r.2*(omega : ℂ)*Complex.I) =
      -(factor q.1*q.2^2-factor r.1*r.2^2)*v +
        (q.2-r.2)*(omega : ℂ)*Complex.I by ring]
    apply (norm_add_le _ _).trans
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one]
    calc
      _ ≤ (12 * ‖q-r‖) * 1 + ‖q-r‖ * 1 := by gcongr
      _ = _ := by ring

def coordinates (p : Pose) : ℂ × ℂ := (p.a, p.frame 1)

theorem coordinates_derivative (c : Control) (p : Pose) (t : ℝ) :
    HasDerivAt (fun s => coordinates (c.trajectory p s))
      (motionField c.velocity c.angularVelocity (coordinates (c.trajectory p t))) t := by
  convert (c.position_equation p t).prodMk (c.frame_equation p t 1) using 1
  · rfl
  · apply Prod.ext <;> simp [coordinates, motionField, Pose.frame, christoffel, coefficient] <;> ring

theorem frame_bound (p : Pose) : ‖p.frame 1‖ ≤ 1 / 2 := by
  have hu : ‖p.u‖ = 1 := by
    have h := p.unit
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg p.u]
  have hg : 0 < 1 - Complex.normSq p.a := sub_pos.mpr p.inside
  simp only [Pose.frame, mul_one, norm_div, norm_mul, Complex.norm_ofNat, hu,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hg, mul_one]
  have := Complex.normSq_nonneg p.a
  linarith

theorem position_displacement (c : Control) (p : Pose) {t : ℝ} (ht : 0 ≤ t)
    (hv : ‖c.velocity‖ ≤ 1) : ‖(c.trajectory p t).a - p.a‖ ≤ t / 2 := by
  have hvel (q : Pose) : ‖q.frame c.velocity‖ ≤ 1 / 2 := by
    have he : q.frame c.velocity = q.frame 1 * c.velocity := by simp [Pose.frame]; ring
    rw [he, norm_mul]
    calc
      _ ≤ (1 / 2 : ℝ) * 1 := mul_le_mul (frame_bound q) hv (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s (_ : s ∈ Icc 0 t) => (c.position_equation p s).hasDerivWithinAt)
    (fun s (_ : s ∈ Ico 0 t) => hvel (c.trajectory p s)) t ⟨ht, le_rfl⟩
  simpa [div_eq_mul_inv, mul_comm] using h

theorem trajectory_domain (c : Control) (p : Pose) {T : ℝ}
    (hv : ‖c.velocity‖ ≤ 1) (hp : ‖p.a‖ + T / 2 ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Domain (coordinates (c.trajectory p t)) := by
  constructor
  · change ‖(c.trajectory p t).a‖ ≤ _
    have h := norm_add_le ((c.trajectory p t).a-p.a) p.a
    rw [sub_add_cancel] at h
    have hd := position_displacement c p ht.1 hv
    linarith [ht.2]
  · exact (frame_bound _).trans (by norm_num)

/-- Euler truncation in coordinate norm. Rational evaluation contributes no
arithmetic term; the conservative constant avoids a transcendental budget. -/
theorem local_error (c : Control) (p : Pose) {a d : ℝ} (hd : 0 ≤ d)
    (hv : ‖c.velocity‖ ≤ 1) (ho : |c.angularVelocity| ≤ 1)
    (hdom : ∀ t ∈ Icc a (a+d), Domain (coordinates (c.trajectory p t))) :
    ‖coordinates (c.trajectory p (a+d)) -
      (coordinates (c.trajectory p a) + d •
        motionField c.velocity c.angularVelocity (coordinates (c.trajectory p a)))‖ ≤
      39 * d ^ 2 := by
  let f := fun t => coordinates (c.trajectory p t)
  let F := motionField c.velocity c.angularVelocity
  have hfa : Domain (f a) := hdom a ⟨le_rfl, by linarith⟩
  have hdisp (t : ℝ) (ht : t ∈ Icc a (a+d)) : ‖f t - f a‖ ≤ 3 * d := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s (_ : s ∈ Icc a (a+d)) => (coordinates_derivative c p s).hasDerivWithinAt)
      (fun s (hs : s ∈ Ico a (a+d)) => field_bound hv ho (hdom s (mem_Icc_of_Ico hs))) t ht
    exact h.trans (by linarith [ht.2])
  let r := fun t => f t - (f a + (t-a) • F (f a))
  have hr (t : ℝ) : HasDerivAt r (F (f t)-F (f a)) t := by
    simpa [r, f, F] using! (coordinates_derivative c p t).sub
      ((hasDerivAt_const t (f a)).add
        (((hasDerivAt_id t).sub_const a).smul_const (F (f a))))
  have hb (t : ℝ) (ht : t ∈ Ico a (a+d)) : ‖F (f t)-F (f a)‖ ≤ 39*d := by
    exact (field_difference hv ho (hdom t (mem_Icc_of_Ico ht)) hfa).trans
      (by have := hdisp t (mem_Icc_of_Ico ht); linarith)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t (_ : t ∈ Icc a (a+d)) => (hr t).hasDerivWithinAt) hb
    (a+d) ⟨by linarith, le_rfl⟩
  simpa [r, f, F, pow_two, mul_assoc] using h

end Orbifold.DiskTransport.Numerical
