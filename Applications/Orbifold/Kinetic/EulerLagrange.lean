import Applications.Orbifold.Kinetic.Differential

noncomputable section
open scoped ComplexConjugate
namespace Orbifold.Kinetic
open DiskConnection

def momentumRate (z v a : ℂ) : ℂ :=
  (4 / gap z^2 : ℝ) • a + (16*(conj z*v).re/gap z^3 : ℝ) • v

theorem kinetic_coefficient_derivative {c : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hc : HasDerivAt c v t) (hg : gap (c t) ≠ 0) :
    HasDerivAt (fun r => 4 / gap (c r)^2)
      (16*(conj (c t)*v).re/gap (c t)^3) t := by
  have hgap := (hasDerivAt_const t (1 : ℝ)).sub (normSq_derivative hc)
  have h := (hasDerivAt_const t (4 : ℝ)).div (hgap.pow 2) (pow_ne_zero 2 hg)
  convert h using 1
  · rfl
  · dsimp [gap] at hg ⊢
    field_simp
    ring

theorem momentum_derivative {c v : ℝ → ℂ} {a : ℂ} {t : ℝ}
    (hc : HasDerivAt c (v t) t) (hv : HasDerivAt v a t) (hg : gap (c t) ≠ 0) :
    HasDerivAt (fun r => momentum (c r) (v r)) (momentumRate (c t) (v t) a) t := by
  convert (kinetic_coefficient_derivative hc hg).smul hv using 1
  · rfl
  · simp [momentumRate]

theorem momentum_defect (z v a : ℂ) (hg : gap z ≠ 0) :
    momentumRate z v a - force z v = (4 / gap z^2 : ℝ) • (a + christoffel z v v) := by
  apply Complex.ext <;>
    simp only [momentumRate,force,Complex.sub_re,Complex.sub_im,scalar_re,scalar_im,
      Complex.add_re,Complex.add_im,christoffel,coefficient,Complex.mul_re,
      Complex.mul_im,Complex.div_re,Complex.div_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,
      mul_zero,zero_mul,sub_zero,add_zero,Complex.normSq_ofReal] <;>
    field_simp <;> simp [Complex.normSq_apply] <;> ring

theorem rate_eq_force_iff (z v a : ℂ) (hg : gap z ≠ 0) :
    momentumRate z v a = force z v ↔ a = -christoffel z v v := by
  have hn : (4 / gap z^2 : ℝ) ≠ 0 := div_ne_zero (by norm_num) (pow_ne_zero 2 hg)
  rw [← sub_eq_zero,momentum_defect z v a hg,smul_eq_zero]
  simp [hn,eq_neg_iff_add_eq_zero]

/-- Euler–Lagrange uses the actual velocity/position partial derivatives proved
in Differential; the covector is identified with its Euclidean vector. -/
def EulerLagrangeAt (c v : ℝ → ℂ) (t : ℝ) : Prop :=
  HasDerivAt (fun r => momentum (c r) (v r)) (force (c t) (v t)) t

theorem eulerLagrange_iff {c v : ℝ → ℂ} {a : ℂ} {t : ℝ}
    (hc : HasDerivAt c (v t) t) (hv : HasDerivAt v a t) (hg : gap (c t) ≠ 0) :
    EulerLagrangeAt c v t ↔ a = -christoffel (c t) (v t) (v t) := by
  have hm := momentum_derivative hc hv hg
  constructor
  · intro h
    exact (rate_eq_force_iff _ _ _ hg).mp (hm.unique h)
  · intro h
    unfold EulerLagrangeAt
    rw [← (rate_eq_force_iff _ _ _ hg).mpr h]
    exact hm

theorem native_eulerLagrange (p : Pose) (d : ℂ) (hd : Complex.normSq d = 1) (s t : ℝ) :
    EulerLagrangeAt (fun r => (DiskTransport.move p d hd s r).a)
      (fun r => (DiskTransport.move p d hd s r).frame (d*(s : ℂ))) t := by
  apply (eulerLagrange_iff (DiskTransport.move_velocity p d hd s t)
    (DiskTransport.move_geodesic p d hd s t)
    (ne_of_gt (sub_pos.mpr (DiskTransport.move p d hd s t).inside))).mpr
  rfl

end Orbifold.Kinetic
