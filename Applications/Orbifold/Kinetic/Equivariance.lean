import Applications.Orbifold.Kinetic.Legendre
import Applications.Orbifold.Kinetic.Controls
import Applications.Orbifold.LocalDisplacement.Alignment

noncomputable section
open scoped ComplexConjugate
namespace Orbifold.Kinetic
open DiskConnection LocalDisplacement

theorem midpoint_rotate (u x y : ℂ) : midpoint (u*x) (u*y) = u*midpoint x y := by
  simp [midpoint,Complex.real_smul,mul_add]
  ring

theorem gap_rotate (u z : ℂ) (hu : Complex.normSq u = 1) : gap (u*z) = gap z := by
  simp [gap,map_mul,hu]

theorem kinetic_rotate (u z v : ℂ) (hu : Complex.normSq u = 1) :
    lagrangian (u*z) (u*v) = lagrangian z v := by
  simp [lagrangian,gap_rotate u z hu,map_mul,hu]

theorem discrete_rotate (u x y : ℂ) (hu : Complex.normSq u = 1) :
    discrete h (u*x) (u*y) = discrete h x y := by
  simp only [discrete,midpoint_rotate,← mul_sub,gap_rotate u _ hu,map_mul,hu,one_mul]

theorem d1_rotate (u x y : ℂ) (hu : Complex.normSq u = 1) :
    d1 h (u*x) (u*y) = u*d1 h x y := by
  simp only [d1,midpoint_rotate,← mul_sub,gap_rotate u _ hu,map_mul,hu,one_mul]
  simp only [Complex.real_smul]
  ring

theorem d2_rotate (u x y : ℂ) (hu : Complex.normSq u = 1) :
    d2 h (u*x) (u*y) = u*d2 h x y := by
  simp only [d2,midpoint_rotate,← mul_sub,gap_rotate u _ hu,map_mul,hu,one_mul]
  simp only [Complex.real_smul]
  ring

theorem covector_rotate (u p v : ℂ) (hu : Complex.normSq u = 1) :
    covector (u*p) (u*v) = covector p v := by
  simp only [covector_apply,Complex.mul_re,Complex.mul_im]
  simp only [Complex.normSq_apply] at hu
  linear_combination (p.re*v.re+p.im*v.im)*hu

def rotatePhase (u : ℂ) (p : ℂ × ℂ) : ℂ × ℂ := (u*p.1,u*p.2)

theorem minus_rotate (u : ℂ) (hu : Complex.normSq u = 1) (p : ℂ × ℂ) :
    legendreMinus h (rotatePhase u p) = rotatePhase u (legendreMinus h p) := by
  simp [legendreMinus,rotatePhase,d1_rotate u _ _ hu]

theorem plus_rotate (u : ℂ) (hu : Complex.normSq u = 1) (p : ℂ × ℂ) :
    legendrePlus h (rotatePhase u p) = rotatePhase u (legendrePlus h p) := by
  simp [legendrePlus,rotatePhase,d2_rotate u _ _ hu]

theorem DEL_rotate (u : ℂ) (hu : Complex.normSq u = 1) {x y z : ℂ}
    (he : discreteEL h x y z) : discreteEL h (u*x) (u*y) (u*z) := by
  unfold discreteEL at *
  rw [d1_rotate u _ _ hu,d2_rotate u _ _ hu,← mul_add,he,mul_zero]

/-- Branch compatibility is an explicit domain condition, not a canonical equivariant selector. -/
theorem minus_inverse_compatible (h : ℝ) (x y : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) (hy : Complex.normSq y < 1)
    (g : QuarterTurn.C4) {p : ℂ × ℂ}
    (hp : p ∈ (minusBranch h x hh hx).source)
    (hr : rotatePhase (phase g) p ∈ (minusBranch h y hh hy).source) :
    (minusBranch h y hh hy).symm (rotatePhase (phase g) (legendreMinus h p)) =
      rotatePhase (phase g) ((minusBranch h x hh hx).symm (legendreMinus h p)) := by
  rw [minusBranch_inverse h x hh hx hp,← minus_rotate (phase g) (phase_norm g)]
  exact minusBranch_inverse h y hh hy hr

/-- The public phase relation keeps the admitted endpoint witness. No solver is selected. -/
def PhaseRelated (h : ℝ) (a b : ℂ × ℂ) : Prop :=
  0 < h ∧ ∃ p ∈ endpointDomain, legendreMinus h p = a ∧ legendrePlus h p = b

theorem phaseRelated_rotate (g : QuarterTurn.C4) {a b : ℂ × ℂ}
    (H : PhaseRelated h a b) :
    PhaseRelated h (rotatePhase (phase g) a) (rotatePhase (phase g) b) := by
  rcases H with ⟨hh,p,hp,ha,hb⟩
  refine ⟨hh,rotatePhase (phase g) p,?_,?_,?_⟩
  · simpa [endpointDomain,rotatePhase,map_mul,phase_norm] using hp
  · rw [minus_rotate _ (phase_norm g),ha]
  · rw [plus_rotate _ (phase_norm g),hb]

theorem plus_inverse_compatible (h : ℝ) (x y : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) (hy : Complex.normSq y < 1)
    (g : QuarterTurn.C4) {p : ℂ × ℂ}
    (hp : p ∈ (plusBranch h x hh hx).source)
    (hr : rotatePhase (phase g) p ∈ (plusBranch h y hh hy).source) :
    (plusBranch h y hh hy).symm (rotatePhase (phase g) (legendrePlus h p)) =
      rotatePhase (phase g) ((plusBranch h x hh hx).symm (legendrePlus h p)) := by
  rw [plusBranch_inverse h x hh hx hp,← plus_rotate (phase g) (phase_norm g)]
  exact plusBranch_inverse h y hh hy hr

end Orbifold.Kinetic
