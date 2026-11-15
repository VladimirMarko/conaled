import Applications.OpenSystems.Wiring
import Applications.Orbifold.CheckedMotion
import SquareKit.DiscreteApproximation

/-! A bounded move consumer: position and frame exchange their old coordinates.
Exact wiring is separate from the comparison of coarse and refined Euler steps. -/
noncomputable section
namespace Orbifold.DiskTransport.Numerical.Wired
open Applications.OpenSystems
open SquareKit.DiscreteApproximation
open DiskConnection

abbrev Ports := Bool ⊕ Bool
abbrev Outputs := (Bool × Bool) ⊕ (Bool × Bool)
def complex (i : Bool → ℝ) : ℂ := ⟨i false, i true⟩
def component (z : ℂ) (i : Bool) : ℝ := if i then z.im else z.re

def position : System ℂ Bool (Bool × Bool) where
  field _ i := complex i
  readout z o := component z o.2

def frame : System ℂ Bool (Bool × Bool) where
  field h i := -factor (complex i) * h^2
  readout h o := component h o.2

/-- Each coordinate has a feedback port and a distinct external observation port. -/
def routing : Routing Ports Outputs Empty Ports where
  input
    | .inl i => .inl (.inr (false,i))
    | .inr i => .inl (.inl (false,i))
  output
    | .inl i => .inl (true,i)
    | .inr i => .inr (true,i)

theorem routing_admitted : routing.Admissible := by
  unfold Routing.Admissible Function.Bijective Function.Injective Function.Surjective
  decide +kernel

def wiring : Wiring Ports Outputs Empty Ports := ⟨routing, routing_admitted⟩
def system := (position.parallel frame).wire wiring.toRouting

theorem field_eq (s : ℂ × ℂ) : system.field s Empty.elim = motionField 1 0 s := by
  rw [motionField_factor]
  apply Prod.ext <;> simp [system, wiring, System.wire, System.parallel, position, frame,
    Routing.supply, routing, complex, component]

/-- The external observation exposes every position and frame coordinate. -/
theorem readout_eq (s : ℂ × ℂ) : system.readout s =
    Sum.elim (component s.1) (component s.2) := by
  funext i
  cases i <;> rfl

theorem component_gain (z w : ℂ) (i : Bool) :
    |component z i-component w i| ≤ ‖z-w‖ := by
  cases i
  · simpa [component] using Complex.abs_re_le_norm (z-w)
  · simpa [component] using Complex.abs_im_le_norm (z-w)

theorem readout_gain (s t : ℂ × ℂ) (o : Ports) :
    |system.readout s o-system.readout t o| ≤ dist s t := by
  rw [readout_eq, readout_eq, dist_eq_norm]
  cases o with
  | inl i => exact (component_gain _ _ i).trans (norm_fst_le (s-t))
  | inr i => exact (component_gain _ _ i).trans (norm_snd_le (s-t))

def euler (h : ℝ) (s : ℂ × ℂ) := s + h • system.field s Empty.elim
def halfTwice (h : ℝ) (s : ℂ × ℂ) := euler (h/2) (euler (h/2) s)

/-- These are the actual real interpretations of the production rational steps. -/
theorem step_eq (h : ℚ) (q : State) :
    (step (.move (1,0)) h q).decode = euler h q.decode := by
  rw [step_decode]
  simp only [euler, field_eq]
  congr 2
  · congr 1
    apply Complex.ext <;> norm_num [Input.decode, QComplex.decode, Control.velocity]

/-- Exact wiring substitution needs no error estimate. -/
theorem rewire {J P : Type} (w : Routing Empty Ports J P) :
    system.wire w = (position.parallel frame).wire (wiring.toRouting.comp w) :=
  System.wire_comp _ _ _

/-- The position component has gain one in its supplied frame. -/
theorem position_gain (s t : ℂ × ℂ) :
    ‖(system.field s Empty.elim).1 - (system.field t Empty.elim).1‖ = ‖s.2-t.2‖ := by
  rw [field_eq, field_eq, motionField_factor, motionField_factor]
  simp

/-- The frame row has gains 8 in supplied position and 4 in its own frame. -/
theorem frame_gain {s t : ℂ × ℂ} (hs : Domain s) (ht : Domain t) :
    ‖(system.field s Empty.elim).2 - (system.field t Empty.elim).2‖ ≤
      8*‖s.1-t.1‖ + 4*‖s.2-t.2‖ := by
  have hsq : ‖s.2^2-t.2^2‖ ≤ 2*‖s.2-t.2‖ := by
    rw [show s.2^2-t.2^2 = (s.2-t.2)*(s.2+t.2) by ring, norm_mul]
    have ha : ‖s.2+t.2‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [hs.2, ht.2])
    nlinarith [norm_nonneg (s.2-t.2)]
  have hf := factor_difference hs.1 ht.1
  have hb := factor_bound ht.1
  have hs2 : ‖s.2‖^2 ≤ 1 := by nlinarith [hs.2, norm_nonneg s.2]
  rw [field_eq, field_eq, motionField_factor, motionField_factor]
  simp only [mul_one, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  rw [show -factor s.1*s.2^2 - -factor t.1*t.2^2 =
    -((factor s.1-factor t.1)*s.2^2 + factor t.1*(s.2^2-t.2^2)) by ring, norm_neg]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ (8*‖s.1-t.1‖)*1 + 2*(2*‖s.2-t.2‖) := by gcongr
    _ = _ := by ring

/-- Row aggregation, derived from the actual wired components. -/
theorem field_gain {s t : ℂ × ℂ} (hs : Domain s) (ht : Domain t) :
    ‖system.field s Empty.elim - system.field t Empty.elim‖ ≤ 12*‖s-t‖ := by
  apply norm_prod_le_iff.mpr
  constructor
  · have h := position_gain s t
    have hh : ‖s.2-t.2‖ ≤ ‖s-t‖ := norm_snd_le (s-t)
    change ‖(system.field s Empty.elim).1 - (system.field t Empty.elim).1‖ ≤ _
    rw [h]
    nlinarith [norm_nonneg (s-t)]
  · exact (frame_gain hs ht).trans (by
      have hz : ‖s.1-t.1‖ ≤ ‖s-t‖ := norm_fst_le (s-t)
      have hh : ‖s.2-t.2‖ ≤ ‖s-t‖ := norm_snd_le (s-t)
      linarith)

/-- Component magnitudes 1 and 2 give the full velocity bound. -/
theorem field_size {s : ℂ × ℂ} (hs : Domain s) : ‖system.field s Empty.elim‖ ≤ 2 := by
  rw [field_eq, motionField_factor]
  simp only [mul_one, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  apply norm_prod_le_iff.mpr
  constructor
  · linarith [hs.2]
  · simp only [norm_mul, norm_neg, norm_pow]
    have hf := factor_bound hs.1
    have hh : ‖s.2‖^2 ≤ 1 := by nlinarith [hs.2, norm_nonneg s.2]
    calc
      ‖factor s.1‖ * ‖s.2‖^2 ≤ 2 * 1 := by gcongr
      _ = _ := by norm_num

theorem euler_gain {h : ℝ} (hh : 0 ≤ h) {s t : ℂ × ℂ}
    (hs : Domain s) (ht : Domain t) :
    dist (euler h s) (euler h t) ≤ (1+12*h)*dist s t := by
  rw [dist_eq_norm, dist_eq_norm]
  unfold euler
  rw [show s+h • system.field s Empty.elim - (t+h • system.field t Empty.elim) =
    (s-t)+h • (system.field s Empty.elim-system.field t Empty.elim) by module]
  apply (norm_add_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  have hg := field_gain hs ht
  nlinarith

theorem half_displacement {h : ℝ} (hh : 0 ≤ h) {s : ℂ × ℂ}
    (hs : Domain s) : ‖euler (h/2) s-s‖ ≤ h := by
  simp only [euler, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ h/2)]
  have hb := field_size hs
  nlinarith

theorem defect_identity (h : ℝ) (s : ℂ × ℂ) :
    halfTwice h s-euler h s = (h/2) •
      (system.field (euler (h/2) s) Empty.elim-system.field s Empty.elim) := by
  dsimp [halfTwice, euler]
  module

/-- Position's local refinement defect follows from its supplied-frame gain. -/
theorem position_defect {h : ℝ} (hh : 0 ≤ h) {s : ℂ × ℂ} (hs : Domain s) :
    ‖(halfTwice h s-euler h s).1‖ ≤ h^2/2 := by
  rw [defect_identity]
  change ‖(h/2) • ((system.field (euler (h/2) s) Empty.elim).1 -
    (system.field s Empty.elim).1)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ h/2), position_gain]
  have hd := half_displacement hh hs
  have hz : ‖(euler (h/2) s).2-s.2‖ ≤ ‖euler (h/2) s-s‖ := norm_snd_le (euler (h/2) s-s)
  nlinarith

/-- Frame's local defect follows from its two component sensitivity terms. -/
theorem frame_defect {h : ℝ} (hh : 0 ≤ h) {s : ℂ × ℂ}
    (hs : Domain s) (hm : Domain (euler (h/2) s)) :
    ‖(halfTwice h s-euler h s).2‖ ≤ 6*h^2 := by
  rw [defect_identity]
  change ‖(h/2) • ((system.field (euler (h/2) s) Empty.elim).2 -
    (system.field s Empty.elim).2)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ h/2)]
  have hg := frame_gain hm hs
  have hd := half_displacement hh hs
  have hz : ‖(euler (h/2) s).1-s.1‖ ≤ ‖euler (h/2) s-s‖ := norm_fst_le (euler (h/2) s-s)
  have hw : ‖(euler (h/2) s).2-s.2‖ ≤ ‖euler (h/2) s-s‖ := norm_snd_le (euler (h/2) s-s)
  have hb : ‖(system.field (euler (h/2) s) Empty.elim).2 -
      (system.field s Empty.elim).2‖ ≤ 12*h := by linarith
  nlinarith

/-- The max norm combines the separately derived local component defects. -/
theorem refinement_defect {h : ℝ} (hh : 0 ≤ h) {s : ℂ × ℂ}
    (hs : Domain s) (hm : Domain (euler (h/2) s)) :
    dist (halfTwice h s) (euler h s) ≤ 6*h^2 := by
  rw [dist_eq_norm]
  apply norm_prod_le_iff.mpr
  exact ⟨(position_defect hh hs).trans (by nlinarith [sq_nonneg h]), frame_defect hh hs hm⟩

end Orbifold.DiskTransport.Numerical.Wired
