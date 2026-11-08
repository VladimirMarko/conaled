import Applications.Orbifold.RationalMotion
import SquareKit.Numerical.Error

/-! Checked rational steps carry their error budget across command boundaries.
Rejection means that the conservative domain test did not certify this step. -/
namespace Orbifold.DiskTransport.Numerical
open Set
open scoped NNReal

def budget (d e : ℚ) : ℚ := (1+13*d)*e+39*d^2

structure Packet where
  state : State
  error : ℚ
  deriving DecidableEq, Repr

def Approx (q : Packet) (p : Pose) : Prop := ‖q.state.decode-coordinates p‖ ≤ (q.error : ℝ)

structure Tick where
  control : Input
  duration : ℚ
  nonneg : 0 ≤ duration
  deriving Repr

noncomputable def Tick.decode (c : Tick) : Command :=
  ⟨c.control.decode, c.duration, by exact_mod_cast c.nonneg⟩

def advance (c : Tick) (q : Packet) : Packet :=
  ⟨step c.control c.duration q.state, budget c.duration q.error⟩

def Admissible (c : Tick) (q : Packet) : Prop :=
  c.control.velocity.normSq ≤ 1 ∧ |c.control.angular| ≤ 1 ∧ 0 ≤ q.error ∧
  q.state.position.size + q.error + c.duration/2 ≤ 1/2 ∧
  q.state.frame.normSq ≤ 1 ∧
  (advance c q).state.position.normSq ≤ 1/4 ∧
  (advance c q).state.frame.normSq ≤ 1

instance (c : Tick) (q : Packet) : Decidable (Admissible c q) := by
  unfold Admissible
  infer_instance

def checkedStep (c : Tick) (q : Packet) : Option Packet :=
  if Admissible c q then some (advance c q) else none

theorem norm_decode_of_sq {x : QComplex} {b : ℚ} (hb : 0 ≤ b)
    (hx : x.normSq ≤ b^2) : ‖x.decode‖ ≤ (b : ℝ) := by
  have h : Complex.normSq x.decode ≤ (b : ℝ)^2 := by
    rw [← QComplex.decode_normSq]
    exact_mod_cast hx
  rw [Complex.normSq_eq_norm_sq] at h
  have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
  nlinarith [norm_nonneg x.decode]

theorem admissible_domain {c : Tick} {q : Packet} (h : Admissible c q) :
    Domain q.state.decode ∧ Domain (advance c q).state.decode := by
  rcases h with ⟨hv, ho, he, hz, hh, hz', hh'⟩
  have he' : (0 : ℝ) ≤ q.error := by exact_mod_cast he
  have hd' : (0 : ℝ) ≤ c.duration := by exact_mod_cast c.nonneg
  have hzR : (q.state.position.size : ℝ) + q.error + (c.duration : ℝ)/2 ≤ 1/2 := by
    have H := (Rat.cast_le (K := ℝ)).mpr hz
    norm_num at H
    exact H
  constructor
  · constructor
    · exact (QComplex.norm_decode_le_size _).trans (by linarith)
    · simpa [State.decode] using norm_decode_of_sq (by norm_num : (0 : ℚ) ≤ 1) (by simpa using hh)
  · constructor
    · simpa [State.decode] using norm_decode_of_sq (by norm_num : (0 : ℚ) ≤ 1/2) (by norm_num; exact hz')
    · simpa [State.decode] using norm_decode_of_sq (by norm_num : (0 : ℚ) ≤ 1) (by simpa using hh')

theorem euler_stability {v : ℂ} {omega d : ℝ} {q r : ℂ × ℂ}
    (hd : 0 ≤ d) (hv : ‖v‖ ≤ 1) (ho : |omega| ≤ 1) (hq : Domain q) (hr : Domain r) :
    ‖(q+d • motionField v omega q)-(r+d • motionField v omega r)‖ ≤
      (1+13*d)*‖q-r‖ := by
  rw [show (q+d • motionField v omega q)-(r+d • motionField v omega r) =
    (q-r)+d • (motionField v omega q-motionField v omega r) by module]
  apply (norm_add_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]
  have h := field_difference hv ho hq hr
  nlinarith

/-- Success relates the actual rational update to the existing exact command,
with initial error retained and a separately proved truncation term. -/
theorem advance_correct {c : Tick} {q : Packet} {p : Pose}
    (hc : Admissible c q) (hp : Approx q p) : Approx (advance c q) (c.decode.finish p) := by
  have hd : (0 : ℝ) ≤ c.duration := by exact_mod_cast c.nonneg
  have hv : ‖c.control.decode.velocity‖ ≤ 1 := by
    rw [← Input.decode_velocity]
    simpa only [Rat.cast_one] using norm_decode_of_sq (by norm_num : (0 : ℚ) ≤ 1) (by simpa using hc.1)
  have ho : |c.control.decode.angularVelocity| ≤ 1 := by
    rw [← Input.decode_angular]
    exact_mod_cast hc.2.1
  have he : ‖q.state.decode-coordinates p‖ ≤ (q.error : ℝ) := hp
  have hpz : ‖p.a‖ ≤ (q.state.position.size : ℝ)+q.error := by
    have hdiff : ‖q.state.position.decode-p.a‖ ≤ (q.error : ℝ) :=
      (norm_fst_le (q.state.decode-coordinates p)).trans he
    have ht := norm_add_le (p.a-q.state.position.decode) q.state.position.decode
    rw [sub_add_cancel, norm_sub_rev] at ht
    have hs := QComplex.norm_decode_le_size q.state.position
    linarith
  have hmargin : ‖p.a‖+(c.duration : ℝ)/2 ≤ 1/2 := by
    have h : (q.state.position.size : ℝ)+q.error+(c.duration : ℝ)/2 ≤ 1/2 := by
      have H := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.1
      norm_num at H
      exact H
    linarith
  have hdom : ∀ t ∈ Icc 0 (c.duration : ℝ),
      Domain (coordinates (c.control.decode.trajectory p t)) :=
    fun t ht => trajectory_domain c.control.decode p hv hmargin ht
  have hpd : Domain (coordinates p) := by simpa using hdom 0 ⟨le_rfl, hd⟩
  have hs : LipschitzOnWith ⟨1 + 13 * (c.duration : ℝ), by positivity⟩
      (fun z => z + (c.duration : ℝ) •
        motionField c.control.decode.velocity c.control.decode.angularVelocity z)
      {z | Domain z} := LipschitzOnWith.of_dist_le_mul fun z hz w hw => by
    rw [dist_eq_norm, dist_eq_norm]
    exact euler_stability hd hv ho hz hw
  have hl := local_error c.control.decode p (a := 0) hd hv ho (by simpa using hdom)
  simp only [zero_add, Control.initial] at hl
  have h := NumericalError.propagate hs (admissible_domain hc).1 hpd
    (y := coordinates (c.control.decode.trajectory p c.duration))
    (d := 39 * (c.duration : ℝ)^2)
    (by simpa only [dist_eq_norm] using he)
    (by rw [dist_eq_norm, norm_sub_rev]; exact hl)
  unfold Approx advance
  dsimp only
  rw [step_decode]
  simp only [dist_eq_norm] at h
  unfold budget
  push_cast
  exact h

theorem checkedStep_correct {c : Tick} {q r : Packet} {p : Pose}
    (h : checkedStep c q = some r) (hp : Approx q p) :
    Approx r (c.decode.finish p) ∧ Domain r.state.decode := by
  unfold checkedStep at h
  split at h
  · cases h
    exact ⟨advance_correct ‹_› hp, (admissible_domain ‹_›).2⟩
  · contradiction

end Orbifold.DiskTransport.Numerical
