import Applications.Orbifold.BoundedMotion.Core

namespace Orbifold.DiskTransport.Numerical.Bounded
open BoundedArithmetic

structure Outputs where
  px : Box
  py : Box
  fx : Box
  fy : Box
  budget : Box
  deriving DecidableEq, Repr

/-- The existing coordinate and budget expressions execute unchanged. -/
def evaluate (env : Motion.Variable → Box) : Option Outputs := do
  let px ← Motion.positionStep.1.run env
  let py ← Motion.positionStep.2.run env
  let fx ← Motion.frameStep.1.run env
  let fy ← Motion.frameStep.2.run env
  let budget ← Motion.budget.run env
  pure ⟨px, py, fx, fy, budget⟩

def Outputs.state (o : Outputs) : State :=
  ⟨o.px.value, o.py.value, o.fx.value, o.fy.value⟩

/-- A conservative coordinate-to-product-norm allowance, in exact integer ticks. -/
def Outputs.roundoff (o : Outputs) : ℤ :=
  o.px.radius + o.py.radius + o.fx.radius + o.fy.radius

theorem Outputs.roundoff_nonneg (o : Outputs) : 0 ≤ o.roundoff := by
  have := (radius_range o.px).1
  have := (radius_range o.py).1
  have := (radius_range o.fx).1
  have := (radius_range o.fy).1
  unfold roundoff
  omega

def Outputs.errorTicks (o : Outputs) : ℤ := o.budget.hi.ticks + o.roundoff

theorem evaluate_enclosure {c : Tick} {q : Packet} {i : Input} {o : Outputs}
    (hi : importInput c = some i) (ho : evaluate (inputEnv i q) = some o) :
    Contains o.px ((Numerical.step c.control c.duration q.state.rational).position.1 : ℝ) ∧
    Contains o.py ((Numerical.step c.control c.duration q.state.rational).position.2 : ℝ) ∧
    Contains o.fx ((Numerical.step c.control c.duration q.state.rational).frame.1 : ℝ) ∧
    Contains o.fy ((Numerical.step c.control c.duration q.state.rational).frame.2 : ℝ) ∧
    Contains o.budget (Numerical.budget c.duration (rational q.error) : ℝ) := by
  simp only [evaluate, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ho
  obtain ⟨px, hpx, py, hpy, fx, hfx, fy, hfy, b, hb, rfl⟩ := ho
  have hs := Motion.step_enclosure (inputEnv_sound hi q) hpx hpy hfx hfy
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, ?_⟩
  rw [← Motion.budget_meaning c.control c.duration (rational q.error) q.state.rational]
  exact Motion.budget.sound (inputEnv_sound hi q) hb

/-- The sum of coordinate radii bounds the product norm of the actual rounded update. -/
theorem evaluate_roundoff {c : Tick} {q : Packet} {i : Input} {o : Outputs}
    (hi : importInput c = some i) (ho : evaluate (inputEnv i q) = some o) :
    ‖o.state.rational.decode - (Numerical.step c.control c.duration q.state.rational).decode‖ ≤
      (o.roundoff : ℝ) / 256 := by
  obtain ⟨hpx, hpy, hfx, hfy, _⟩ := evaluate_enclosure hi ho
  have px := certificate_sound hpx
  have py := certificate_sound hpy
  have fx := certificate_sound hfx
  have fy := certificate_sound hfy
  have hp := Complex.norm_le_abs_re_add_abs_im
    (o.state.rational.position.decode - (Numerical.step c.control c.duration q.state.rational).position.decode)
  have hf := Complex.norm_le_abs_re_add_abs_im
    (o.state.rational.frame.decode - (Numerical.step c.control c.duration q.state.rational).frame.decode)
  have npx : (0 : ℝ) ≤ o.px.radius := by exact_mod_cast (radius_range o.px).1
  have npy : (0 : ℝ) ≤ o.py.radius := by exact_mod_cast (radius_range o.py).1
  have nfx : (0 : ℝ) ≤ o.fx.radius := by exact_mod_cast (radius_range o.fx).1
  have nfy : (0 : ℝ) ≤ o.fy.radius := by exact_mod_cast (radius_range o.fy).1
  change max ‖o.state.rational.position.decode - _‖ ‖o.state.rational.frame.decode - _‖ ≤ _
  simp only [Outputs.roundoff, Int.cast_add]
  simp only [State.rational] at px py fx fy
  apply max_le (hp.trans ?_) (hf.trans ?_) <;>
    simp only [QComplex.decode, Complex.sub_re, Complex.sub_im, State.rational, Outputs.state,
      rational_cast] <;> linarith

inductive Failure where
  | precision | range | domain | accuracy | work | unsupported
  deriving DecidableEq, Repr, BEq

/-- Integer domain guard for the selected coordinates, after all rounding. -/
def State.Admitted (s : State) : Prop :=
  s.px.ticks^2 + s.py.ticks^2 ≤ 16384 ∧ s.fx.ticks^2 + s.fy.ticks^2 ≤ 65536
instance (s : State) : Decidable s.Admitted := inferInstanceAs (Decidable (_ ∧ _))

theorem State.admitted_sound {s : State} (h : s.Admitted) : Domain s.rational.decode := by
  have hp : (s.px.ticks : ℚ)^2 + (s.py.ticks : ℚ)^2 ≤ 16384 := by exact_mod_cast h.1
  have hf : (s.fx.ticks : ℚ)^2 + (s.fy.ticks : ℚ)^2 ≤ 65536 := by exact_mod_cast h.2
  have hp' : s.rational.position.normSq ≤ (1/2 : ℚ)^2 := by
    dsimp [State.rational, QComplex.normSq, Bounded.rational]
    nlinarith
  have hf' : s.rational.frame.normSq ≤ (1 : ℚ)^2 := by
    dsimp [State.rational, QComplex.normSq, Bounded.rational]
    nlinarith
  constructor
  · simpa [Numerical.State.decode] using norm_decode_of_sq (by norm_num : (0 : ℚ) ≤ 1/2) hp'
  · simpa [Numerical.State.decode] using norm_decode_of_sq (by norm_num : (0 : ℚ) ≤ 1) hf'

def InputWithinRange (c : Tick) : Prop :=
  |c.control.velocity.1| ≤ 256 ∧ |c.control.velocity.2| ≤ 256 ∧
    |c.control.angular| ≤ 256 ∧ c.duration ≤ 256
instance (c : Tick) : Decidable (InputWithinRange c) := by unfold InputWithinRange; infer_instance

def checkedStep (c : Tick) (q : Packet) : Except Failure Packet :=
  match importInput c with
  | none => .error (if InputWithinRange c then .precision else .range)
  | some i => match evaluate (inputEnv i q) with
    | none => .error .range
    | some o =>
      if Motion.admitted (inputEnv i q) && decide o.state.Admitted then
        match pack o.errorTicks o.errorTicks o.errorTicks with
        | none => .error .range
        | some b => .ok ⟨o.state, b.value⟩
      else .error .domain

/-- Success certifies both the actual rounded output and the continuous trajectory. -/
theorem checkedStep_correct {c : Tick} {q r : Packet} {p : Pose}
    (h : checkedStep c q = .ok r) (hp : Approx q.rational p) :
    Approx r.rational (c.decode.finish p) ∧ Domain r.state.rational.decode := by
  unfold checkedStep at h
  cases hi : importInput c with
  | none => simp [hi] at h
  | some i =>
    simp only [hi] at h
    cases ho : evaluate (inputEnv i q) with
    | none => simp [ho] at h
    | some o =>
      simp only [ho] at h
      split at h
      · rename_i ha
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
        have hd : o.state.Admitted := ha.2
        have hc := Motion.admitted_sound c q.rational (inputEnv_sound hi q) ha.1
        cases hb : pack o.errorTicks o.errorTicks o.errorTicks with
        | none => simp [hb] at h
        | some b =>
          simp only [hb, Except.ok.injEq] at h
          subst r
          refine ⟨?_, State.admitted_sound hd⟩
          have he := (evaluate_enclosure hi ho).2.2.2.2
          have hr := evaluate_roundoff hi ho
          have ht := Numerical.advance_correct hc hp
          have hs := dist_triangle o.state.rational.decode
            (Numerical.step c.control c.duration q.state.rational).decode (coordinates (c.decode.finish p))
          simp only [dist_eq_norm] at hs
          have hbudget := he.2
          have hbval := (pack_fields hb).1
          unfold Approx at ht ⊢
          simp only [Packet.rational, Numerical.advance] at ht ⊢
          rw [rational_cast]
          dsimp [Scalar.decode]
          rw [hbval]
          simp only [Outputs.errorTicks, Int.cast_add]
          dsimp [Scalar.decode] at hbudget
          linarith
      · simp at h

/-- Successful step data identifies the precise expression run behind the output. -/
theorem checkedStep_data {c : Tick} {q r : Packet} (h : checkedStep c q = .ok r) :
    ∃ i o, importInput c = some i ∧ evaluate (inputEnv i q) = some o ∧
      Motion.admitted (inputEnv i q) = true ∧ r.state = o.state ∧ r.error.ticks = o.errorTicks := by
  unfold checkedStep at h
  cases hi : importInput c with
  | none => simp [hi] at h
  | some i =>
    simp only [hi] at h
    cases ho : evaluate (inputEnv i q) with
    | none => simp [ho] at h
    | some o =>
      simp only [ho] at h
      split at h
      · rename_i ha
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
        cases hb : pack o.errorTicks o.errorTicks o.errorTicks with
        | none => simp [hb] at h
        | some b =>
          simp only [hb, Except.ok.injEq] at h
          subst r
          exact ⟨i, o, rfl, ho, ha.1, rfl, (pack_fields hb).1⟩
      · simp at h

def stepRoundoff (c : Tick) (q : Packet) : ℚ :=
  match importInput c with
  | none => 0
  | some i => match evaluate (inputEnv i q) with
    | none => 0
    | some o => o.roundoff / 256

/-- A finite-mesh comparison includes only propagated input discrepancy and actual
rounding. The trajectory truncation term belongs to checkedStep_correct instead. -/
theorem checkedStep_mesh {c : Tick} {q r : Packet} {a b : Numerical.Packet}
    (h : checkedStep c q = .ok r) (hab : Numerical.checkedStep c a = some b) :
    ‖r.state.rational.decode - b.state.decode‖ ≤
      (1 + 13 * (c.duration : ℝ)) * ‖q.state.rational.decode - a.state.decode‖ +
      (stepRoundoff c q : ℝ) := by
  obtain ⟨i, o, hi, ho, ha, hs, _⟩ := checkedStep_data h
  have hq := Motion.admitted_sound c q.rational (inputEnv_sound hi q) ha
  have ha' : Numerical.Admissible c a := by
    unfold Numerical.checkedStep at hab
    split at hab
    · assumption
    · contradiction
  have hb : b = Numerical.advance c a := by
    simpa [Numerical.checkedStep, ha'] using hab.symm
  have hv : ‖c.control.decode.velocity‖ ≤ 1 := by
    rw [← Numerical.Input.decode_velocity]
    simpa only [Rat.cast_one] using norm_decode_of_sq (by norm_num : (0 : ℚ) ≤ 1)
      (by simpa using hq.1)
  have hw : |c.control.decode.angularVelocity| ≤ 1 := by
    rw [← Numerical.Input.decode_angular]
    exact_mod_cast hq.2.1
  have hd : (0 : ℝ) ≤ c.duration := by exact_mod_cast c.nonneg
  have he := euler_stability hd hv hw (admissible_domain hq).1 (admissible_domain ha').1
  rw [← step_decode, ← step_decode] at he
  have ht := dist_triangle r.state.rational.decode
    (Numerical.step c.control c.duration q.state.rational).decode b.state.decode
  simp only [dist_eq_norm] at ht
  rw [hs, hb] at ht ⊢
  have hr := evaluate_roundoff hi ho
  simp only [stepRoundoff, hi, ho, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
  dsimp only [Packet.rational] at he
  exact ht.trans (by dsimp [Numerical.advance]; linarith)


end Orbifold.DiskTransport.Numerical.Bounded
