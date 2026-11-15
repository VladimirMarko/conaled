import Applications.Orbifold.BoundedMotion.Step
import Applications.Orbifold.Driver.Events

namespace Orbifold.DiskTransport.Numerical.Bounded

structure Result where
  final : Packet
  samples : List Packet
  elapsed : ℚ
  deriving DecidableEq, Repr

/-- A failed schedule is not committed; the driver retains its incoming packet. -/
def run : List Tick → Packet → Except Failure Result
  | [], q => .ok ⟨q, [], 0⟩
  | c :: cs, q => match checkedStep c q with
    | .error err => .error err
    | .ok r => match run cs r with
      | .error err => .error err
      | .ok result => .ok ⟨result.final, r :: result.samples, c.duration + result.elapsed⟩

theorem run_correct {cs : List Tick} {q : Packet} {r : Result} {p : Pose}
    (h : run cs q = .ok r) (hp : Approx q.rational p) :
    Approx r.final.rational (execute p (cs.map Tick.decode)) ∧
    List.Forall₂ (fun q p => Approx q.rational p) r.samples (endpoints p cs) ∧
    List.Forall (fun s => Domain s.state.rational.decode) r.samples := by
  induction cs generalizing q r p with
  | nil =>
    simp only [run, Except.ok.injEq] at h
    subst r
    exact ⟨hp, .nil, trivial⟩
  | cons c cs ih =>
    simp only [run] at h
    cases hs : checkedStep c q with
    | error err => simp [hs] at h
    | ok s =>
      cases hr : run cs s with
      | error err => simp [hs, hr] at h
      | ok t =>
        simp [hs, hr] at h
        subst r
        obtain ⟨hp', hd⟩ := checkedStep_correct hs hp
        obtain ⟨hf, ht, hv⟩ := ih hr hp'
        exact ⟨hf, .cons hp' ht, (List.forall_cons _ _ _).mpr ⟨hd, hv⟩⟩

theorem run_clock {cs : List Tick} {q : Packet} {r : Result} (h : run cs q = .ok r) :
    r.elapsed = clock cs := by
  induction cs generalizing q r with
  | nil =>
    simp only [run, Except.ok.injEq] at h
    subst r
    rfl
  | cons c cs ih =>
    unfold run at h
    cases hs : checkedStep c q with
    | error err => simp [hs] at h
    | ok s =>
      cases hr : run cs s with
      | error err => simp [hs, hr] at h
      | ok t =>
        simp [hs, hr] at h
        subst r
        change c.duration + t.elapsed = _
        rw [ih hr]
        simp [clock]

theorem run_samples_length {cs : List Tick} {q : Packet} {r : Result}
    (h : run cs q = .ok r) : r.samples.length = cs.length := by
  induction cs generalizing q r with
  | nil => simp [run] at h; cases h; rfl
  | cons c cs ih =>
    unfold run at h
    cases hs : checkedStep c q with
    | error err => simp [hs] at h
    | ok s =>
      cases hr : run cs s with
      | error err => simp [hs, hr] at h
      | ok t =>
        simp [hs, hr] at h
        subst r
        exact congrArg Nat.succ (ih hr)

/-- Counts invocations, including the failing tick; no work from rejected attempts is erased. -/
def runMeasured : List Tick → Packet → Except Failure Result × Nat
  | [], q => (.ok ⟨q, [], 0⟩, 0)
  | c :: cs, q => match checkedStep c q with
    | .error err => (.error err, 1)
    | .ok r =>
      let rest := runMeasured cs r
      (match rest.1 with
        | .error err => .error err
        | .ok result => .ok ⟨result.final, r :: result.samples, c.duration + result.elapsed⟩,
       1 + rest.2)

theorem runMeasured_erases (cs : List Tick) (q : Packet) : (runMeasured cs q).1 = run cs q := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    simp only [runMeasured, run]
    cases checkedStep c q with
    | error err => rfl
    | ok r => simp only [ih]

theorem runMeasured_bound (cs : List Tick) (q : Packet) : (runMeasured cs q).2 ≤ cs.length := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    simp only [runMeasured]
    cases checkedStep c q with
    | error err => simp
    | ok r => simpa only [List.length_cons, Nat.add_comm] using Nat.add_le_add_left (ih r) 1

/-- Quarter turns of stored coordinates are exact signed permutations. -/
def State.turn (s : State) : State := ⟨s.py.neg, s.px, s.fy.neg, s.fx⟩
def State.rotate (k : Nat) (s : State) : State := (State.turn^[k]) s
def Packet.rotate (k : Nat) (q : Packet) : Packet := ⟨q.state.rotate k, q.error⟩

theorem State.turn_rational (s : State) : s.turn.rational = s.rational.turn := by
  cases s
  simp [State.turn, State.rational, Bounded.rational, BoundedArithmetic.Scalar.neg,
    Numerical.State.turn, QComplex.turn, neg_div]

theorem State.rotate_rational (k : Nat) (s : State) : (s.rotate k).rational = s.rational.rotate k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [State.rotate, Numerical.State.rotate, Function.iterate_succ_apply']
    rw [State.turn_rational]
    exact congrArg Numerical.State.turn (ih s)

theorem Packet.rotate_rational (k : Nat) (q : Packet) :
    (q.rotate k).rational = q.rational.rotate k := by
  simp [Packet.rotate, Packet.rational, Numerical.Packet.rotate, State.rotate_rational]

theorem rotate_approx (k : Driver.Label) (q : Packet) (p : Pose) :
    Approx (q.rotate k.val).rational (k.decode • p) ↔ Approx q.rational p := by
  rw [Packet.rotate_rational]
  exact Driver.rotate_approx k q.rational p

/-- Two successful rounded executions are compared through their shared exact trajectory.
This is an error bound, not exact equivariance of floor rounding. -/
theorem run_representative_bound (k : Driver.Label) {cs : List Tick} {q : Packet}
    {r s : Result} {p : Pose} (hq : Approx q.rational p)
    (hr : run cs q = .ok r) (hs : run cs (q.rotate k.val) = .ok s) :
    ‖s.final.state.rational.decode - (r.final.rational.rotate k.val).state.decode‖ ≤
      (rational s.final.error : ℝ) + (rational r.final.error : ℝ) := by
  have ha := (run_correct hr hq).1
  have hb := (run_correct hs ((rotate_approx k q p).mpr hq)).1
  have hc := (Driver.rotate_approx k r.final.rational (execute p (cs.map Tick.decode))).mpr ha
  have he : execute (k.decode • p) (cs.map Tick.decode) = k.decode • execute p (cs.map Tick.decode) := by
    exact execute_equivariant k.decode p _
  rw [he] at hb
  have ht := dist_triangle s.final.state.rational.decode
    (coordinates (k.decode • execute p (cs.map Tick.decode)))
    (r.final.rational.rotate k.val).state.decode
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add hb (by simpa only [Approx, Numerical.Packet.rotate, Packet.rational, norm_sub_rev] using hc))

/-- Error against the rational Euler mesh; no continuous truncation is included here. -/
def meshAllowance : List Tick → Packet → ℚ → ℚ
  | [], _, e => e
  | c :: cs, q, e => match checkedStep c q with
    | .error _ => e
    | .ok r => meshAllowance cs r ((1+13*c.duration)*e + stepRoundoff c q)

theorem run_mesh {cs : List Tick} {q : Packet} {r : Result}
    {a : Numerical.Packet} {b : Numerical.Result} {e : ℚ}
    (hr : run cs q = .ok r) (hb : Numerical.run cs a = some b)
    (he : ‖q.state.rational.decode - a.state.decode‖ ≤ (e : ℝ)) :
    ‖r.final.state.rational.decode - b.final.state.decode‖ ≤ (meshAllowance cs q e : ℝ) := by
  induction cs generalizing q r a b e with
  | nil =>
    simp only [run, Except.ok.injEq] at hr
    simp only [Numerical.run, Option.some.injEq] at hb
    subst r
    subst b
    exact he
  | cons c cs ih =>
    cases hs : checkedStep c q with
    | error err => simp [run, hs] at hr
    | ok s =>
      cases ht : run cs s with
      | error err => simp [run, hs, ht] at hr
      | ok t =>
        simp only [run, hs, ht, Except.ok.injEq] at hr
        subst r
        cases hx : Numerical.checkedStep c a with
        | none => simp [Numerical.run, hx] at hb
        | some x =>
          cases hy : Numerical.run cs x with
          | none => simp [Numerical.run, hx, hy] at hb
          | some y =>
            simp [Numerical.run, hx, hy] at hb
            subst b
            have hd : (0 : ℝ) ≤ c.duration := by exact_mod_cast c.nonneg
            have hm := checkedStep_mesh hs hx
            have hp : ‖s.state.rational.decode - x.state.decode‖ ≤
                (((1+13*c.duration)*e + stepRoundoff c q : ℚ) : ℝ) := by
              push_cast
              exact hm.trans (add_le_add
                (mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 1 + 13 * (c.duration : ℝ) by linarith)) le_rfl)
            simpa only [meshAllowance, hs] using ih ht hy hp


end Orbifold.DiskTransport.Numerical.Bounded
