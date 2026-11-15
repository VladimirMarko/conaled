import Examples.BoundedArithmetic
import Applications.Orbifold.CheckedMotion

/-! Coordinate arithmetic for one disk-motion Euler step. This is an enclosure
of the rational formula, not a theorem about an entire trajectory. -/
namespace BoundedArithmetic.Motion
open Orbifold.DiskTransport

inductive Variable where
  | px | py | fx | fy | vx | vy | angular | duration | error
  deriving DecidableEq, Repr

abbrev E := Expr Variable
abbrev Pair := E × E

def constant (n : ℤ) (h : -65536 ≤ n ∧ n ≤ 65536) : E := .literal ⟨n, h.1, h.2⟩
def zero : E := constant 0 (by norm_num)
def one : E := constant 256 (by norm_num)
def two : E := constant 512 (by norm_num)
def position : Pair := (.input .px, .input .py)
def frame : Pair := (.input .fx, .input .fy)
def control : Pair := (.input .vx, .input .vy)
def addPair (a b : Pair) : Pair := (.add a.1 b.1, .add a.2 b.2)
def mulPair (a b : Pair) : Pair :=
  (.sub (.mul a.1 b.1) (.mul a.2 b.2), .add (.mul a.1 b.2) (.mul a.2 b.1))
def scalePair (k : E) (a : Pair) : Pair := (.mul k a.1, .mul k a.2)
def conjPair (a : Pair) : Pair := (a.1, .neg a.2)
def turnPair (a : Pair) : Pair := (.neg a.2, a.1)
def normSq (a : Pair) : E := .add (.mul a.1 a.1) (.mul a.2 a.2)
def velocity : Pair := mulPair frame control
def coefficient : E := .divide (.neg two) (.sub one (normSq position))
def frameField : Pair := addPair
  (scalePair coefficient (mulPair (mulPair (conjPair position) velocity) frame))
  (scalePair (.input .angular) (turnPair frame))
def positionStep : Pair := addPair position (scalePair (.input .duration) velocity)
def frameStep : Pair := addPair frame (scalePair (.input .duration) frameField)
def budget : E := .add
  (.mul (.add one (.mul (constant 3328 (by norm_num)) (.input .duration))) (.input .error))
  (.mul (constant 9984 (by norm_num)) (.mul (.input .duration) (.input .duration)))

noncomputable def exactEnv (c : Numerical.Input) (d e : ℚ) (q : Numerical.State) : Variable → ℝ
  | .px => q.position.1 | .py => q.position.2
  | .fx => q.frame.1 | .fy => q.frame.2
  | .vx => c.velocity.1 | .vy => c.velocity.2
  | .angular => c.angular | .duration => d | .error => e

/-- Every signed operation of the existing Euler coordinate formula is retained. -/
theorem step_meaning (c : Numerical.Input) (d e : ℚ) (q : Numerical.State) :
    positionStep.1.meaning (exactEnv c d e q) = ((Numerical.step c d q).position.1 : ℝ) ∧
    positionStep.2.meaning (exactEnv c d e q) = ((Numerical.step c d q).position.2 : ℝ) ∧
    frameStep.1.meaning (exactEnv c d e q) = ((Numerical.step c d q).frame.1 : ℝ) ∧
    frameStep.2.meaning (exactEnv c d e q) = ((Numerical.step c d q).frame.2 : ℝ) := by
  norm_num [positionStep, frameStep, frameField, coefficient, velocity, position, frame,
    control, addPair, mulPair, scalePair, conjPair, turnPair, normSq, one, two,
    constant, Expr.meaning, Scalar.decode, exactEnv, Numerical.step, Numerical.field,
    Numerical.QComplex.add, Numerical.QComplex.mul, Numerical.QComplex.scale, Numerical.QComplex.conj,
    Numerical.QComplex.turn, Numerical.QComplex.normSq, pow_two]

theorem budget_meaning (c : Numerical.Input) (d e : ℚ) (q : Numerical.State) :
    budget.meaning (exactEnv c d e q) = (Numerical.budget d e : ℝ) := by
  norm_num [budget, one, constant, Expr.meaning, Scalar.decode, exactEnv, Numerical.budget, pow_two]

/-- The certificate is computed from primitive enclosures at each arithmetic node. -/
theorem step_enclosure {env : Variable → Box} {c : Numerical.Input} {d e : ℚ} {q : Numerical.State}
    (h : ∀ i, Contains (env i) (exactEnv c d e q i)) {px py fx fy : Box}
    (hpx : positionStep.1.run env = some px) (hpy : positionStep.2.run env = some py)
    (hfx : frameStep.1.run env = some fx) (hfy : frameStep.2.run env = some fy) :
    Contains px ((Numerical.step c d q).position.1 : ℝ) ∧
    Contains py ((Numerical.step c d q).position.2 : ℝ) ∧
    Contains fx ((Numerical.step c d q).frame.1 : ℝ) ∧
    Contains fy ((Numerical.step c d q).frame.2 : ℝ) := by
  obtain ⟨mx, my, mf, mg⟩ := step_meaning c d e q
  exact ⟨mx ▸ positionStep.1.sound h hpx, my ▸ positionStep.2.sound h hpy,
    mf ▸ frameStep.1.sound h hfx, mg ▸ frameStep.2.sound h hfy⟩

def fixtureState : Numerical.State := ⟨(1/8, -1/8), (1/2, -1/4)⟩
def fixtureControl : Numerical.Input := .move (-1/2, 1/4)
def fixtureScalar : Variable → Scalar
  | .px => ⟨32, by norm_num, by norm_num⟩
  | .py => ⟨-32, by norm_num, by norm_num⟩
  | .fx => ⟨128, by norm_num, by norm_num⟩
  | .fy => ⟨-64, by norm_num, by norm_num⟩
  | .vx => ⟨-128, by norm_num, by norm_num⟩
  | .vy => ⟨64, by norm_num, by norm_num⟩
  | .angular => ⟨0, by norm_num, by norm_num⟩
  | .duration => ⟨16, by norm_num, by norm_num⟩
  | .error => ⟨1, by norm_num, by norm_num⟩
def fixtureEnv (i : Variable) : Box := singleton (fixtureScalar i)

theorem fixture_related : ∀ i, Contains (fixtureEnv i)
    (exactEnv fixtureControl (1/16) (1/256) fixtureState i) := by
  intro i
  cases i <;> norm_num [Contains, fixtureEnv, singleton, fixtureScalar, Scalar.decode,
    exactEnv, fixtureControl, fixtureState, Numerical.Input.velocity, Numerical.Input.angular]

def fixturePX : Box := ⟨⟨29, by norm_num, by norm_num⟩,
  ⟨29, by norm_num, by norm_num⟩, ⟨29, by norm_num, by norm_num⟩, by decide, by decide⟩
def fixturePY : Box := ⟨⟨-28, by norm_num, by norm_num⟩,
  ⟨-28, by norm_num, by norm_num⟩, ⟨-28, by norm_num, by norm_num⟩, by decide, by decide⟩
def fixtureFX : Box := ⟨⟨128, by norm_num, by norm_num⟩,
  ⟨128, by norm_num, by norm_num⟩, ⟨129, by norm_num, by norm_num⟩, by decide, by decide⟩
def fixtureFY : Box := ⟨⟨-65, by norm_num, by norm_num⟩,
  ⟨-65, by norm_num, by norm_num⟩, ⟨-64, by norm_num, by norm_num⟩, by decide, by decide⟩
def fixtureBudget : Box := ⟨⟨40, by norm_num, by norm_num⟩,
  ⟨40, by norm_num, by norm_num⟩, ⟨41, by norm_num, by norm_num⟩, by decide, by decide⟩

example : positionStep.1.run fixtureEnv = some fixturePX := by decide
example : positionStep.2.run fixtureEnv = some fixturePY := by decide
example : frameStep.1.run fixtureEnv = some fixtureFX := by decide
example : frameStep.2.run fixtureEnv = some fixtureFY := by decide
example : budget.run fixtureEnv = some fixtureBudget := by decide

/-- A nonzero position and signed frame/control exercise the separated denominator. -/
theorem fixture_step :
    Contains fixturePX ((Numerical.step fixtureControl (1/16) fixtureState).position.1 : ℝ) ∧
    Contains fixturePY ((Numerical.step fixtureControl (1/16) fixtureState).position.2 : ℝ) ∧
    Contains fixtureFX ((Numerical.step fixtureControl (1/16) fixtureState).frame.1 : ℝ) ∧
    Contains fixtureFY ((Numerical.step fixtureControl (1/16) fixtureState).frame.2 : ℝ) :=
  step_enclosure fixture_related (by decide) (by decide) (by decide) (by decide)

theorem fixture_budget : Contains fixtureBudget
    (Numerical.budget (1/16) (1/256) : ℝ) := by
  rw [← budget_meaning fixtureControl (1/16) (1/256) fixtureState]
  exact budget.sound fixture_related (by decide)

/-- Admission executes the arithmetic and requires its entire enclosure below the bound. -/
def checkBelow (env : Variable → Box) (expr : E) (threshold : Scalar) : Bool :=
  match expr.run env with
  | none => false
  | some b => below b threshold

theorem checkBelow_sound {env : Variable → Box} {exact : Variable → ℝ}
    (he : ∀ i, Contains (env i) (exact i)) {expr : E} {threshold : Scalar}
    (h : checkBelow env expr threshold = true) : expr.meaning exact ≤ threshold.decode := by
  unfold checkBelow at h
  cases hb : expr.run env with
  | none => simp [hb] at h
  | some b => exact below_sound (by simpa [hb] using h) (expr.sound he hb)

def zeroScalar : Scalar := ⟨0, by norm_num, by norm_num⟩
def halfScalar : Scalar := ⟨128, by norm_num, by norm_num⟩
def quarterScalar : Scalar := ⟨64, by norm_num, by norm_num⟩
def positionMargin : E := .add
  (.add (.add (.absolute position.1) (.absolute position.2)) (.input .error))
  (.divide (.input .duration) two)

def admitted (env : Variable → Box) : Bool :=
  checkBelow env (normSq control) Examples.one &&
  checkBelow env (.absolute (.input .angular)) Examples.one &&
  checkBelow env (.neg (.input .error)) zeroScalar &&
  checkBelow env positionMargin halfScalar &&
  checkBelow env (normSq frame) Examples.one &&
  checkBelow env (normSq positionStep) quarterScalar &&
  checkBelow env (normSq frameStep) Examples.one

/-- Conservative bounded tests imply every predicate of the existing rational admission. -/
theorem admitted_sound {env : Variable → Box}
    (c : Numerical.Tick) (q : Numerical.Packet)
    (he : ∀ i, Contains (env i) (exactEnv c.control c.duration q.error q.state i))
    (h : admitted env = true) : Numerical.Admissible c q := by
  simp only [admitted, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hv, ho⟩, he0⟩, hz⟩, hf⟩, hp⟩, hg⟩ := h
  have hv' := checkBelow_sound he hv
  have ho' := checkBelow_sound he ho
  have he' := checkBelow_sound he he0
  have hz' := checkBelow_sound he hz
  have hf' := checkBelow_sound he hf
  have hp' := checkBelow_sound he hp
  have hg' := checkBelow_sound he hg
  obtain ⟨mx, my, mf, mg⟩ := step_meaning c.control c.duration q.error q.state
  simp only [normSq, Expr.meaning] at hp' hg'
  rw [mx, my] at hp'
  rw [mf, mg] at hg'
  norm_num [normSq, control, frame, positionMargin, position, two, constant,
    Expr.meaning, exactEnv, Examples.one, zeroScalar, halfScalar, quarterScalar,
    Scalar.decode] at hv' ho' he' hz' hf' hp' hg'
  unfold Numerical.Admissible
  constructor
  · simpa [Numerical.QComplex.normSq, pow_two] using
      (show c.control.velocity.1*c.control.velocity.1 + c.control.velocity.2*c.control.velocity.2 ≤ 1 by exact_mod_cast hv')
  constructor
  · rw [← Numerical.Input.decode_angular] at ho'
    exact_mod_cast ho'
  constructor
  · exact_mod_cast he'
  constructor
  · simpa [Numerical.QComplex.size] using
      (show |q.state.position.1| + |q.state.position.2| + q.error + c.duration/2 ≤ 1/2 by
        apply (Rat.cast_le (K := ℝ)).mp
        push_cast
        exact hz')
  constructor
  · simpa [Numerical.QComplex.normSq, pow_two] using
      (show q.state.frame.1*q.state.frame.1 + q.state.frame.2*q.state.frame.2 ≤ 1 by exact_mod_cast hf')
  constructor
  · simpa [Numerical.advance, Numerical.QComplex.normSq, pow_two] using
      (show (Numerical.step c.control c.duration q.state).position.1 *
        (Numerical.step c.control c.duration q.state).position.1 +
        (Numerical.step c.control c.duration q.state).position.2 *
        (Numerical.step c.control c.duration q.state).position.2 ≤ 1/4 by
          apply (Rat.cast_le (K := ℝ)).mp
          push_cast
          exact hp')
  · simpa [Numerical.advance, Numerical.QComplex.normSq, pow_two] using
      (show (Numerical.step c.control c.duration q.state).frame.1 *
        (Numerical.step c.control c.duration q.state).frame.1 +
        (Numerical.step c.control c.duration q.state).frame.2 *
        (Numerical.step c.control c.duration q.state).frame.2 ≤ 1 by exact_mod_cast hg')

example : admitted fixtureEnv = true := by decide

def uncertainMargin (i : Variable) : Box :=
  match i with
  | .px => ⟨⟨118, by norm_num, by norm_num⟩, ⟨118, by norm_num, by norm_num⟩,
      ⟨120, by norm_num, by norm_num⟩, by decide, by decide⟩
  | .py => singleton zeroScalar
  | _ => fixtureEnv i

/-- The center passes the position margin, but its uncertain upper endpoint does not. -/
example : positionMargin.meaning (fun i => (uncertainMargin i).value.decode) < 1/2 := by
  norm_num [positionMargin, position, Expr.meaning, uncertainMargin, fixtureEnv,
    fixtureScalar, singleton, zeroScalar, two, constant, Scalar.decode]
example : checkBelow uncertainMargin positionMargin halfScalar = false := by decide
example : admitted uncertainMargin = false := by decide

theorem fixture_frame_error :
    |fixtureFX.value.decode - (1997/3968)| ≤ 1/256 ∧
    |fixtureFY.value.decode - (-1001/3968)| ≤ 1/256 := by
  have hx := certificate_sound fixture_step.2.2.1
  have hy := certificate_sound fixture_step.2.2.2
  norm_num [Numerical.step, Numerical.field, fixtureControl, fixtureState,
    Numerical.Input.velocity, Numerical.Input.angular, Numerical.QComplex.add,
    Numerical.QComplex.mul, Numerical.QComplex.scale, Numerical.QComplex.conj,
    Numerical.QComplex.turn, Numerical.QComplex.normSq, Box.radius, fixtureFX, fixtureFY] at hx hy
  constructor
  · exact hx
  · convert hy using 1
    norm_num [fixtureFY, Scalar.decode]

#eval Examples.observe (positionStep.1.run fixtureEnv)
#eval Examples.observe (positionStep.2.run fixtureEnv)
#eval Examples.observe (frameStep.1.run fixtureEnv)
#eval Examples.observe (frameStep.2.run fixtureEnv)
#eval Examples.observe (budget.run fixtureEnv)
#eval admitted fixtureEnv
#eval admitted uncertainMargin

#eval show IO Unit from do
  let values := [Examples.observe (positionStep.1.run fixtureEnv),
    Examples.observe (positionStep.2.run fixtureEnv),
    Examples.observe (frameStep.1.run fixtureEnv),
    Examples.observe (frameStep.2.run fixtureEnv), Examples.observe (budget.run fixtureEnv)]
  let expected : List (Option (ℤ × ℤ × ℤ)) :=
    [some (29,29,29), some (-28,-28,-28), some (128,128,129),
      some (-65,-65,-64), some (40,40,41)]
  if values != expected || !admitted fixtureEnv || admitted uncertainMargin then
    throw (IO.userError "bounded motion runtime checks failed")
  IO.println "bounded motion runtime checks passed"

end BoundedArithmetic.Motion
