import Applications.Orbifold.NumericalBounds
import Applications.Orbifold.CommandComparison

/-! Exact rational Euler arithmetic for disk position and the frame at `1`.
These coordinate pairs are not normalized poses. -/
namespace Orbifold.DiskTransport.Numerical
open DiskConnection

abbrev QComplex := ℚ × ℚ

namespace QComplex
def add (x y : QComplex) : QComplex := (x.1+y.1, x.2+y.2)
def mul (x y : QComplex) : QComplex := (x.1*y.1-x.2*y.2, x.1*y.2+x.2*y.1)
def scale (a : ℚ) (x : QComplex) : QComplex := (a*x.1, a*x.2)
def conj (x : QComplex) : QComplex := (x.1, -x.2)
def turn (x : QComplex) : QComplex := (-x.2, x.1)
def normSq (x : QComplex) : ℚ := x.1^2+x.2^2
def size (x : QComplex) : ℚ := |x.1|+|x.2|
noncomputable def decode (x : QComplex) : ℂ := ⟨x.1, x.2⟩

@[simp] theorem decode_add (x y : QComplex) : decode (add x y) = decode x + decode y := by
  apply Complex.ext <;> simp [decode, add]
@[simp] theorem decode_mul (x y : QComplex) : decode (mul x y) = decode x * decode y := by
  apply Complex.ext <;> simp [decode, mul, Complex.mul_re, Complex.mul_im]
@[simp] theorem decode_scale (a : ℚ) (x : QComplex) :
    decode (scale a x) = (a : ℂ) * decode x := by
  apply Complex.ext <;> simp [decode, scale, Complex.mul_re, Complex.mul_im]
@[simp] theorem decode_conj (x : QComplex) : decode (conj x) = star (decode x) := by
  apply Complex.ext <;> simp [decode, conj]
@[simp] theorem decode_turn (x : QComplex) : decode (turn x) = Complex.I * decode x := by
  apply Complex.ext <;> simp [decode, turn, Complex.mul_re, Complex.mul_im]
@[simp] theorem decode_normSq (x : QComplex) : (normSq x : ℝ) = Complex.normSq (decode x) := by
  simp [normSq, decode, Complex.normSq_apply, pow_two]

theorem decode_injective : Function.Injective decode := by
  intro x y h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  change (x.1 : ℝ) = y.1 at hr
  change (x.2 : ℝ) = y.2 at hi
  apply Prod.ext
  · exact_mod_cast hr
  · exact_mod_cast hi

theorem norm_decode_le_size (x : QComplex) : ‖decode x‖ ≤ (size x : ℝ) := by
  simpa [decode, size] using Complex.norm_le_abs_re_add_abs_im (decode x)

end QComplex

structure State where
  position : QComplex
  frame : QComplex
  deriving DecidableEq, Repr

noncomputable def State.decode (q : State) : ℂ × ℂ :=
  (q.position.decode, q.frame.decode)

inductive Input where
  | move (v : QComplex)
  | turn (omega : ℚ)
  | hold
  deriving DecidableEq, Repr

def Input.velocity : Input → QComplex
  | .move v => v
  | _ => (0,0)
def Input.angular : Input → ℚ
  | .turn omega => omega
  | _ => 0
noncomputable def Input.decode : Input → Control
  | .move v => .move v.decode
  | .turn omega => .turn omega
  | .hold => .hold

@[simp] theorem Input.decode_velocity (c : Input) : c.velocity.decode = c.decode.velocity := by
  cases c <;> apply Complex.ext <;> simp [Input.velocity, Input.decode, Control.velocity, QComplex.decode]
@[simp] theorem Input.decode_angular (c : Input) : (c.angular : ℝ) = c.decode.angularVelocity := by
  cases c <;> simp [Input.angular, Input.decode, Control.angularVelocity]

def field (c : Input) (q : State) : State :=
  let velocity := QComplex.mul q.frame c.velocity
  ⟨velocity, QComplex.add
    (QComplex.scale (-2 / (1 - q.position.normSq))
      (QComplex.mul (QComplex.mul q.position.conj velocity) q.frame))
    (QComplex.scale c.angular q.frame.turn)⟩

def step (c : Input) (d : ℚ) (q : State) : State :=
  let f := field c q
  ⟨q.position.add (f.position.scale d), q.frame.add (f.frame.scale d)⟩

theorem field_decode (c : Input) (q : State) :
    (field c q).decode = motionField c.decode.velocity c.decode.angularVelocity q.decode := by
  apply Prod.ext
  · simp [field, State.decode, motionField]
  · simp only [field, State.decode, QComplex.decode_add, QComplex.decode_scale,
      QComplex.decode_mul, QComplex.decode_conj, QComplex.decode_turn,
      Input.decode_velocity, motionField, coefficient, gap]
    have hn : (q.position.normSq : ℂ) = (Complex.normSq q.position.decode : ℂ) := by
      exact_mod_cast QComplex.decode_normSq q.position
    push_cast
    rw [hn]
    rw [show (c.angular : ℂ) = (c.decode.angularVelocity : ℂ) by exact_mod_cast c.decode_angular]
    simp only [starRingEnd_apply]
    ring

/-- The implemented rational arithmetic is exactly the real Euler method. -/
theorem step_decode (c : Input) (d : ℚ) (q : State) :
    (step c d q).decode = q.decode + (d : ℝ) •
      motionField c.decode.velocity c.decode.angularVelocity q.decode := by
  rw [← field_decode]
  apply Prod.ext <;> simp [step, State.decode, Complex.real_smul]

@[simp] theorem step_zero (c : Input) (q : State) : step c 0 q = q := by
  cases q
  simp [step, QComplex.add, QComplex.scale]

@[simp] theorem step_hold (d : ℚ) (q : State) : step .hold d q = q := by
  cases q
  simp [step, field, Input.velocity, Input.angular, QComplex.add, QComplex.mul,
    QComplex.scale, QComplex.turn]

/-- A nonzero move from the origin checks both independent coordinate updates. -/
example : step (.move (1,0)) (1/8) ⟨(0,0),(1/2,0)⟩ = ⟨(1/16,0),(1/2,0)⟩ := by
  norm_num [step, field, Input.velocity, Input.angular, QComplex.add, QComplex.mul,
    QComplex.scale, QComplex.conj, QComplex.normSq, QComplex.turn]

end Orbifold.DiskTransport.Numerical
