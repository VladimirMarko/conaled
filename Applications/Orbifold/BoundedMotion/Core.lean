import Examples.BoundedMotionArithmetic

/-! Stored coordinates for the bounded motion realization. Rational conversion
is an explicit boundary; arithmetic within a step uses fixed-point scalars. -/
namespace Orbifold.DiskTransport.Numerical.Bounded
open BoundedArithmetic

def rational (a : Scalar) : ℚ := a.ticks / 256

@[simp] theorem rational_cast (a : Scalar) : (rational a : ℝ) = a.decode := by
  simp [rational, Scalar.decode]

/-- Import rejects non-grid values rather than changing input coordinates or time. -/
def encode (q : ℚ) : Option Scalar :=
  let n := q.num * 256 / (q.den : ℤ)
  if _h : (n : ℚ) / 256 = q then
    if hl : -65536 ≤ n then
      if hh : n ≤ 65536 then some ⟨n, hl, hh⟩ else none
    else none
  else none

theorem encode_sound {q : ℚ} {a : Scalar} (h : encode q = some a) : rational a = q := by
  dsimp only [encode] at h
  split at h <;> simp_all
  obtain ⟨hl, hh, rfl⟩ := h
  simpa only [rational] using ‹(↑(q.num * 256 / ↑q.den) : ℚ) / 256 = q›

structure State where
  px : Scalar
  py : Scalar
  fx : Scalar
  fy : Scalar
  deriving DecidableEq, Repr

def State.rational (s : State) : Numerical.State :=
  ⟨(Bounded.rational s.px, Bounded.rational s.py),
    (Bounded.rational s.fx, Bounded.rational s.fy)⟩

structure Packet where
  state : State
  error : Scalar
  deriving DecidableEq, Repr

def Packet.rational (q : Packet) : Numerical.Packet :=
  ⟨q.state.rational, Bounded.rational q.error⟩

def importPacket (q : Numerical.Packet) : Option Packet := do
  let px ← encode q.state.position.1
  let py ← encode q.state.position.2
  let fx ← encode q.state.frame.1
  let fy ← encode q.state.frame.2
  let e ← encode q.error
  pure ⟨⟨px, py, fx, fy⟩, e⟩

theorem importPacket_sound {q : Numerical.Packet} {p : Packet}
    (h : importPacket q = some p) : p.rational = q := by
  simp only [importPacket, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨px, hpx, py, hpy, fx, hfx, fy, hfy, e, he, rfl⟩ := h
  cases q with
  | mk s err =>
    cases s with
    | mk pos frame =>
      cases pos; cases frame
      simp only [Packet.rational, State.rational, encode_sound hpx,
        encode_sound hpy, encode_sound hfx, encode_sound hfy, encode_sound he]

structure Input where
  vx : Scalar
  vy : Scalar
  angular : Scalar
  duration : Scalar
  deriving DecidableEq, Repr

def importInput (c : Tick) : Option Input := do
  let vx ← encode c.control.velocity.1
  let vy ← encode c.control.velocity.2
  let angular ← encode c.control.angular
  let duration ← encode c.duration
  pure ⟨vx, vy, angular, duration⟩

def inputEnv (c : Input) (q : Packet) : BoundedArithmetic.Motion.Variable → Box
  | .px => singleton q.state.px
  | .py => singleton q.state.py
  | .fx => singleton q.state.fx
  | .fy => singleton q.state.fy
  | .vx => singleton c.vx
  | .vy => singleton c.vy
  | .angular => singleton c.angular
  | .duration => singleton c.duration
  | .error => singleton q.error

theorem inputEnv_sound {c : Tick} {i : Input} (hi : importInput c = some i)
    (q : Packet) : ∀ v, Contains (inputEnv i q v)
      (BoundedArithmetic.Motion.exactEnv c.control c.duration
        (Bounded.rational q.error) q.state.rational v) := by
  simp only [importInput, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hi
  obtain ⟨vx, hvx, vy, hvy, a, ha, d, hd, rfl⟩ := hi
  have vxcast := congrArg (fun r : ℚ => (r : ℝ)) (encode_sound hvx)
  have vycast := congrArg (fun r : ℚ => (r : ℝ)) (encode_sound hvy)
  have acast := congrArg (fun r : ℚ => (r : ℝ)) (encode_sound ha)
  have dcast := congrArg (fun r : ℚ => (r : ℝ)) (encode_sound hd)
  simp only [rational_cast] at vxcast vycast acast dcast
  intro v
  cases v <;> simp only [inputEnv, BoundedArithmetic.Motion.exactEnv, State.rational,
    rational_cast, ← vxcast, ← vycast, ← acast, ← dcast] <;>
    exact singleton_contains _

example : encode (1/512) = none := by norm_num [encode]
example : encode 257 = none := by norm_num [encode]
example : (encode (-1/8)).map Scalar.ticks = some (-32) := by norm_num [encode]

end Orbifold.DiskTransport.Numerical.Bounded
