import Applications.Numerals.PositiveKeys

/-!
# Positive keys as paths

Low-bit-first trie paths have a lexicographic order different from the existing
numeric order on `PosNum`. Keep that relation explicit. Appending paths and
reversing a stored prefix support both finite-trie traversal conventions.

The source equations correspond to `PositiveOrderedTypeBits`, `FMapPositive`
and `FSetPositive` from Rocq Stdlib at `fda356e01346f7766b282ef9f44080cce2be23b3`.
Upstream copyright INRIA, CNRS and contributors; GNU LGPL version 2.1.
The source attribution and notice are retained in `docs/research/rocq-stdlib-notice.md`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Numerals.PositivePaths

/-- Low bits are compared first, with `bit0 < one < bit1`. -/
def BitLt : PosNum → PosNum → Prop
  | .one, .bit1 _ => True
  | .one, _ => False
  | .bit0 p, .bit0 q => BitLt p q
  | .bit0 _, _ => True
  | .bit1 p, .bit1 q => BitLt p q
  | .bit1 _, _ => False

@[simp] theorem bitLt_bit0_bit0 (p q : PosNum) :
    BitLt (.bit0 p) (.bit0 q) ↔ BitLt p q := Iff.rfl

@[simp] theorem bitLt_bit1_bit1 (p q : PosNum) :
    BitLt (.bit1 p) (.bit1 q) ↔ BitLt p q := Iff.rfl

theorem bitLt_irrefl (p : PosNum) : ¬ BitLt p p := by
  induction p <;> simp_all [BitLt]

theorem bitLt_trans {p q r : PosNum} (hpq : BitLt p q) (hqr : BitLt q r) :
    BitLt p r := by
  induction p generalizing q r with
  | one => cases q <;> cases r <;> simp_all [BitLt]
  | bit0 p ih =>
      cases q <;> cases r <;> simp_all [BitLt]
      exact ih hpq hqr
  | bit1 p ih =>
      cases q <;> cases r <;> simp_all [BitLt]
      exact ih hpq hqr

theorem bitLt_asymm {p q : PosNum} (hpq : BitLt p q) : ¬ BitLt q p :=
  fun hqp => bitLt_irrefl p (bitLt_trans hpq hqp)

theorem bitLt_ne {p q : PosNum} (hpq : BitLt p q) : p ≠ q := by
  intro h
  subst q
  exact bitLt_irrefl p hpq

/-- Source equality is ordinary key equality, independently of either order. -/
theorem bitLt_congr {p p' q q' : PosNum} (hp : p = p') (hq : q = q') :
    BitLt p q ↔ BitLt p' q' := by
  subst p'
  subst q'
  rfl

/-- Replace the terminal `one` of the first path by the second path. -/
def append : PosNum → PosNum → PosNum
  | .one, q => q
  | .bit0 p, q => .bit0 (append p q)
  | .bit1 p, q => .bit1 (append p q)

@[simp] theorem append_one_left (q : PosNum) : append .one q = q := rfl

@[simp] theorem append_one_right (p : PosNum) : append p .one = p := by
  induction p <;> simp_all [append]

theorem append_assoc (p q r : PosNum) :
    append (append p q) r = append p (append q r) := by
  induction p <;> simp_all [append]

theorem append_injective (p : PosNum) : Function.Injective (append p) := by
  induction p with
  | one => exact fun _ _ h => h
  | bit0 p ih => exact fun _ _ h => ih (PosNum.bit0.inj h)
  | bit1 p ih => exact fun _ _ h => ih (PosNum.bit1.inj h)

theorem append_bit0 (p q : PosNum) :
    append (append p (.bit0 .one)) q = append p (.bit0 q) := by
  rw [append_assoc]
  rfl

theorem append_bit1 (p q : PosNum) :
    append (append p (.bit1 .one)) q = append p (.bit1 q) := by
  rw [append_assoc]
  rfl

/-- A fixed prefix preserves and reflects the explicit bit order. -/
theorem bitLt_append_iff (pathPrefix p q : PosNum) :
    BitLt (append pathPrefix p) (append pathPrefix q) ↔ BitLt p q := by
  induction pathPrefix <;> simp_all [append]

/-- Reverse the first path onto an accumulator, as in the set provider. -/
def reverseAppend : PosNum → PosNum → PosNum
  | .one, q => q
  | .bit0 p, q => reverseAppend p (.bit0 q)
  | .bit1 p, q => reverseAppend p (.bit1 q)

def reverse (p : PosNum) : PosNum := reverseAppend p .one

theorem reverseAppend_eq (p q : PosNum) :
    reverseAppend p q = append (reverse p) q := by
  induction p generalizing q with
  | one => rfl
  | bit0 p ih =>
      change reverseAppend p (.bit0 q) = append (reverseAppend p (.bit0 .one)) q
      rw [ih, ih, append_bit0]
  | bit1 p ih =>
      change reverseAppend p (.bit1 q) = append (reverseAppend p (.bit1 .one)) q
      rw [ih, ih, append_bit1]

@[simp] theorem reverse_one : reverse .one = .one := rfl

theorem reverse_bit0 (p : PosNum) :
    reverse (.bit0 p) = append (reverse p) (.bit0 .one) :=
  reverseAppend_eq p (.bit0 .one)

theorem reverse_bit1 (p : PosNum) :
    reverse (.bit1 p) = append (reverse p) (.bit1 .one) :=
  reverseAppend_eq p (.bit1 .one)

theorem reverse_append (p q : PosNum) :
    reverse (append p q) = append (reverse q) (reverse p) := by
  induction p with
  | one => simp
  | bit0 p ih => simp only [append, reverse_bit0, ih, append_assoc]
  | bit1 p ih => simp only [append, reverse_bit1, ih, append_assoc]

@[simp] theorem reverse_reverse (p : PosNum) : reverse (reverse p) = p := by
  induction p with
  | one => rfl
  | bit0 p ih => rw [reverse_bit0, reverse_append, reverse_bit0, reverse_one, ih]; rfl
  | bit1 p ih => rw [reverse_bit1, reverse_append, reverse_bit1, reverse_one, ih]; rfl

theorem reverse_injective : Function.Injective reverse := by
  intro p q h
  simpa only [reverse_reverse] using congrArg reverse h

end Numerals.PositivePaths
