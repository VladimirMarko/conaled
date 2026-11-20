import Applications.Resources.Measured
import Applications.Numerals.PositivePaths.Length

/-!
# Actual measured positive-path reconstruction

The coordinates count entered recursive calls (including the terminal one)
and constructed branch wrappers. Fixed input values and the public reverse
wrapper have zero additional tariff. These declared source events do not
include arithmetic, parsing, conversion, printing or physical allocation.
Forward append consumes the returned child; reverseAppend constructs its
actual accumulator before entering the next call.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositivePaths

open Numerals.PositiveArithmetic

abbrev Cost := Nat × Nat

def appendRun : PosNum → PosNum → Measured PosNum Cost
  | .one, q => (q, (1, 0))
  | .bit0 p, q =>
      bind ((), (1, 0)) (fun _ =>
        bind (appendRun p q) (fun result => (.bit0 result, (0, 1))))
  | .bit1 p, q =>
      bind ((), (1, 0)) (fun _ =>
        bind (appendRun p q) (fun result => (.bit1 result, (0, 1))))

theorem appendRun_value (p q : PosNum) :
    (appendRun p q).1 = Numerals.PositivePaths.append p q := by
  induction p <;> simp_all only [appendRun, bind_value, Numerals.PositivePaths.append]

theorem appendRun_calls (p q : PosNum) : (appendRun p q).2.1 = bitLength p := by
  induction p <;>
    simp_all only [appendRun, bind, Prod.fst_add, bitLength_one, bitLength_bit0,
      bitLength_bit1, Nat.zero_add, Nat.add_comm]

theorem appendRun_branches_add (p q : PosNum) :
    (appendRun p q).2.2 + 1 = bitLength p := by
  induction p with
  | one => rfl
  | bit0 p ih =>
      simp only [appendRun, bind, Prod.snd_add, Nat.zero_add, bitLength_bit0]
      omega
  | bit1 p ih =>
      simp only [appendRun, bind, Prod.snd_add, Nat.zero_add, bitLength_bit1]
      omega

theorem appendRun_cost (p q : PosNum) :
    (appendRun p q).2 = (bitLength p, bitLength p - 1) := by
  apply Prod.ext
  · exact appendRun_calls p q
  · have h := appendRun_branches_add p q
    omega

def reverseAppendRun : PosNum → PosNum → Measured PosNum Cost
  | .one, q => (q, (1, 0))
  | .bit0 p, q => bind ((), (1, 1)) (fun _ => reverseAppendRun p (.bit0 q))
  | .bit1 p, q => bind ((), (1, 1)) (fun _ => reverseAppendRun p (.bit1 q))

theorem reverseAppendRun_value (p q : PosNum) :
    (reverseAppendRun p q).1 = Numerals.PositivePaths.reverseAppend p q := by
  induction p generalizing q <;>
    simp_all only [reverseAppendRun, bind_value, Numerals.PositivePaths.reverseAppend]

theorem reverseAppendRun_calls (p q : PosNum) :
    (reverseAppendRun p q).2.1 = bitLength p := by
  induction p generalizing q <;>
    simp_all only [reverseAppendRun, bind, Prod.fst_add, bitLength_one,
      bitLength_bit0, bitLength_bit1, Nat.add_comm]

theorem reverseAppendRun_branches_add (p q : PosNum) :
    (reverseAppendRun p q).2.2 + 1 = bitLength p := by
  induction p generalizing q with
  | one => rfl
  | bit0 p ih =>
      have h := ih (.bit0 q)
      simp only [reverseAppendRun, bind, Prod.snd_add, bitLength_bit0]
      omega
  | bit1 p ih =>
      have h := ih (.bit1 q)
      simp only [reverseAppendRun, bind, Prod.snd_add, bitLength_bit1]
      omega

theorem reverseAppendRun_cost (p q : PosNum) :
    (reverseAppendRun p q).2 = (bitLength p, bitLength p - 1) := by
  apply Prod.ext
  · exact reverseAppendRun_calls p q
  · have h := reverseAppendRun_branches_add p q
    omega

def reverseRun (p : PosNum) : Measured PosNum Cost := reverseAppendRun p .one

theorem reverseRun_value (p : PosNum) :
    (reverseRun p).1 = Numerals.PositivePaths.reverse p := reverseAppendRun_value p .one

theorem reverseRun_cost (p : PosNum) :
    (reverseRun p).2 = (bitLength p, bitLength p - 1) := reverseAppendRun_cost p .one

end Resources.PositivePaths
