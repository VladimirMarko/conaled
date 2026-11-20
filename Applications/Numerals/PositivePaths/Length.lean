import Applications.Numerals.PositivePaths
import Applications.Numerals.PositiveArithmetic

/-! Positive path lengths, including the terminal one. These are size laws;
they do not identify the work of forward append and accumulator reversal. -/

set_option autoImplicit false
set_option warningAsError true

namespace Numerals.PositivePaths

open PositiveArithmetic

theorem bitLength_append_add (p q : PosNum) :
    bitLength (append p q) + 1 = bitLength p + bitLength q := by
  induction p with
  | one => simp [append, Nat.add_comm]
  | bit0 p ih => simp only [append, bitLength_bit0]; omega
  | bit1 p ih => simp only [append, bitLength_bit1]; omega

theorem bitLength_reverseAppend_add (p q : PosNum) :
    bitLength (reverseAppend p q) + 1 = bitLength p + bitLength q := by
  induction p generalizing q with
  | one => simp [reverseAppend, Nat.add_comm]
  | bit0 p ih =>
      have h := ih (.bit0 q)
      simp only [reverseAppend, bitLength_bit0] at h ⊢
      omega
  | bit1 p ih =>
      have h := ih (.bit1 q)
      simp only [reverseAppend, bitLength_bit1] at h ⊢
      omega

theorem bitLength_reverse (p : PosNum) : bitLength (reverse p) = bitLength p := by
  have h := bitLength_reverseAppend_add p .one
  simpa only [reverse, bitLength_one, Nat.add_right_cancel_iff] using h

theorem bitLength_le_append (p q : PosNum) : bitLength p ≤ bitLength (append p q) := by
  have h := bitLength_append_add p q
  have positive := bitLength_pos q
  omega

end Numerals.PositivePaths
