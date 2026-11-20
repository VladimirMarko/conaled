import Applications.Resources.PositiveArithmetic
import Mathlib.Logic.Function.Iterate

/-!
# Connected positive arithmetic work cases

The terminal one separates visits from changed-digit writes. Terminal addition
cases in both orientations require the successor work on the remaining operand.
Carry chains and equal-length comparison families attain the universal bounds;
comparison with one stops immediately even for arbitrarily long other keys.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PositiveArithmeticWork

open Numerals.PositiveKeys Numerals.PositiveArithmetic Resources.PositiveArithmetic

theorem one_has_two_observations :
    succVisitRun .one = ((2 : PosNum), 1) ∧ succWriteRun .one = ((2 : PosNum), 2) :=
  ⟨succVisitRun_one, succWriteRun_one⟩

theorem seven_carries_to_eight : succRun (7 : PosNum) = ((8 : PosNum), (3, 4)) := by
  change succRun (.bit1 (.bit1 .one)) = _
  rw [succRun_bit1, succRun_bit1, succRun_one]
  rfl

theorem ten_stops_at_low_zero : succRun (10 : PosNum) = ((11 : PosNum), (1, 1)) :=
  succRun_bit0 (.bit1 (.bit0 .one))

theorem terminal_left_charges_successor : addcRun false (1 : PosNum) 7 = ((8 : PosNum), 3) := by
  change addcRun false .one (.bit1 (.bit1 .one)) = _
  rw [addcRun_false_one_bit1, succVisitRun_bit1, succVisitRun_one]
  rfl

theorem terminal_right_charges_successor : addcRun false (7 : PosNum) 1 = ((8 : PosNum), 3) := by
  change addcRun false (.bit1 (.bit1 .one)) .one = _
  rw [addcRun_false_bit1_one, succVisitRun_bit1, succVisitRun_one]
  rfl

theorem carry_left_even_terminal : addcRun true (1 : PosNum) 6 = ((8 : PosNum), 3) := by
  change addcRun true .one (.bit0 (.bit1 .one)) = _
  rw [addcRun_true_one_bit0, succVisitRun_bit1, succVisitRun_one]
  rfl

theorem carry_right_even_terminal : addcRun true (6 : PosNum) 1 = ((8 : PosNum), 3) := by
  change addcRun true (.bit0 (.bit1 .one)) .one = _
  rw [addcRun_true_bit0_one, succVisitRun_bit1, succVisitRun_one]
  rfl

theorem unequal_no_carry : addcRun false (3 : PosNum) 8 = ((11 : PosNum), 2) := by
  change addcRun false (.bit1 .one) (.bit0 (.bit0 (.bit0 .one))) = _
  rw [addcRun_false_bit1_bit0, addcRun_false_one_bit0]
  rfl

theorem unequal_with_carry : addcRun true (3 : PosNum) 8 = ((12 : PosNum), 3) := by
  change addcRun true (.bit1 .one) (.bit0 (.bit0 (.bit0 .one))) = _
  rw [addcRun_true_bit1_bit0, addcRun_true_one_bit0, succVisitRun_bit0]
  rfl

theorem double_terminal_cases :
    addcRun false .one .one = ((2 : PosNum), 1) ∧
      addcRun true .one .one = ((3 : PosNum), 1) :=
  ⟨addcRun_false_one_one, addcRun_true_one_one⟩

/-- Both carries and every raw positive input retain the independent numeric sum. -/
theorem measured_carry_numeric (c : Bool) (p q : PosNum) :
    numeric (addcRun c p q).1 = (if c then 1 else 0) + numeric p + numeric q := by
  rw [addcRun_value]
  exact addc_correct c p q

theorem terminal_bound_is_attained :
    (addcRun false (1 : PosNum) 7).2 = max (bitLength (1 : PosNum)) (bitLength (7 : PosNum)) := by
  rw [terminal_left_charges_successor]
  rfl

theorem unequal_bound_has_slack :
    (addcRun false (3 : PosNum) 8).2 < max (bitLength (3 : PosNum)) (bitLength (8 : PosNum)) := by
  rw [unequal_no_carry]
  decide

theorem measured_result_log_bound (c : Bool) (p q : PosNum) :
    (addcRun c p q).2 ≤ Nat.log 2 ((if c then 1 else 0) + numeric p + numeric q) + 1 := by
  simpa only [measured_carry_numeric] using addcRun_cost_log_result c p q

theorem higher_bits_override_low_one : cmpRun (3 : PosNum) 4 = (.lt, 2) := by
  change cmpRun (.bit1 .one) (.bit0 (.bit0 .one)) = _
  rw [cmpRun_bit1_bit0, cmpRun_one_bit0]
  rfl

theorem higher_bits_override_low_zero : cmpRun (4 : PosNum) 3 = (.gt, 2) := by
  change cmpRun (.bit0 (.bit0 .one)) (.bit1 .one) = _
  rw [cmpRun_bit0_bit1, cmpRun_bit0_one]
  rfl

theorem measured_comparison_equal_keys (p q : PosNum) :
    (cmpRun p q).1 = .eq ↔ p = q := by
  rw [cmpRun_value]
  exact cmp_eq_iff p q

/-- Existing constructors generate the positive carry-chain family. -/
abbrev allOnes (n : Nat) : PosNum := PosNum.bit1^[n] .one

/-- Exactly n low zero bits followed by the terminal one. -/
abbrev powerKey (n : Nat) : PosNum := PosNum.bit0^[n] .one

theorem allOnes_succ (n : Nat) : allOnes (n + 1) = .bit1 (allOnes n) :=
  Function.iterate_succ_apply' PosNum.bit1 n .one

theorem powerKey_succ (n : Nat) : powerKey (n + 1) = .bit0 (powerKey n) :=
  Function.iterate_succ_apply' PosNum.bit0 n .one

theorem allOnes_bitLength (n : Nat) : bitLength (allOnes n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [allOnes_succ, bitLength_bit1, ih]

theorem powerKey_numeric (n : Nat) : numeric (powerKey n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [powerKey_succ, numeric_bit0, Nat.zero_add, ih, Nat.pow_succ, Nat.mul_comm]

theorem powerKey_bitLength (n : Nat) : bitLength (powerKey n) = n + 1 :=
  bitLength_of_numeric_eq_pow (powerKey n) n (powerKey_numeric n)

/-- Every recursive measured result supplies the next constructor of the power. -/
theorem carry_chain_run (n : Nat) :
    succRun (allOnes n) = (powerKey (n + 1), (n + 1, n + 2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allOnes_succ, succRun_bit1, ih, powerKey_succ (n + 1)]
    simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem carry_chain_visits (n : Nat) : (succVisitRun (allOnes n)).2 = n + 1 := by
  change (succRun (allOnes n)).2.1 = _
  rw [carry_chain_run]

theorem carry_chain_writes (n : Nat) : (succWriteRun (allOnes n)).2 = n + 2 := by
  change (succRun (allOnes n)).2.2 = _
  rw [carry_chain_run]

theorem carry_chain_attains_visit_bound (n : Nat) :
    (succVisitRun (allOnes n)).2 = bitLength (allOnes n) := by
  rw [carry_chain_visits, allOnes_bitLength]

theorem carry_chain_attains_write_bound (n : Nat) :
    (succWriteRun (allOnes n)).2 = bitLength (allOnes n) + 1 := by
  rw [carry_chain_writes, allOnes_bitLength]

theorem equal_length_comparison_family (n : Nat) :
    (cmpRun (powerKey n) (allOnes n)).2 = n + 1 := by
  rw [cmpRun_cost, powerKey_bitLength, allOnes_bitLength, min_self]

theorem terminal_comparison_family (n : Nat) :
    cmpRun (powerKey (n + 1)) .one = (.gt, 1) := by
  rw [powerKey_succ, cmpRun_bit0_one]

theorem terminal_comparison_has_strict_slack (n : Nat) :
    (cmpRun (powerKey (n + 1)) .one).2 < bitLength (powerKey (n + 1)) := by
  rw [terminal_comparison_family, powerKey_bitLength]
  omega

end Examples.PositiveArithmeticWork
