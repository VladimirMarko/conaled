import Applications.Resources.PositiveArithmetic
import Applications.Resources.BinaryCounter
import Mathlib.Data.Num.ZNum
import Mathlib.Algebra.Order.Field.Rat

/-!
# Positive and nonnegative binary counters

The accepted low-first digit observation connects the actual measured positive
successor to `BinaryCounter.incWithCost`. All trajectories use `Resources.run`,
and the established bit-counter accounting supplies exact boundary potentials.

The existing `Num` carrier realizes the nonnegative part of the source signed
counter. Its actual zero/positive addition-by-one branches commute with both
Nat and `toZNum` observations. Costs count changed-digit writes. Sign dispatch,
wrapper dispatch and surrounding loop work require separate constant tariffs;
the negative signed-counter branch is outside this realization.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveCounter

open Numerals.PositiveKeys Numerals.PositiveArithmetic Resources.PositiveArithmetic

theorem digits_canonical (p : PosNum) : BinaryCounter.Canonical (digits p) := by
  induction p with
  | one => simp [digits_one, BinaryCounter.Canonical]
  | bit0 p ih =>
    rw [digits_bit0, BinaryCounter.canonical_cons_nonempty false (digits p) (digits_nonempty p)]
    exact ih
  | bit1 p ih =>
    rw [digits_bit1, BinaryCounter.canonical_cons_nonempty true (digits p) (digits_nonempty p)]
    exact ih

theorem digits_value (p : PosNum) : BinaryCounter.value (digits p) = numeric p := by
  induction p with
  | one => rfl
  | bit0 p ih => rw [digits_bit0, BinaryCounter.value, ih, numeric_bit0, Nat.zero_add]
  | bit1 p ih => rw [digits_bit1, BinaryCounter.value, ih, numeric_bit1]

theorem digits_ones_pos (p : PosNum) : 0 < BinaryCounter.ones (digits p) := by
  induction p with
  | one => decide
  | bit0 p ih => simpa only [digits_bit0, BinaryCounter.ones] using ih
  | bit1 p ih => simp only [digits_bit1, BinaryCounter.ones]; omega

theorem digits_succ (p : PosNum) :
    digits (PosNum.succ p) = BinaryCounter.inc (digits p) := by
  induction p with
  | one => simp only [PosNum.succ, digits_bit0, digits_one, BinaryCounter.inc]
  | bit0 p => simp only [PosNum.succ, digits_bit0, digits_bit1, BinaryCounter.inc]
  | bit1 p ih => simp only [PosNum.succ, digits_bit0, digits_bit1, BinaryCounter.inc, ih]

/-- Preserve both the actual output digits and every changed-digit charge. -/
theorem succWriteRun_digits (p : PosNum) :
    (digits (succWriteRun p).1, (succWriteRun p).2) =
      BinaryCounter.incWithCost (digits p) := by
  induction p with
  | one => simp only [succWriteRun_one, digits_bit0, digits_one, BinaryCounter.incWithCost]
  | bit0 p => simp only [succWriteRun_bit0, digits_bit0, digits_bit1, BinaryCounter.incWithCost]
  | bit1 p ih =>
    simpa only [succWriteRun_bit1, digits_bit0, digits_bit1, BinaryCounter.incWithCost] using
      congrArg (fun result : Measured (List Bool) Nat => (false :: result.1, 1 + result.2)) ih

theorem succWriteRun_cost (p : PosNum) :
    (succWriteRun p).2 = BinaryCounter.flipCost (digits p) := by
  have h := congrArg Prod.snd (succWriteRun_digits p)
  simpa only [BinaryCounter.incWithCost_eq] using h

theorem succWriteRun_potential (p : PosNum) :
    (succWriteRun p).2 + BinaryCounter.ones (digits (succWriteRun p).1) =
      BinaryCounter.ones (digits p) + 2 := by
  rw [succWriteRun_cost, succWriteRun_value, digits_succ]
  exact (BinaryCounter.flipCost_potential (digits p)).trans (Nat.add_comm _ _)

/-- Exactly n source successor transitions, through the existing measured executor. -/
def positiveAdvanceRun (n : Nat) (p : PosNum) : Measured PosNum Nat :=
  run (fun (_ : Unit) => succWriteRun) (List.replicate n ()) p

@[simp] theorem positiveAdvanceRun_zero (p : PosNum) : positiveAdvanceRun 0 p = (p, 0) := rfl

theorem positiveAdvanceRun_succ (n : Nat) (p : PosNum) :
    positiveAdvanceRun (n + 1) p = bind (succWriteRun p) (positiveAdvanceRun n) := rfl

theorem positiveAdvanceRun_value (n : Nat) (p : PosNum) :
    (positiveAdvanceRun n p).1 = PosNum.succ^[n] p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [positiveAdvanceRun_succ, bind_value, ih, succWriteRun_value,
      Function.iterate_succ_apply]

theorem positiveAdvanceRun_digits (n : Nat) (p : PosNum) :
    (digits (positiveAdvanceRun n p).1, (positiveAdvanceRun n p).2) =
      BinaryCounter.advanceWithCost n (digits p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simpa only [positiveAdvanceRun_succ, BinaryCounter.advanceWithCost_succ,
      ← succWriteRun_digits, bind] using
      congrArg (fun result : Measured (List Bool) Nat =>
        (result.1, (succWriteRun p).2 + result.2)) (ih (succWriteRun p).1)

theorem positiveAdvanceRun_cost (n : Nat) (p : PosNum) :
    (positiveAdvanceRun n p).2 = BinaryCounter.totalCost n (digits p) := by
  have h := congrArg Prod.snd (positiveAdvanceRun_digits n p)
  simpa only [BinaryCounter.advanceWithCost_eq] using h

theorem positiveAdvanceRun_numeric (n : Nat) (p : PosNum) :
    numeric (positiveAdvanceRun n p).1 = numeric p + n := by
  have h := congrArg (fun result : Measured (List Bool) Nat => BinaryCounter.value result.1)
    (positiveAdvanceRun_digits n p)
  simpa only [BinaryCounter.advanceWithCost_eq, BinaryCounter.value_advance, digits_value] using h

/-- Exact arbitrary-start accounting retains both boundary potentials. -/
theorem positiveAdvanceRun_potential (n : Nat) (p : PosNum) :
    (positiveAdvanceRun n p).2 + BinaryCounter.ones (digits (positiveAdvanceRun n p).1) =
      2 * n + BinaryCounter.ones (digits p) := by
  have h := BinaryCounter.counter_potential n (digits p)
  rw [← positiveAdvanceRun_digits] at h
  exact h.trans (Nat.add_comm _ _)

theorem positiveAdvanceRun_bound (n : Nat) (p : PosNum) :
    (positiveAdvanceRun n p).2 ≤ 2 * n + BinaryCounter.ones (digits p) := by
  have h := positiveAdvanceRun_potential n p
  omega

/-- Initial positive one has potential one, and the final positive still has
at least one one bit, so both boundary terms sharpen the generic bound. -/
theorem positiveAdvanceRun_one_bound (n : Nat) :
    (positiveAdvanceRun n .one).2 ≤ 2 * n := by
  have h := positiveAdvanceRun_potential n .one
  have hp := digits_ones_pos (positiveAdvanceRun n .one).1
  simp only [digits_one, BinaryCounter.ones] at h
  omega

theorem positiveAdvanceRun_one_average (n : Nat) (hn : 0 < n) :
    ((positiveAdvanceRun n .one).2 : ℚ) / (n : ℚ) ≤ 2 := by
  have hnq : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr hn
  apply (div_le_iff₀ hnq).mpr
  have hq : ((positiveAdvanceRun n .one).2 : ℚ) ≤ ((2 * n : Nat) : ℚ) :=
    Nat.cast_le.mpr (positiveAdvanceRun_one_bound n)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hq

/-- The input states before n transitions are exactly the consecutive numeric
values starting at the arbitrary positive initial value. -/
theorem positivePrefix_values (n : Nat) (p : PosNum) :
    (List.iterate PosNum.succ p n).map numeric = List.range' (numeric p) n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [List.iterate, List.map_cons, ih, succ_correct, List.range'_succ]

theorem positivePrefix_one_values (n : Nat) :
    (List.iterate PosNum.succ .one n).map numeric = List.range' 1 n :=
  positivePrefix_values n .one

theorem positiveAdvanceRun_one_numeric (n : Nat) :
    numeric (positiveAdvanceRun n .one).1 = n + 1 := by
  rw [positiveAdvanceRun_numeric, numeric_one, Nat.add_comm]

/-- Observing n states without incrementing the last needs n-1 transitions. -/
theorem positivePrefix_transition_bound (n : Nat) :
    (positiveAdvanceRun (n - 1) .one).2 ≤ 2 * (n - 1) :=
  positiveAdvanceRun_one_bound (n - 1)

/-- Digit observation on the existing nonnegative binary carrier. -/
def numDigits : Num → List Bool
  | .zero => []
  | .pos p => digits p

@[simp] theorem numDigits_zero : numDigits .zero = [] := rfl

@[simp] theorem numDigits_pos (p : PosNum) : numDigits (.pos p) = digits p := rfl

theorem numDigits_canonical (c : Num) : BinaryCounter.Canonical (numDigits c) := by
  cases c with
  | zero => trivial
  | pos p => exact digits_canonical p

theorem numDigits_value (c : Num) : BinaryCounter.value (numDigits c) = (c : Nat) := by
  cases c with
  | zero => rfl
  | pos p => exact digits_value p

theorem numDigits_length (c : Num) : (numDigits c).length = c.natSize := by
  cases c with
  | zero => rfl
  | pos p => exact digits_length p

/-- The actual zero/positive addition-by-one cases, with bit-write charges.
For a positive operand `PosNum.add p 1` calls the inspected successor of p;
this is not the source carry-addition implementation `addcRun`. -/
def numAddOneRun : Num → Measured Num Nat
  | .zero => (.pos .one, 1)
  | .pos p =>
      let result := succWriteRun p
      (.pos result.1, result.2)

@[simp] theorem numAddOneRun_zero : numAddOneRun .zero = (.pos .one, 1) := rfl

@[simp] theorem numAddOneRun_pos (p : PosNum) :
    numAddOneRun (.pos p) = (.pos (succWriteRun p).1, (succWriteRun p).2) := rfl

theorem numAddOneRun_value (c : Num) : (numAddOneRun c).1 = c + 1 := by
  rw [Num.add_one]
  cases c with
  | zero => rfl
  | pos p => change Num.pos (succWriteRun p).1 = Num.pos (PosNum.succ p)
             rw [succWriteRun_value]

theorem numAddOneRun_toNat (c : Num) :
    ((numAddOneRun c).1 : Nat) = (c : Nat) + 1 := by
  rw [numAddOneRun_value, Num.add_to_nat, Num.cast_one]

theorem numAddOneRun_toZNum (c : Num) :
    (numAddOneRun c).1.toZNum = c.toZNum + 1 := by
  rw [numAddOneRun_value, Num.add_one, Num.toZNum_succ, ZNum.add_one]

theorem num_toZNum_nonnegative (c : Num) : 0 ≤ (c.toZNum : Int) := by
  rw [Num.cast_toZNum, ← Num.to_nat_to_int]
  exact Int.natCast_nonneg _

theorem numAddOneRun_nonnegative (c : Num) : 0 ≤ ((numAddOneRun c).1.toZNum : Int) :=
  num_toZNum_nonnegative _

theorem numAddOneRun_digits (c : Num) :
    (numDigits (numAddOneRun c).1, (numAddOneRun c).2) =
      BinaryCounter.incWithCost (numDigits c) := by
  cases c with
  | zero => rfl
  | pos p => exact succWriteRun_digits p

theorem numAddOneRun_cost (c : Num) :
    (numAddOneRun c).2 = BinaryCounter.flipCost (numDigits c) := by
  have h := congrArg Prod.snd (numAddOneRun_digits c)
  simpa only [BinaryCounter.incWithCost_eq] using h

/-- This local law can telescope on sparse duplicate increments in the shared
collision executor, without extracting or executing a second command sequence. -/
theorem numAddOneRun_potential (c : Num) :
    (numAddOneRun c).2 + BinaryCounter.ones (numDigits (numAddOneRun c).1) =
      BinaryCounter.ones (numDigits c) + 2 := by
  have hv := congrArg Prod.fst (numAddOneRun_digits c)
  simp only [BinaryCounter.incWithCost_eq] at hv
  rw [numAddOneRun_cost, hv]
  exact (BinaryCounter.flipCost_potential (numDigits c)).trans (Nat.add_comm _ _)

theorem numAddOneRun_cost_le (c : Num) :
    (numAddOneRun c).2 ≤ (numDigits c).length + 1 := by
  rw [numAddOneRun_cost]
  exact BinaryCounter.flipCost_le_length_add_one _

/-- The same shared executor, now starting at any nonnegative binary state. -/
def numAdvanceRun (n : Nat) (c : Num) : Measured Num Nat :=
  run (fun (_ : Unit) => numAddOneRun) (List.replicate n ()) c

@[simp] theorem numAdvanceRun_zero (c : Num) : numAdvanceRun 0 c = (c, 0) := rfl

theorem numAdvanceRun_succ (n : Nat) (c : Num) :
    numAdvanceRun (n + 1) c = bind (numAddOneRun c) (numAdvanceRun n) := rfl

theorem numAdvanceRun_value (n : Nat) (c : Num) :
    (numAdvanceRun n c).1 = (fun d : Num => d + 1)^[n] c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [numAdvanceRun_succ, bind_value, ih, numAddOneRun_value,
      Function.iterate_succ_apply]

theorem numAdvanceRun_digits (n : Nat) (c : Num) :
    (numDigits (numAdvanceRun n c).1, (numAdvanceRun n c).2) =
      BinaryCounter.advanceWithCost n (numDigits c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simpa only [numAdvanceRun_succ, BinaryCounter.advanceWithCost_succ,
      ← numAddOneRun_digits, bind] using
      congrArg (fun result : Measured (List Bool) Nat =>
        (result.1, (numAddOneRun c).2 + result.2)) (ih (numAddOneRun c).1)

theorem numAdvanceRun_toNat (n : Nat) (c : Num) :
    ((numAdvanceRun n c).1 : Nat) = (c : Nat) + n := by
  have h := congrArg (fun result : Measured (List Bool) Nat => BinaryCounter.value result.1)
    (numAdvanceRun_digits n c)
  simpa only [BinaryCounter.advanceWithCost_eq, BinaryCounter.value_advance, numDigits_value] using h

theorem numAdvanceRun_toZNum (n : Nat) (c : Num) :
    (numAdvanceRun n c).1.toZNum = (fun z : ZNum => z + 1)^[n] c.toZNum := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [numAdvanceRun_succ, bind_value, ih, numAddOneRun_toZNum,
      Function.iterate_succ_apply]

theorem numAdvanceRun_nonnegative (n : Nat) (c : Num) :
    0 ≤ ((numAdvanceRun n c).1.toZNum : Int) := num_toZNum_nonnegative _

theorem numAdvanceRun_cost (n : Nat) (c : Num) :
    (numAdvanceRun n c).2 = BinaryCounter.totalCost n (numDigits c) := by
  have h := congrArg Prod.snd (numAdvanceRun_digits n c)
  simpa only [BinaryCounter.advanceWithCost_eq] using h

theorem numAdvanceRun_potential (n : Nat) (c : Num) :
    (numAdvanceRun n c).2 + BinaryCounter.ones (numDigits (numAdvanceRun n c).1) =
      2 * n + BinaryCounter.ones (numDigits c) := by
  have h := BinaryCounter.counter_potential n (numDigits c)
  rw [← numAdvanceRun_digits] at h
  exact h.trans (Nat.add_comm _ _)

theorem numAdvanceRun_bound (n : Nat) (c : Num) :
    (numAdvanceRun n c).2 ≤ 2 * n + BinaryCounter.ones (numDigits c) := by
  have h := numAdvanceRun_potential n c
  omega

theorem numAdvanceRun_zero_bound (n : Nat) : (numAdvanceRun n .zero).2 ≤ 2 * n := by
  simpa only [numDigits_zero, BinaryCounter.ones, Nat.add_zero] using numAdvanceRun_bound n .zero

theorem numAdvanceRun_zero_toNat (n : Nat) : ((numAdvanceRun n .zero).1 : Nat) = n := by
  exact (numAdvanceRun_toNat n .zero).trans (Nat.zero_add n)

theorem numAdvanceRun_zero_toInt (n : Nat) : ((numAdvanceRun n .zero).1.toZNum : Int) = n := by
  rw [Num.cast_toZNum, ← Num.to_nat_to_int, numAdvanceRun_zero_toNat]

end Resources.PositiveCounter
