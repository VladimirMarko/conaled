import Applications.Resources.PositiveCounter

/-!
# Connected binary-counter accounting

Concrete states and write totals connect the measured source transitions to the
public digit and potential laws. Four transitions differ from four observed
states. A carry-heavy arbitrary start spends initial potential. Sparse optional
increments telescope directly through the shared executor, as required by the
collision client, without executing a second extracted increment sequence.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PositiveCounterWork

open Resources Numerals.PositiveKeys Numerals.PositiveArithmetic
open Resources.PositiveArithmetic Resources.PositiveCounter

theorem ten_digits_and_meaning :
    digits (10 : PosNum) = [false, true, false, true] ∧
      BinaryCounter.value (digits (10 : PosNum)) = 10 ∧
      BinaryCounter.Canonical (digits (10 : PosNum)) ∧
      (digits (10 : PosNum)).length = 4 := by
  refine ⟨rfl, ?_, digits_canonical _, ?_⟩
  · exact digits_value (10 : PosNum)
  · exact digits_length (10 : PosNum)

theorem terminal_write_bridge :
    (digits (succWriteRun .one).1, (succWriteRun .one).2) = ([false, true], 2) := by
  rw [succWriteRun_digits, digits_one]
  rfl

theorem carry_write_bridge :
    (digits (succWriteRun (7 : PosNum)).1, (succWriteRun (7 : PosNum)).2) =
      ([false, false, false, true], 4) := by
  rw [succWriteRun_digits]
  rfl

theorem zero_positive_transitions (p : PosNum) : positiveAdvanceRun 0 p = (p, 0) :=
  positiveAdvanceRun_zero p

theorem positive_four_final : (positiveAdvanceRun 4 .one).1 = (5 : PosNum) := by
  apply numeric_injective
  rw [positiveAdvanceRun_numeric, numeric_one]
  rfl

theorem positive_four_writes : (positiveAdvanceRun 4 .one).2 = 7 := by
  have h := positiveAdvanceRun_potential 4 .one
  rw [positive_four_final] at h
  change (positiveAdvanceRun 4 .one).2 + 2 = 8 + 1 at h
  omega

theorem positive_four_run : positiveAdvanceRun 4 .one = ((5 : PosNum), 7) :=
  Prod.ext positive_four_final positive_four_writes

theorem positive_four_average_bound : ((positiveAdvanceRun 4 .one).2 : ℚ) / 4 ≤ 2 :=
  positiveAdvanceRun_one_average 4 (by decide)

theorem positive_four_average_exact : ((positiveAdvanceRun 4 .one).2 : ℚ) / 4 = 7 / 4 := by
  rw [positive_four_writes]
  rfl

theorem four_before_states :
    (List.iterate PosNum.succ .one 4).map numeric = [1, 2, 3, 4] := by
  rw [map_numeric_iterate_succ_one]
  rfl

theorem four_transitions_finish_at_five : numeric (positiveAdvanceRun 4 .one).1 = 5 :=
  positiveAdvanceRun_one_numeric 4

theorem four_observed_states_final : (positiveAdvanceRun (4 - 1) .one).1 = (4 : PosNum) := by
  apply numeric_injective
  rw [positiveAdvanceRun_one_numeric]
  rfl

theorem four_observed_states_writes : (positiveAdvanceRun (4 - 1) .one).2 = 6 := by
  have h := positiveAdvanceRun_potential (4 - 1) .one
  rw [four_observed_states_final] at h
  change (positiveAdvanceRun (4 - 1) .one).2 + 1 = 6 + 1 at h
  omega

theorem observed_states_bound_is_attained :
    (positiveAdvanceRun (4 - 1) .one).2 = 2 * (4 - 1) := four_observed_states_writes

theorem empty_observation_needs_no_transition :
    (List.iterate PosNum.succ .one 0).map numeric = [] ∧
      (positiveAdvanceRun (0 - 1) .one).2 = 0 :=
  ⟨rfl, congrArg Prod.snd (positiveAdvanceRun_zero .one)⟩

theorem initial_seven_final : (positiveAdvanceRun 1 (7 : PosNum)).1 = (8 : PosNum) := by
  apply numeric_injective
  rw [positiveAdvanceRun_numeric]
  rfl

theorem initial_seven_writes : (positiveAdvanceRun 1 (7 : PosNum)).2 = 4 := by
  have h := positiveAdvanceRun_potential 1 (7 : PosNum)
  rw [initial_seven_final] at h
  change (positiveAdvanceRun 1 (7 : PosNum)).2 + 1 = 2 + 3 at h
  omega

/-- The positive-one bound cannot be transferred to arbitrary starts. -/
theorem initial_potential_is_necessary : (positiveAdvanceRun 1 (7 : PosNum)).2 > 2 * 1 := by
  rw [initial_seven_writes]
  decide

theorem initial_seven_boundary (n : Nat) :
    (positiveAdvanceRun n (7 : PosNum)).2 +
      BinaryCounter.ones (digits (positiveAdvanceRun n (7 : PosNum)).1) = 2 * n + 3 :=
  positiveAdvanceRun_potential n (7 : PosNum)

theorem zero_start_first_write : numAddOneRun .zero = ((1 : Num), 1) := numAddOneRun_zero

theorem positive_one_next_writes : numAddOneRun (1 : Num) = ((2 : Num), 2) := by
  change numAddOneRun (.pos .one) = _
  rw [numAddOneRun_pos, succWriteRun_one]
  rfl

theorem numeric_and_signed_step :
    ((numAddOneRun (7 : Num)).1 : Nat) = 8 ∧
      (numAddOneRun (7 : Num)).1.toZNum = (8 : ZNum) := by
  constructor
  · rw [castNum_numAddOneRun]
    rfl
  · rw [numAddOneRun_toZNum]
    rfl

theorem num_four_final : (numAdvanceRun 4 .zero).1 = (4 : Num) := by
  apply Num.to_nat_inj.mp
  rw [castNum_numAdvanceRun_zero]
  rfl

theorem num_four_writes : (numAdvanceRun 4 .zero).2 = 7 := by
  have h := numAdvanceRun_potential 4 .zero
  rw [num_four_final] at h
  change (numAdvanceRun 4 .zero).2 + 1 = 8 + 0 at h
  omega

theorem num_four_run : numAdvanceRun 4 .zero = ((4 : Num), 7) :=
  Prod.ext num_four_final num_four_writes

theorem signed_four_successors : (fun z : ZNum => z + 1)^[4] 0 = (4 : ZNum) := by
  calc
    (fun z : ZNum => z + 1)^[4] 0 = (numAdvanceRun 4 .zero).1.toZNum :=
      (numAdvanceRun_toZNum 4 .zero).symm
    _ = 4 := by rw [num_four_final]; rfl

theorem signed_zero_start_nonnegative (n : Nat) :
    0 ≤ ((numAdvanceRun n .zero).1.toZNum : Int) ∧
      ((numAdvanceRun n .zero).1.toZNum : Int) = n :=
  ⟨numAdvanceRun_nonnegative n .zero, castZNum_toZNum_numAdvanceRun_zero n⟩

/-- A duplicate flag increments; a fresh flag leaves the same binary counter.
This is only a transition supplied to the existing `Resources.run`. -/
def optionalIncrement (duplicate : Bool) (c : Num) : Measured Num Nat :=
  if duplicate then numAddOneRun c else Resources.pure c

theorem optionalIncrement_toNat (duplicate : Bool) (c : Num) :
    ((optionalIncrement duplicate c).1 : Nat) =
      if duplicate then (c : Nat) + 1 else (c : Nat) := by
  cases duplicate with
  | false => rfl
  | true => exact castNum_numAddOneRun c

theorem optionalIncrement_potential (duplicate : Bool) (c : Num) :
    (optionalIncrement duplicate c).2 +
      BinaryCounter.ones (numDigits (optionalIncrement duplicate c).1) =
        BinaryCounter.ones (numDigits c) + (if duplicate then 2 else 0) := by
  cases duplicate with
  | false => simp [optionalIncrement, Resources.pure]
  | true => exact numAddOneRun_potential c

/-- Four increment commands among six transitions; no second run is extracted. -/
theorem sparse_potential (c : Num) :
    (run optionalIncrement [true, false, true, true, false, true] c).2 +
      BinaryCounter.ones
        (numDigits (run optionalIncrement [true, false, true, true, false, true] c).1) =
          BinaryCounter.ones (numDigits c) + 8 := by
  have h := run_potential_exact optionalIncrement (fun duplicate _ => if duplicate then 2 else 0)
    (fun d => BinaryCounter.ones (numDigits d)) optionalIncrement_potential
    [true, false, true, true, false, true] c
  simpa only [budget, Bool.false_eq_true, ite_true, ite_false, Nat.zero_add, Nat.add_zero,
    Nat.add_assoc, show (2 : Nat) + (2 + (2 + 2)) = 8 from rfl] using h

theorem sparse_numeric :
    ((run optionalIncrement [true, false, true, true, false, true] .zero).1 : Nat) = 4 := by
  have h := run_value_fusion optionalIncrement
    (fun duplicate (n : Nat) => if duplicate then n + 1 else n) (fun c : Num => (c : Nat))
    (fun _ => True) (fun _ _ _ => True.intro)
    (fun duplicate c _ => optionalIncrement_toNat duplicate c)
    [true, false, true, true, false, true] .zero True.intro
  exact h

theorem sparse_final :
    (run optionalIncrement [true, false, true, true, false, true] .zero).1 = (4 : Num) :=
  Num.to_nat_inj.mp sparse_numeric

theorem sparse_writes :
    (run optionalIncrement [true, false, true, true, false, true] .zero).2 = 7 := by
  have h := sparse_potential .zero
  rw [sparse_final] at h
  change (run optionalIncrement [true, false, true, true, false, true] .zero).2 + 1 = 0 + 8 at h
  omega

end Examples.PositiveCounterWork
