import Applications.Floating.Observation
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Numerical meaning of the actual rounding classification

The existing core accuracy tag and residual-bit record represent an independent
rational value. The operations remain the actual pinned logical-model operations.
This common relation supports both quotient and shift correctness. Absolute
values and ordered-field reasoning use the standard library.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.Rounding

open Float.Model Float.Model.UnpackedFloat

def AccuracyRep (mantissa : Nat) (accuracy : Accuracy) (value : Rat) : Prop :=
  match accuracy with
  | .exact => value = (mantissa : Rat)
  | .inexact .lt => (mantissa : Rat) < value ∧ 2 * value < 2 * (mantissa : Rat) + 1
  | .inexact .eq => 2 * value = 2 * (mantissa : Rat) + 1
  | .inexact .gt => 2 * (mantissa : Rat) + 1 < 2 * value ∧ value < (mantissa : Rat) + 1

def ExtendedRep (extended : ExtendedMantissa) (value : Rat) : Prop :=
  AccuracyRep extended.mantissa extended.accuracy value

theorem nearestEven_adjacent (mantissa : Nat) (accuracy : Accuracy) :
    mantissa ≤ accuracy.roundToNearestEven mantissa ∧
      accuracy.roundToNearestEven mantissa ≤ mantissa + 1 := by
  cases accuracy with
  | exact => simp [Accuracy.roundToNearestEven]
  | inexact relative =>
    cases relative with
    | lt => simp [Accuracy.roundToNearestEven]
    | eq => simp only [Accuracy.roundToNearestEven]; omega
    | gt => simp [Accuracy.roundToNearestEven]

theorem nearestEven_tie_even (mantissa : Nat) :
    ((Accuracy.inexact .eq).roundToNearestEven mantissa) % 2 = 0 := by
  simp only [Accuracy.roundToNearestEven]
  omega

theorem AccuracyRep.bounds {m : Nat} {a : Accuracy} {x : Rat}
    (h : AccuracyRep m a x) : (m : Rat) ≤ x ∧ x < (m : Rat) + 1 := by
  cases a with
  | exact => simp only [AccuracyRep] at h; subst x; constructor <;> linarith
  | inexact relative => cases relative <;> simp only [AccuracyRep] at h <;>
      constructor <;> linarith

theorem ofMantissaAndAccuracy_rep {m : Nat} {a : Accuracy} {x : Rat}
    (h : AccuracyRep m a x) : ExtendedRep (ExtendedMantissa.ofMantissaAndAccuracy m a) x := by
  cases a with
  | exact => exact h
  | inexact relative => cases relative <;> exact h

theorem AccuracyRep.round_bounds {m : Nat} {a : Accuracy} {x : Rat}
    (h : AccuracyRep m a x) :
    (a.roundToNearestEven m : Rat) - 1 / 2 ≤ x ∧
      x ≤ (a.roundToNearestEven m : Rat) + 1 / 2 := by
  have parity : m % 2 = 0 ∨ m % 2 = 1 := by omega
  cases a with
  | exact => simp only [AccuracyRep, Accuracy.roundToNearestEven] at *; constructor <;> linarith
  | inexact relative =>
    cases relative with
    | lt => simp only [AccuracyRep, Accuracy.roundToNearestEven] at *; constructor <;> linarith
    | eq =>
      simp only [AccuracyRep, Accuracy.roundToNearestEven, Nat.cast_add] at *
      rcases parity with parity | parity <;> norm_num [parity] <;> constructor <;> linarith
    | gt =>
      simp only [AccuracyRep, Accuracy.roundToNearestEven, Nat.cast_add, Nat.cast_one] at *
      constructor <;> linarith

theorem AccuracyRep.round_abs {m : Nat} {a : Accuracy} {x : Rat}
    (h : AccuracyRep m a x) : |(a.roundToNearestEven m : Rat) - x| ≤ 1 / 2 := by
  obtain ⟨lower, upper⟩ := h.round_bounds
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem AccuracyRep.round_scaled {m : Nat} {a : Accuracy} {x : Rat}
    (h : AccuracyRep m a x) (unit : Rat) (nonnegative : 0 ≤ unit) :
    |(a.roundToNearestEven m : Rat) * unit - x * unit| ≤ unit / 2 := by
  rw [← sub_mul, abs_mul, abs_of_nonneg nonnegative]
  calc
    _ ≤ (1 / 2 : Rat) * unit := mul_le_mul_of_nonneg_right h.round_abs nonnegative
    _ = unit / 2 := by ring

theorem AccuracyRep.round_lower {m : Nat} {a : Accuracy} {x : Rat} (k : Nat)
    (h : AccuracyRep m a x) (lower : (k : Rat) ≤ x) : k ≤ a.roundToNearestEven m := by
  have interval := h.bounds
  have adjacent := nearestEven_adjacent m a
  have km : k ≤ m := by
    have hk : (k : Rat) < ((m + 1 : Nat) : Rat) := by
      simpa only [Nat.cast_add, Nat.cast_one] using lower.trans_lt interval.2
    have hk' : k < m + 1 := Rat.natCast_lt_natCast.mp hk
    omega
  omega

theorem AccuracyRep.round_upper {m : Nat} {a : Accuracy} {x : Rat} (k : Nat)
    (h : AccuracyRep m a x) (upper : x ≤ (k : Rat)) : a.roundToNearestEven m ≤ k := by
  have interval := h.bounds
  have mk : m ≤ k := Rat.natCast_le_natCast.mp (interval.1.trans upper)
  have adjacent := nearestEven_adjacent m a
  by_cases equal : m = k
  · subst m
    have value : x = (k : Rat) := le_antisymm upper interval.1
    cases a with
    | exact => simp [Accuracy.roundToNearestEven]
    | inexact relative => cases relative <;> simp only [AccuracyRep, value] at h <;> linarith
  · omega

end Floating.Rounding
