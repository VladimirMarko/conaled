import Applications.Sequences.RangeMinimum
import Mathlib.Data.Nat.Log

/-! Arbitrary-size sparse-table range coverage. Overlap is justified by minimum's
idempotence, expressed through its order characterization. -/
namespace Sequences.LCA
open PreparedRMQ
variable {α : Type} [LinearOrder α]

/-- A power-of-two row recurrence, before its finite storage realization. -/
def sparseRow (read : Nat → α) : Nat → Nat → α
  | 0, i => read i
  | k + 1, i => min (sparseRow read k i) (sparseRow read k (i + 2 ^ k))

theorem rangeMin_split (read : Nat → α) (start p q : Nat) (hp : 0 < p) (hq : 0 < q) :
    rangeMin read start (p + q - 1) =
      min (rangeMin read start (p - 1)) (rangeMin read (start + p) (q - 1)) := by
  apply le_antisymm
  · apply le_min
    · apply le_rangeMin
      intro i hi
      exact rangeMin_le read start _ i (by omega)
    · apply le_rangeMin
      intro i hi
      simpa [Nat.add_assoc] using rangeMin_le read start (p + q - 1) (p + i) (by omega)
  · apply le_rangeMin
    intro i hi
    by_cases hip : i < p
    · exact (min_le_left _ _).trans (rangeMin_le read start (p - 1) i (by omega))
    · have he : start + i = start + p + (i - p) := by omega
      rw [he]
      exact (min_le_right _ _).trans (rangeMin_le read (start + p) (q - 1) (i-p) (by omega))

theorem sparseRow_correct (read : Nat → α) (k start : Nat) :
    sparseRow read k start = rangeMin read start (2 ^ k - 1) := by
  induction k generalizing start with
  | zero => simp [sparseRow, rangeMin]
  | succ k ih =>
    rw [sparseRow, ih, ih, pow_succ]
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    have he : 2 ^ k * 2 = 2 ^ k + 2 ^ k := by omega
    rw [he, rangeMin_split read start _ _ hp hp]

/-- Two possibly overlapping ranges cover the requested interval. -/
theorem rangeMin_overlap (read : Nat → α) (start len p : Nat)
    (hp : 0 < p) (hpl : p ≤ len) (hcover : len ≤ 2 * p) :
    min (rangeMin read start (p - 1))
      (rangeMin read (start + len - p) (p - 1)) =
      rangeMin read start (len - 1) := by
  apply le_antisymm
  · apply le_rangeMin
    intro i hi
    by_cases hip : i < p
    · exact (min_le_left _ _).trans (rangeMin_le read start (p-1) i (by omega))
    · have hj : i - (len - p) ≤ p - 1 := by omega
      have he : start + i = start + len - p + (i - (len-p)) := by omega
      rw [he]
      exact (min_le_right _ _).trans (rangeMin_le read (start+len-p) (p-1) _ hj)
  · apply le_min
    · apply le_rangeMin
      intro i hi
      exact rangeMin_le read start (len-1) i (by omega)
    · apply le_rangeMin
      intro i hi
      have he : start + len - p + i = start + (len - p + i) := by omega
      rw [he]
      exact rangeMin_le read start (len-1) (len-p+i) (by omega)

theorem sparse_query_correct (read : Nat → α) (start len : Nat) (hl : 0 < len) :
    min (sparseRow read (Nat.log 2 len) start)
      (sparseRow read (Nat.log 2 len) (start + len - 2 ^ Nat.log 2 len)) =
      rangeMin read start (len - 1) := by
  rw [sparseRow_correct, sparseRow_correct]
  apply rangeMin_overlap
  · exact Nat.two_pow_pos _
  · exact Nat.pow_log_le_self 2 (by omega)
  · have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) len
    rw [pow_succ] at hh
    omega

/-- The same overlap rule fails for addition: the middle input is duplicated. -/
example : (1 + 2) + (2 + 3) ≠ (1 + 2 + 3 : Nat) := by decide

end Sequences.LCA
