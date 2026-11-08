import Mathlib.Tactic

namespace Sequences.PreparedRMQ
variable {α : Type} [LinearOrder α]

/-- Inclusive interval scan; the seed is the first element, so no sentinel or
inhabitedness assumption is required. -/
def rangeMin (read : Nat → α) (start : Nat) : Nat → α
  | 0 => read start
  | n+1 => min (rangeMin read start n) (read (start+n+1))

theorem rangeMin_le_first (read : Nat → α) (start n : Nat) :
    rangeMin read start n ≤ read start := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (min_le_left _ _).trans ih

theorem rangeMin_le (read : Nat → α) (start n i : Nat) (hi : i ≤ n) :
    rangeMin read start n ≤ read (start+i) := by
  induction n with
  | zero =>
    have hiz : i = 0 := by omega
    subst i
    simp [rangeMin]
  | succ n ih =>
    by_cases h : i ≤ n
    · exact (min_le_left _ _).trans (ih h)
    · have : i = n+1 := by omega
      subst i
      simpa [rangeMin,Nat.add_assoc] using min_le_right (rangeMin read start n) (read (start+n+1))

theorem le_rangeMin (read : Nat → α) (start n : Nat) (x : α)
    (h : ∀ i ≤ n, x ≤ read (start+i)) : x ≤ rangeMin read start n := by
  induction n with
  | zero => simpa [rangeMin] using h 0 (by omega)
  | succ n ih => exact le_min (ih (fun i hi => h i (by omega))) (by simpa [Nat.add_assoc] using h (n+1) le_rfl)

end Sequences.PreparedRMQ
