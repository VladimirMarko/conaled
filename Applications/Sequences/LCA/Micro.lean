import Applications.Sequences.LCA.BlockShape
import Applications.Sequences.LCA.Sparse
import Mathlib.Order.Prod.Lex.Basic

/-! Leftmost argmin queries and their factorization through integer block-class
addresses. Key ordering retains the position when depths tie. -/
namespace Sequences.LCA
open PreparedRMQ

def depthKey (depth : Nat → Int) (i : Nat) : Int ×ₗ Nat := toLex (depth i, i)

theorem rangeMin_occurs {α : Type} [LinearOrder α] (read : Nat → α) (start n : Nat) :
    ∃ i, i ≤ n ∧ rangeMin read start n = read (start + i) := by
  induction n with
  | zero => exact ⟨0, le_rfl, by simp [rangeMin]⟩
  | succ n ih =>
    rcases ih with ⟨i, hi, he⟩
    by_cases h : rangeMin read start n ≤ read (start + n + 1)
    · exact ⟨i, by omega, by simpa [rangeMin, min_eq_left h] using he⟩
    · refine ⟨n+1, le_rfl, ?_⟩
      rw [rangeMin, min_eq_right (le_of_not_ge h)]
      congr 1

def argmin (depth : Nat → Int) (start lenMinusOne : Nat) : Nat :=
  (ofLex (rangeMin (depthKey depth) start lenMinusOne)).2

theorem argmin_correct (depth : Nat → Int) (start len : Nat) :
    LeftmostMinimum depth start (start + len) (argmin depth start len) := by
  obtain ⟨i, hi, he⟩ := rangeMin_occurs (depthKey depth) start len
  have ha : argmin depth start len = start + i := by simp [argmin, he, depthKey]
  rw [ha]
  refine ⟨by omega, by omega, ?_⟩
  intro j hj hj'
  have hh := rangeMin_le (depthKey depth) start len (j-start) (by omega)
  have hjj : start + (j-start) = j := by omega
  rw [he, hjj] at hh
  simpa [depthKey, Prod.Lex.le_iff'] using hh

theorem relative_unitSteps (shape : Shape steps) : UnitSteps steps (relative shape) := by
  intro i hi
  simp only [relative, hi, dite_true]
  cases shape ⟨i, hi⟩ <;> simp <;> omega

theorem classify_relative (shape : Shape steps) : classify steps (relative shape) = shape := by
  funext i
  simp only [classify, relative, i.isLt, dite_true]
  cases h : shape i <;> simp [h]

/-- The height offset discarded by classification is invisible to exact
leftmost argmin queries, not merely to minimum-value comparisons. -/
theorem argmin_factor (depth : Nat → Int) (h : UnitSteps steps depth)
    (start len : Nat) (hi : start + len ≤ steps) :
    argmin depth start len = argmin (relative (classify steps depth)) start len := by
  apply leftmostMinimum_unique depth
  · exact argmin_correct depth start len
  · apply (same_shape_minimum depth (relative (classify steps depth)) h
      (relative_unitSteps _) (by rw [classify_relative]) hi).mpr
    exact argmin_correct _ start len

def classQuery (steps code start lenMinusOne : Nat) : Nat :=
  argmin (relative (decodeShape steps code)) start lenMinusOne

theorem classQuery_correct (depth : Nat → Int) (h : UnitSteps steps depth)
    (start len : Nat) (hi : start + len ≤ steps) :
    classQuery steps (classAddress steps depth).val start len = argmin depth start len := by
  unfold classQuery classAddress
  rw [decode_shapeCode]
  exact (argmin_factor depth h start len hi).symm

example : argmin (fun i => if i = 1 then (4 : Int) else 3) 0 2 = 0 := by decide
example : argmin (fun i => if i = 1 then (4 : Int) else 3) 1 1 = 2 := by decide
example : classQuery 2 1 0 2 = 0 := by decide

end Sequences.LCA
