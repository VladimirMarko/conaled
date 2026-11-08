import Mathlib.Tactic

/-! Independent total meanings chosen before the table implementation. -/
namespace Applications.Memoization.Client

def wordValue : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * wordValue bs

def wordMeaning (w : List Bool) : List Bool × Nat := (w, wordValue w)

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def ordinary : Nat → Nat × Nat
  | 0 => (0, 1)
  | 1 => (1, 1)
  | n + 2 =>
    let a := ordinary (n + 1)
    let b := ordinary n
    (a.1 + b.1, 1 + a.2 + b.2)

theorem ordinary_value (n : Nat) : (ordinary n).1 = fib n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih ih' => simp [ordinary, fib, ih, ih']

example : wordMeaning [true, false, true] = ([true, false, true], 5) := rfl
example : ordinary 10 = (55, 177) := by decide
example : fib 0 = 0 ∧ fib 1 = 1 ∧ fib 2 = 1 := by decide
end Applications.Memoization.Client
