import SquareKit.PartialSpine
import Mathlib.Order.Monotone.Defs

/-!
# Finite constructor-budget observations

Seeing the final nil consumes one constructor of budget. The independent view
therefore uses a strict length comparison for the completed-end flag.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.PartialSpine

universe u
variable {α : Type u}

def cut : Nat → PartialSpine α → PartialSpine α
  | 0, _ => .bottom
  | _ + 1, .bottom => .bottom
  | _ + 1, .nil => .nil
  | n + 1, .cons a s => .cons a (cut n s)

theorem view_cut (n : Nat) (s : PartialSpine α) :
    view (cut n s) = ((view s).1.take n, (view s).2 && decide ((view s).1.length < n)) := by
  induction n generalizing s with
  | zero => simp [cut, view]
  | succ n ih => cases s <;> simp [cut, view, ih, Nat.succ_lt_succ_iff]

theorem cut_le (n : Nat) (s : PartialSpine α) : cut n s ≤ s := by
  induction n generalizing s with
  | zero => exact bot_le
  | succ n ih =>
    cases s with
    | bottom => exact le_rfl
    | nil => exact le_rfl
    | cons a s => exact Below.cons a (ih s)

theorem cut_monotone (n : Nat) : Monotone (cut (α := α) n) := by
  intro s t h
  induction h generalizing n with
  | bottom s => cases n <;> exact bot_le
  | nil => exact le_rfl
  | cons a h ih =>
    cases n with
    | zero => exact le_rfl
    | succ n => exact Below.cons a (ih n)

theorem cut_openPrefix (n : Nat) (xs : List α) : cut n (openPrefix xs) = openPrefix (xs.take n) := by
  apply view_injective
  simp only [view_cut, view_openPrefix, Bool.false_and]

end SquareKit.PartialSpine
