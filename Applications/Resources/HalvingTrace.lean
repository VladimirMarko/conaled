import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! Finite positive halving traces supporting FDSA Chapter 3, printed p.35.

Entries count active invocations; recursive edges are one fewer. A positive
state may stop early. This module proves size and tariff arithmetic only.
An algorithmic use must establish its actual policy trace and its actual
per-step charges, including pivot construction and partition work.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.HalvingTrace

/-- A nonempty trace of positive sizes, halving at every continuing edge. -/
inductive Halves : Nat → List Nat → Prop where
  | stop {n : Nat} (positive : 0 < n) : Halves n [n]
  | step {n m : Nat} {tail : List Nat}
      (halving : 2 * m ≤ n) (rest : Halves m tail) : Halves n (n :: tail)

theorem positive {n : Nat} {sizes : List Nat} (trace : Halves n sizes) : 0 < n := by
  induction trace with
  | stop hp => exact hp
  | step halving _ ih => omega

theorem nonempty {n : Nat} {sizes : List Nat} (trace : Halves n sizes) :
    sizes ≠ [] := by
  cases trace <;> simp

theorem head_eq {n : Nat} {sizes : List Nat} (trace : Halves n sizes) :
    sizes.head? = some n := by
  cases trace <;> rfl

theorem length_pos {n : Nat} {sizes : List Nat} (trace : Halves n sizes) :
    0 < sizes.length := by
  cases trace <;> simp

theorem all_positive {n : Nat} {sizes : List Nat} (trace : Halves n sizes) :
    ∀ size ∈ sizes, 0 < size := by
  induction trace with
  | stop hp => simpa using hp
  | step halving rest ih =>
      intro size member
      rcases List.mem_cons.mp member with first | later
      · subst size
        have child_positive := positive rest
        omega
      · exact ih size later

/-- The indexed tail really starts at the next recorded size. -/
theorem next_halved {n m : Nat} {tail : List Nat}
    (trace : Halves n (n :: m :: tail)) : 2 * m ≤ n := by
  cases trace with
  | step halving rest =>
      have hhead := head_eq rest
      simp at hhead
      omega

/-- Natural division gives the exact floor-halving version of the constructor. -/
theorem step_of_le_half {n m : Nat} {tail : List Nat}
    (halving : m ≤ n / 2) (rest : Halves m tail) : Halves n (n :: tail) := by
  exact Halves.step (m := m) (by omega) rest

/-- Positivity bounds the number of active entries by scan volume. -/
theorem length_le_sum {n : Nat} {sizes : List Nat} (trace : Halves n sizes) :
    sizes.length ≤ sizes.sum := by
  exact List.length_le_sum_of_one_le sizes
    (fun size member => Nat.succ_le_of_lt (all_positive trace size member))

theorem member_le_sum {n size : Nat} {sizes : List Nat}
    (trace : Halves n sizes) (member : size ∈ sizes) : size ≤ sizes.sum := by
  exact List.single_le_sum (fun value hv => (all_positive trace value hv).le) size member

theorem initial_le_sum {n : Nat} {sizes : List Nat} (trace : Halves n sizes) :
    n ≤ sizes.sum := by
  cases trace <;> simp only [List.sum_cons, List.sum_nil] <;> omega

theorem sum_le_twice {n : Nat} {sizes : List Nat} (trace : Halves n sizes) :
    sizes.sum ≤ 2 * n := by
  induction trace with
  | stop _ => simp only [List.sum_cons, List.sum_nil]; omega
  | step halving _ ih => simp only [List.sum_cons]; omega

/-- The final active size is positive, giving a power bound on recursive edges. -/
theorem pow_edges_le {n : Nat} {sizes : List Nat} (trace : Halves n sizes) :
    2 ^ (sizes.length - 1) ≤ n := by
  induction trace with
  | stop hp => simpa using Nat.succ_le_of_lt hp
  | @step n m tail halving rest ih =>
      have tail_positive := length_pos rest
      have split_length : tail.length = (tail.length - 1) + 1 := by omega
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [split_length, pow_succ]
      omega

theorem edges_le_log {n : Nat} {sizes : List Nat} (trace : Halves n sizes) :
    sizes.length - 1 ≤ Nat.log 2 n := by
  exact Nat.le_log_of_pow_le (by decide) (pow_edges_le trace)

theorem edges_le_clog {n : Nat} {sizes : List Nat} (trace : Halves n sizes) :
    sizes.length - 1 ≤ Nat.clog 2 n :=
  (edges_le_log trace).trans (Nat.log_le_clog 2 n)

theorem singleton_at_one {sizes : List Nat} (trace : Halves 1 sizes) :
    sizes = [1] := by
  cases trace with
  | stop _ => rfl
  | step halving rest =>
      have child_positive := positive rest
      omega

theorem zero_impossible (sizes : List Nat) : ¬ Halves 0 sizes := by
  intro trace
  have impossible := positive trace
  omega

/-- Alignment rules out omitted or extra charged steps. A and B are fixed. -/
theorem affine_charges_sum_le (A B : Nat) {sizes charges : List Nat}
    (aligned : List.Forall₂ (fun size charge => charge ≤ A * size + B) sizes charges) :
    charges.sum ≤ A * sizes.sum + B * sizes.length := by
  induction aligned with
  | nil => simp
  | cons bound _ ih =>
      simp only [List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- The conditional linear upper tariff; pivot construction is part of the premise. -/
theorem tariff_sum_le {n : Nat} {sizes charges : List Nat}
    (trace : Halves n sizes) (A B : Nat)
    (aligned : List.Forall₂ (fun size charge => charge ≤ A * size + B) sizes charges) :
    charges.sum ≤ (2 * A + 2 * B) * n := by
  have volume := sum_le_twice trace
  have entries : sizes.length ≤ 2 * n := (length_le_sum trace).trans volume
  calc
    charges.sum ≤ A * sizes.sum + B * sizes.length := affine_charges_sum_le A B aligned
    _ ≤ A * (2 * n) + B * (2 * n) :=
      Nat.add_le_add (Nat.mul_le_mul_left A volume) (Nat.mul_le_mul_left B entries)
    _ = (2 * A + 2 * B) * n := by ring

/-- A lower charge premise is independent of the upper tariff. -/
theorem sum_le_charges {sizes charges : List Nat}
    (aligned : List.Forall₂ (fun size charge => size ≤ charge) sizes charges) :
    sizes.sum ≤ charges.sum := by
  induction aligned with
  | nil => simp
  | cons bound _ ih => simpa only [List.sum_cons] using Nat.add_le_add bound ih

theorem initial_le_charges {n : Nat} {sizes charges : List Nat}
    (trace : Halves n sizes)
    (aligned : List.Forall₂ (fun size charge => size ≤ charge) sizes charges) :
    n ≤ charges.sum :=
  (initial_le_sum trace).trans (sum_le_charges aligned)

end Resources.HalvingTrace
