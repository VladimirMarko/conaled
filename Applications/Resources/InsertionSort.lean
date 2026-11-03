import Applications.Resources.CallCount
import Applications.Sorting.Sort
import Mathlib.Tactic.Linarith

/-! Source call counts for insertion, shared by sorting and selection clients.
The operations and uniform bounds require only a decidable relation. Order laws
are required separately for the existing stable-sorting specification. Counts
refer to the stated recursive invocations, not Lean execution time.
Source: FDSA (July 27, 2026), section 2.2 and exercise 2.1.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.InsertionSort
universe u v
variable {α : Type u} {κ : Type v}

/-- One call for the immediate branch, or one plus the recursive-tail count. -/
def insertRun (r : α → α → Prop) [DecidableRel r] (x : α) :
    List α → Measured (List α) Nat
  | [] => ([x], 1)
  | y :: ys =>
      if r x y then (x :: y :: ys, 1)
      else
        let rest := insertRun r x ys
        (y :: rest.1, rest.2 + 1)

theorem insertRun_value (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    (insertRun r x xs).1 = List.orderedInsert r x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : r x y <;> simp [insertRun, List.orderedInsert, h, ih]

theorem insertRun_cost_bounds (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) :
    1 ≤ (insertRun r x xs).2 ∧ (insertRun r x xs).2 ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [insertRun]
  | cons y ys ih =>
      by_cases h : r x y
      · simp [insertRun, h]
      · simp only [insertRun, h, ↓reduceIte, List.length_cons]
        omega

/-- The immediate branch inspects only the head, regardless of the tail. -/
theorem insertRun_cost_of_head (r : α → α → Prop) [DecidableRel r] (x y : α)
    (ys : List α) (h : r x y) : (insertRun r x (y :: ys)).2 = 1 := by
  simp [insertRun, h]

theorem insertRun_cost_of_all (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) (h : ∀ y ∈ xs, r x y) : (insertRun r x xs).2 = 1 := by
  cases xs with
  | nil => rfl
  | cons y ys => exact insertRun_cost_of_head r x y ys (h y List.mem_cons_self)

theorem insertRun_cost_of_all_not (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) (h : ∀ y ∈ xs, ¬ r x y) :
    (insertRun r x xs).2 = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      have hy := h y List.mem_cons_self
      have ht : ∀ z ∈ ys, ¬ r x z := fun z hz => h z (List.mem_cons_of_mem y hz)
      simp [insertRun, hy, ih ht]

/-- Count the recursive sort, insertion into its actual result, and sort entry. -/
def sortRun (r : α → α → Prop) [DecidableRel r] : List α → Measured (List α) Nat
  | [] => ([], 1)
  | x :: xs => CallCount.tick (bind (sortRun r xs) (insertRun r x))

theorem sortRun_value (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (sortRun r xs).1 = List.insertionSort r xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sortRun, bind, insertRun_value, ih]

theorem sortRun_length (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (sortRun r xs).1.length = xs.length := by
  rw [sortRun_value]
  exact (List.perm_insertionSort r xs).length_eq

theorem sortRun_cons_cost (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    (sortRun r (x :: xs)).2 =
      (sortRun r xs).2 + (insertRun r x (sortRun r xs).1).2 + 1 := rfl

theorem sortRun_cost_lower (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    2 * xs.length + 1 ≤ (sortRun r xs).2 := by
  induction xs with
  | nil => simp [sortRun]
  | cons x xs ih =>
      have hi := (insertRun_cost_bounds r x (sortRun r xs).1).1
      rw [sortRun_cons_cost]
      simp only [List.length_cons]
      omega

/-- A division-free uniform upper bound, stronger than the source's square. -/
theorem sortRun_double_cost_le (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    2 * (sortRun r xs).2 ≤ (xs.length + 1) * (xs.length + 2) := by
  induction xs with
  | nil => simp [sortRun]
  | cons x xs ih =>
      have hi := (insertRun_cost_bounds r x (sortRun r xs).1).2
      rw [sortRun_length] at hi
      rw [sortRun_cons_cost]
      simp only [List.length_cons]
      nlinarith

theorem sortRun_cost_le (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (sortRun r xs).2 ≤ (xs.length + 1) * (xs.length + 2) / 2 := by
  have h := sortRun_double_cost_le r xs
  omega

theorem sortRun_quadratic (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (sortRun r xs).2 ≤ (xs.length + 1) ^ 2 := by
  have h := sortRun_double_cost_le r xs
  nlinarith [Nat.zero_le (xs.length * xs.length)]

/-- Pairwise order itself suffices for the best case; no global order is needed. -/
theorem sortRun_cost_of_pairwise (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (h : xs.Pairwise r) : (sortRun r xs).2 = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
      rw [sortRun_cons_cost, sortRun_value, ht.insertionSort_eq,
        insertRun_cost_of_all r x xs hx, ih ht]
      simp [Nat.mul_add, Nat.add_assoc]

/-- Every insertion traverses its tail when earlier inputs precede none of it.
Permutation preserves this condition even though the tail is recursively sorted.
-/
theorem sortRun_double_cost_of_opposite (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (h : xs.Pairwise (fun x y => ¬ r x y)) :
    2 * (sortRun r xs).2 = (xs.length + 1) * (xs.length + 2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
      have ho : ∀ y ∈ (sortRun r xs).1, ¬ r x y := by
        intro y hy
        rw [sortRun_value] at hy
        exact hx y ((List.mem_insertionSort r).mp hy)
      rw [sortRun_cons_cost, insertRun_cost_of_all_not r x _ ho, sortRun_length]
      simp only [List.length_cons]
      have hi := ih ht
      nlinarith

theorem reverse_range_opposite (n : Nat) :
    (List.range n).reverse.Pairwise (fun x y => ¬ x ≤ y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.range_succ, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.cons_append]
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih⟩
      intro y hy
      have hlt := List.mem_range.mp (List.mem_reverse.mp hy)
      omega

/-- The descending range attains the uniform triangular upper bound. -/
theorem sortRun_cost_reverse_range (n : Nat) :
    (sortRun (α := Nat) (· ≤ ·) (List.range n).reverse).2 = (n + 1) * (n + 2) / 2 := by
  have h := sortRun_double_cost_of_opposite (α := Nat) (· ≤ ·)
    (List.range n).reverse (reverse_range_opposite n)
  simp only [List.length_reverse, List.length_range] at h
  omega

/-- Existing stable-sort clients observe the same keyed insertion algorithm. -/
theorem sortRun_stable [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ] [DecidableEq κ]
    (key : α → κ) (xs : List α) :
    Applications.Sorting.StableSort key xs
      (sortRun (fun x y => key x ≤ key y) xs).1 := by
  rw [sortRun_value]
  exact Applications.Sorting.insertionOn_spec key xs

end Resources.InsertionSort
