import Applications.Resources.InsertionSort

/-!
# Insertion sorting with comparisons, calls and constructor requests

One execution records `(comparisons, invocations, literal cons requests)`.
The invocation projection is exactly the existing FDSA `insertRun` / `sortRun`.
The source stopping branch `x :: y :: ys` requests two constructors; this is
not a count of fresh heap cells. Comparisons charge one head test, independently
of its implementation cost. Source correspondence and physical sharing boundaries:
`docs/research/vfa-coverage.md` (VFA 2.1, Sort; CTB-80).
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.InsertionSort
universe u
variable {α : Type u}

/-- Comparisons, recursive invocations, and literal cons requests, respectively. -/
abbrev Work := Nat × Nat × Nat

/-- Refine insertion's actual branch execution with three additive observations. -/
def insertMeasured (r : α → α → Prop) [DecidableRel r] (x : α) :
    List α → Measured (List α) Work
  | [] => ([x], (0, 1, 1))
  | y :: ys =>
      if r x y then (x :: y :: ys, (1, 1, 2))
      else bind (insertMeasured r x ys) (fun zs => (y :: zs, (1, 1, 1)))

/-- Sort the actual tail, insert into its returned value, and charge sort entry. -/
def sortMeasured (r : α → α → Prop) [DecidableRel r] :
    List α → Measured (List α) Work
  | [] => ([], (0, 1, 0))
  | x :: xs => bind (bind (sortMeasured r xs) (insertMeasured r x))
      (fun zs => (zs, (0, 1, 0)))

abbrev insertComparisons (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) : Nat := (insertMeasured r x xs).2.1

abbrev insertConstructors (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) : Nat := (insertMeasured r x xs).2.2.2

abbrev sortComparisons (r : α → α → Prop) [DecidableRel r] (xs : List α) : Nat :=
  (sortMeasured r xs).2.1

abbrev sortConstructors (r : α → α → Prop) [DecidableRel r] (xs : List α) : Nat :=
  (sortMeasured r xs).2.2.2

/-- This is equality of the whole measured pair, including its executed value. -/
theorem insertMeasured_calls (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) : reweight (fun w : Work => w.2.1) (insertMeasured r x xs) =
      insertRun r x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : r x y
      · simp [insertMeasured, insertRun, h, reweight]
      · simpa [insertMeasured, insertRun, h, bind, reweight] using
          congrArg (fun z : Measured (List α) Nat => (y :: z.1, z.2 + 1)) ih

theorem insertMeasured_value (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) : (insertMeasured r x xs).1 = List.orderedInsert r x xs := by
  have h := congrArg Prod.fst (insertMeasured_calls r x xs)
  exact h.trans (insertRun_value r x xs)

theorem sortMeasured_calls (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    reweight (fun w : Work => w.2.1) (sortMeasured r xs) = sortRun r xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hv : (sortMeasured r xs).1 = (sortRun r xs).1 := congrArg Prod.fst ih
      have hc : (sortMeasured r xs).2.2.1 = (sortRun r xs).2 := congrArg Prod.snd ih
      have hi := insertMeasured_calls r x (sortMeasured r xs).1
      apply Prod.ext
      · change (insertMeasured r x (sortMeasured r xs).1).1 =
          (insertRun r x (sortRun r xs).1).1
        rw [← hv]
        exact congrArg Prod.fst hi
      · change (sortMeasured r xs).2.2.1 +
          (insertMeasured r x (sortMeasured r xs).1).2.2.1 + 1 =
            (sortRun r xs).2 + (insertRun r x (sortRun r xs).1).2 + 1
        have hcost : (insertMeasured r x (sortMeasured r xs).1).2.2.1 =
            (insertRun r x (sortMeasured r xs).1).2 := congrArg Prod.snd hi
        rw [hc, hcost, hv]

theorem sortMeasured_value (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (sortMeasured r xs).1 = List.insertionSort r xs := by
  have h := congrArg Prod.fst (sortMeasured_calls r xs)
  exact h.trans (sortRun_value r xs)

theorem sortMeasured_length (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (sortMeasured r xs).1.length = xs.length := by
  rw [sortMeasured_value]
  exact (List.perm_insertionSort r xs).length_eq

theorem insertComparisons_nil (r : α → α → Prop) [DecidableRel r] (x : α) :
    insertComparisons r x [] = 0 := rfl

/-- No comparison is made beyond the first successful head test. -/
theorem insertComparisons_cons (r : α → α → Prop) [DecidableRel r] (x y : α)
    (ys : List α) : insertComparisons r x (y :: ys) =
      if r x y then 1 else insertComparisons r x ys + 1 := by
  by_cases h : r x y <;> simp [insertComparisons, insertMeasured, bind, h]

theorem insertComparisons_of_head (r : α → α → Prop) [DecidableRel r] (x y : α)
    (ys : List α) (h : r x y) : insertComparisons r x (y :: ys) = 1 := by
  simp [insertComparisons_cons, h]

theorem insertComparisons_cons_pos (r : α → α → Prop) [DecidableRel r] (x y : α)
    (ys : List α) : 1 ≤ insertComparisons r x (y :: ys) := by
  rw [insertComparisons_cons]
  split <;> omega

theorem insertComparisons_le (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) : insertComparisons r x xs ≤ xs.length := by
  induction xs with
  | nil => simp [insertComparisons_nil]
  | cons y ys ih =>
      rw [insertComparisons_cons]
      simp only [List.length_cons]
      split <;> omega

theorem insertComparisons_of_all_not (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) (h : ∀ y ∈ xs, ¬ r x y) :
    insertComparisons r x xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      have hy := h y List.mem_cons_self
      have ht : ∀ z ∈ ys, ¬ r x z := fun z hz => h z (List.mem_cons_of_mem y hz)
      simp [insertComparisons_cons, hy, ih ht]

/-- Proved from the branch requests, not assigned afterwards from the output. -/
theorem insertConstructors_eq (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) : insertConstructors r x xs = insertComparisons r x xs + 1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : r x y
      · simp [insertConstructors, insertComparisons, insertMeasured, h]
      · simpa [insertConstructors, insertComparisons, insertMeasured, bind, h] using ih

theorem sortComparisons_nil (r : α → α → Prop) [DecidableRel r] :
    sortComparisons r [] = 0 := rfl

theorem sortComparisons_cons (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) : sortComparisons r (x :: xs) =
      sortComparisons r xs + insertComparisons r x (sortMeasured r xs).1 := by
  simp [sortComparisons, sortMeasured, insertComparisons, bind]

theorem sortConstructors_eq (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    sortConstructors r xs = sortComparisons r xs + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hi := insertConstructors_eq r x (sortMeasured r xs).1
      simpa [sortConstructors, sortComparisons, insertConstructors, insertComparisons,
          sortMeasured, bind, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        congrArg₂ (· + ·) ih hi

/-- At least one comparison for each insertion into a nonempty sorted tail. -/
theorem sortComparisons_lower (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    xs.length - 1 ≤ sortComparisons r xs := by
  induction xs with
  | nil => simp [sortComparisons_nil]
  | cons x xs ih =>
      rw [sortComparisons_cons]
      simp only [List.length_cons]
      cases hout : (sortMeasured r xs).1 with
      | nil =>
          have hlen := sortMeasured_length r xs
          rw [hout] at hlen
          simp only [List.length_nil] at hlen
          omega
      | cons y ys =>
          have hi := insertComparisons_cons_pos r x y ys
          omega

/-- Pairwise order suffices for the best case, without any global order laws. -/
theorem sortComparisons_of_pairwise (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (h : xs.Pairwise r) : sortComparisons r xs = xs.length - 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
      rw [sortComparisons_cons, sortMeasured_value, ht.insertionSort_eq, ih ht]
      cases xs with
      | nil => rfl
      | cons y ys =>
          rw [insertComparisons_of_head r x y ys (hx y List.mem_cons_self)]
          simp

/-- A division-free comparison budget, independent of relation laws. -/
theorem sortComparisons_double_le (r : α → α → Prop) [DecidableRel r]
    (xs : List α) : 2 * sortComparisons r xs ≤ xs.length * (xs.length - 1) := by
  induction xs with
  | nil => simp [sortComparisons_nil]
  | cons x xs ih =>
      have hi := insertComparisons_le r x (sortMeasured r xs).1
      rw [sortMeasured_length] at hi
      rw [sortComparisons_cons]
      cases xs with
      | nil => simp [sortComparisons_nil, sortMeasured, insertComparisons_nil]
      | cons y ys =>
          simp only [List.length_cons, Nat.add_sub_cancel] at ih hi ⊢
          nlinarith

theorem sortComparisons_le (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    sortComparisons r xs ≤ xs.length * (xs.length - 1) / 2 := by
  have h := sortComparisons_double_le r xs
  omega

/-- Permutation transports the all-false premise to the actual sorted tail. -/
theorem sortComparisons_double_of_opposite (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (h : xs.Pairwise (fun x y => ¬ r x y)) :
    2 * sortComparisons r xs = xs.length * (xs.length - 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
      have ho : ∀ y ∈ (sortMeasured r xs).1, ¬ r x y := by
        intro y hy
        rw [sortMeasured_value] at hy
        exact hx y ((List.mem_insertionSort r).mp hy)
      rw [sortComparisons_cons, insertComparisons_of_all_not r x _ ho,
        sortMeasured_length]
      have hi := ih ht
      cases xs with
      | nil => rfl
      | cons y ys =>
          simp only [List.length_cons, Nat.add_sub_cancel] at hi ⊢
          nlinarith

theorem sortComparisons_of_opposite (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (h : xs.Pairwise (fun x y => ¬ r x y)) :
    sortComparisons r xs = xs.length * (xs.length - 1) / 2 := by
  have hi := sortComparisons_double_of_opposite r xs h
  omega

/-- An infinite family attains the comparison bound, including lengths 0 and 1. -/
theorem sortComparisons_reverse_range (n : Nat) :
    sortComparisons (α := Nat) (· ≤ ·) (List.range n).reverse = n * (n - 1) / 2 := by
  simpa using sortComparisons_of_opposite (α := Nat) (· ≤ ·)
    (List.range n).reverse (reverse_range_opposite n)

/-- Literal constructor requests have their own triangular budget. -/
theorem sortConstructors_le (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    sortConstructors r xs ≤ xs.length * (xs.length + 1) / 2 := by
  have hc := sortComparisons_double_le r xs
  rw [sortConstructors_eq]
  have h : 2 * (sortComparisons r xs + xs.length) ≤ xs.length * (xs.length + 1) := by
    cases xs with
    | nil => simp [sortComparisons_nil]
    | cons x xs =>
        simp only [List.length_cons, Nat.add_sub_cancel] at hc ⊢
        nlinarith
  omega

theorem sortConstructors_of_opposite (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (h : xs.Pairwise (fun x y => ¬ r x y)) :
    sortConstructors r xs = xs.length * (xs.length + 1) / 2 := by
  have hc := sortComparisons_double_of_opposite r xs h
  rw [sortConstructors_eq]
  have he : 2 * (sortComparisons r xs + xs.length) = xs.length * (xs.length + 1) := by
    cases xs with
    | nil => rfl
    | cons x xs =>
        simp only [List.length_cons, Nat.add_sub_cancel] at hc ⊢
        nlinarith
  omega

theorem sortConstructors_reverse_range (n : Nat) :
    sortConstructors (α := Nat) (· ≤ ·) (List.range n).reverse = n * (n + 1) / 2 := by
  simpa using sortConstructors_of_opposite (α := Nat) (· ≤ ·)
    (List.range n).reverse (reverse_range_opposite n)

end Resources.InsertionSort
