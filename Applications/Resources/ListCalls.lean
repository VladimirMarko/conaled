import Applications.Resources.CallCount
import Applications.Resources.SymmetricCosts
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Measured list primitives for FDSA Appendix B.1. Callback observations are
charged once per occurrence. Taking and dropping separately each pay for their
own traversal, even though `splitRun` can produce both values in one traversal.
Lookup uses sequential recursion and optional failure, with an explicitly chosen
empty-input extension. These are source-model counts, not Lean runtime bounds.
Provenance and statement review: `docs/research/fdsa-reconstruction-map.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListCalls
universe u v
variable {α : Type u} {β : Type v}

/-- Map evaluates the callback and recursive tail, then charges one map entry. -/
def mapRun (f : α → Measured β Nat) : List α → Measured (List β) Nat
  | [] => ([], 1)
  | x :: xs => CallCount.tick (bind (f x) fun y =>
      bind (mapRun f xs) fun ys => pure (y :: ys))

theorem mapRun_nil (f : α → Measured β Nat) : mapRun f [] = ([], 1) := rfl

theorem mapRun_cons (f : α → Measured β Nat) (x : α) (xs : List α) :
    mapRun f (x :: xs) =
      ((f x).1 :: (mapRun f xs).1, (f x).2 + (mapRun f xs).2 + 1) := by
  simp [mapRun, bind, pure, CallCount.tick]

theorem mapRun_value (f : α → Measured β Nat) (xs : List α) :
    (mapRun f xs).1 = xs.map (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapRun_cons, ih]

theorem mapRun_cost (f : α → Measured β Nat) (xs : List α) :
    (mapRun f xs).2 = (xs.map (fun x => (f x).2)).sum + xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapRun_cons, ih, Nat.add_assoc]

theorem mapRun_exact (f : α → Measured β Nat) (xs : List α) :
    mapRun f xs =
      (xs.map (fun x => (f x).1), (xs.map (fun x => (f x).2)).sum + xs.length + 1) :=
  Prod.ext (mapRun_value f xs) (mapRun_cost f xs)

/-- Constant cost is needed only for callbacks actually reached by this input. -/
theorem mapRun_cost_of_constant (f : α → Measured β Nat) (xs : List α) (c : Nat)
    (hc : ∀ x ∈ xs, (f x).2 = c) :
    (mapRun f xs).2 = (c + 1) * xs.length + 1 := by
  induction xs with
  | nil => simp [mapRun_nil]
  | cons x xs ih =>
      have hx := hc x (by simp)
      have ht := ih (fun y hy => hc y (by simp [hy]))
      simp only [mapRun_cons, hx, ht, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- Every predicate occurrence is evaluated, including those that discard a head. -/
def filterRun (p : α → Measured Bool Nat) : List α → Measured (List α) Nat
  | [] => ([], 1)
  | x :: xs => CallCount.tick (bind (p x) fun keep =>
      bind (filterRun p xs) fun ys => pure (if keep then x :: ys else ys))

theorem filterRun_nil (p : α → Measured Bool Nat) : filterRun p [] = ([], 1) := rfl

theorem filterRun_cons (p : α → Measured Bool Nat) (x : α) (xs : List α) :
    filterRun p (x :: xs) =
      (if (p x).1 then x :: (filterRun p xs).1 else (filterRun p xs).1,
       (p x).2 + (filterRun p xs).2 + 1) := by
  simp [filterRun, bind, pure, CallCount.tick]

theorem filterRun_value (p : α → Measured Bool Nat) (xs : List α) :
    (filterRun p xs).1 = xs.filter (fun x => (p x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [filterRun_cons, ih, List.filter_cons]

theorem filterRun_cost (p : α → Measured Bool Nat) (xs : List α) :
    (filterRun p xs).2 = (xs.map (fun x => (p x).2)).sum + xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [filterRun_cons, ih, Nat.add_assoc]

theorem filterRun_exact (p : α → Measured Bool Nat) (xs : List α) :
    filterRun p xs =
      (xs.filter (fun x => (p x).1), (xs.map (fun x => (p x).2)).sum + xs.length + 1) :=
  Prod.ext (filterRun_value p xs) (filterRun_cost p xs)

/-- The cost recurrences agree; the returned lists have different meanings. -/
theorem filterRun_cost_eq_mapRun (p : α → Measured Bool Nat) (xs : List α) :
    (filterRun p xs).2 = (mapRun p xs).2 := by
  rw [filterRun_cost, mapRun_cost]

theorem filterRun_cost_of_constant (p : α → Measured Bool Nat) (xs : List α) (c : Nat)
    (hc : ∀ x ∈ xs, (p x).2 = c) :
    (filterRun p xs).2 = (c + 1) * xs.length + 1 := by
  rw [filterRun_cost_eq_mapRun]
  exact mapRun_cost_of_constant p xs c hc

/-- Preserve the first result and the traversal observation of the existing split. -/
def takeRun (k : Nat) (xs : List α) : Measured (List α) Nat :=
  let r := SymmetricCosts.splitRun k xs
  (r.1.1, r.2)

/-- Preserve the second result and the traversal observation of the existing split. -/
def dropRun (k : Nat) (xs : List α) : Measured (List α) Nat :=
  let r := SymmetricCosts.splitRun k xs
  (r.1.2, r.2)

theorem takeRun_nil (k : Nat) : takeRun k ([] : List α) = ([], 1) := by
  cases k <;> rfl

theorem takeRun_zero (xs : List α) : takeRun 0 xs = ([], 1) := rfl

theorem takeRun_succ_cons (k : Nat) (x : α) (xs : List α) :
    takeRun (k + 1) (x :: xs) =
      (x :: (takeRun k xs).1, (takeRun k xs).2 + 1) := rfl

theorem dropRun_nil (k : Nat) : dropRun k ([] : List α) = ([], 1) := by
  cases k <;> rfl

theorem dropRun_zero (xs : List α) : dropRun 0 xs = (xs, 1) := rfl

theorem dropRun_succ_cons (k : Nat) (x : α) (xs : List α) :
    dropRun (k + 1) (x :: xs) =
      ((dropRun k xs).1, (dropRun k xs).2 + 1) := rfl

theorem takeRun_exact (k : Nat) (xs : List α) :
    takeRun k xs = (xs.take k, min k xs.length + 1) := by
  simp [takeRun, SymmetricCosts.splitRun_value, SymmetricCosts.splitRun_work]

theorem dropRun_exact (k : Nat) (xs : List α) :
    dropRun k xs = (xs.drop k, min k xs.length + 1) := by
  simp [dropRun, SymmetricCosts.splitRun_value, SymmetricCosts.splitRun_work]

/-- Two separate calls return the fused split's value but pay twice its count. -/
theorem take_drop_separate (k : Nat) (xs : List α) :
    bind (takeRun k xs) (fun taken =>
      bind (dropRun k xs) (fun dropped => pure (taken, dropped))) =
      ((SymmetricCosts.splitRun k xs).1, 2 * (SymmetricCosts.splitRun k xs).2) := by
  simp [takeRun_exact, dropRun_exact, SymmetricCosts.splitRun_value,
    SymmetricCosts.splitRun_work, bind, pure, Nat.two_mul]

/-- Sequential zero-based lookup. The empty-input count of one is an explicit
extension: the source specifies costs only for valid positions.
-/
def lookupRun : List α → Nat → Measured (Option α) Nat
  | [], _ => (none, 1)
  | x :: _, 0 => (some x, 1)
  | _ :: xs, k + 1 => CallCount.tick (lookupRun xs k)

theorem lookupRun_nil (k : Nat) : lookupRun ([] : List α) k = (none, 1) := rfl

theorem lookupRun_zero_cons (x : α) (xs : List α) :
    lookupRun (x :: xs) 0 = (some x, 1) := rfl

theorem lookupRun_succ_cons (k : Nat) (x : α) (xs : List α) :
    lookupRun (x :: xs) (k + 1) =
      ((lookupRun xs k).1, (lookupRun xs k).2 + 1) := rfl

theorem lookupRun_value (xs : List α) (k : Nat) :
    (lookupRun xs k).1 = xs[k]? := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => cases k <;> simp [lookupRun, ih]

/-- Total count of our optional extension; only its bounded specialization below
is a claim from the book.
-/
theorem lookupRun_cost (xs : List α) (k : Nat) :
    (lookupRun xs k).2 = min k xs.length + 1 := by
  induction xs generalizing k with
  | nil => simp [lookupRun]
  | cons x xs ih => cases k <;> simp [lookupRun, ih, Nat.succ_min_succ]

theorem lookupRun_cost_of_lt (xs : List α) (k : Nat) (hk : k < xs.length) :
    (lookupRun xs k).2 = k + 1 := by
  rw [lookupRun_cost, Nat.min_eq_left (Nat.le_of_lt hk)]

/-- The optional result recovers the existing proof-domain observation. -/
theorem lookupRun_valid (xs : List α) (k : Nat) (hk : k < xs.length) :
    lookupRun xs k = (some xs[k], k + 1) := by
  apply Prod.ext
  · simp [lookupRun_value]
  · exact lookupRun_cost_of_lt xs k hk

end Resources.ListCalls
