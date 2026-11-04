import Applications.Selection.FixedRank
import Applications.Resources.InsertionSort
import Applications.Resources.ListCalls

/-!
Source call counts for the actual fixed-rank selectors in FDSA Exercises 3.1–3.3.

Each named function entry costs one. Primitive comparisons, `min`, `max`,
constructors and pattern matching have zero observation. Insertion, taking
and final lookup use the existing measured list implementations. The outer
loops accumulate their observations before the recursive tail call; they do
not traverse the input again to assign a cost. All bounds are for this source
model and do not assert Lean runtime or allocation bounds.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.FixedRank
open Applications.Selection.FixedRank
universe u
variable {α : Type u} [LinearOrder α]

/-- `spent` is the cost already incurred before entering this tail loop. -/
def minimumLoopRun (best : α) (spent : Nat) : List α → Measured α Nat
  | [] => (best, spent + 1)
  | x :: xs => minimumLoopRun (min best x) (spent + 1) xs

theorem minimumLoopRun_value (best : α) (spent : Nat) (xs : List α) :
    (minimumLoopRun best spent xs).1 = minimumLoop best xs := by
  induction xs generalizing best spent with
  | nil => rfl
  | cons x xs ih => simp only [minimumLoopRun, minimumLoop, ih]

theorem minimumLoopRun_cost (best : α) (spent : Nat) (xs : List α) :
    (minimumLoopRun best spent xs).2 = spent + xs.length + 1 := by
  induction xs generalizing best spent with
  | nil => rfl
  | cons x xs ih =>
      simp only [minimumLoopRun, ih, List.length_cons]
      omega

/-- Charge the selector's entry, then execute the actual minimum tail loop. -/
def select0Run : List α → Measured (Option α) Nat
  | [] => (none, 1)
  | x :: xs =>
      let r := minimumLoopRun x 1 xs
      (some r.1, r.2)

theorem select0Run_value (xs : List α) : (select0Run xs).1 = select0 xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [select0Run, select0, minimumLoopRun_value]

/-- Exact linear source cost for Exercise 3.1, including empty input. -/
theorem select0Run_cost (xs : List α) : (select0Run xs).2 = xs.length + 1 := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      simp only [select0Run, minimumLoopRun_cost, List.length_cons]
      omega

theorem select0Run_exact (xs : List α) :
    select0Run xs = (select0 xs, xs.length + 1) :=
  Prod.ext (select0Run_value xs) (select0Run_cost xs)

/-- Both traversals are charged: measured insertion into the accumulator,
then measured taking from its actual returned list, plus this helper's entry. -/
def boundedInsertRun (m : Nat) (x : α) (acc : List α) : Measured (List α) Nat :=
  CallCount.tick (bind (InsertionSort.insertRun (· ≤ ·) x acc) (ListCalls.takeRun m))

theorem boundedInsertRun_value (m : Nat) (x : α) (acc : List α) :
    (boundedInsertRun m x acc).1 = boundedInsert m x acc := by
  simp only [boundedInsertRun, CallCount.tick_value, bind_value,
    ListCalls.takeRun_exact, InsertionSort.insertRun_value, boundedInsert]

theorem boundedInsertRun_cost (m : Nat) (x : α) (acc : List α) :
    (boundedInsertRun m x acc).2 =
      (InsertionSort.insertRun (· ≤ ·) x acc).2 + min m (acc.length + 1) + 2 := by
  simp only [boundedInsertRun, CallCount.tick_cost, bind, ListCalls.takeRun_exact,
    InsertionSort.insertRun_value, List.orderedInsert_length]
  omega

/-- A step is linear in the chosen accumulator width, independent of the
unread input length and of the values (including duplicates). -/
theorem boundedInsertRun_cost_le (m : Nat) (x : α) (acc : List α)
    (hacc : acc.length ≤ m) : (boundedInsertRun m x acc).2 ≤ 2 * m + 3 := by
  rw [boundedInsertRun_cost]
  have hi := (InsertionSort.insertRun_cost_bounds (· ≤ ·) x acc).2
  have ht := Nat.min_le_left m (acc.length + 1)
  omega

theorem boundedInsertRun_length_le (m : Nat) (x : α) (acc : List α) :
    (boundedInsertRun m x acc).1.length ≤ m := by
  rw [boundedInsertRun_value]
  exact boundedInsert_length_le m x acc

/-- Count the outer entry and actual bounded insertion before the recursive
call. This is the same tail-recursive input traversal as `prefixLoop`. -/
def prefixLoopRun (m : Nat) (acc : List α) (spent : Nat) :
    List α → Measured (List α) Nat
  | [] => (acc, spent + 1)
  | x :: xs =>
      let step := boundedInsertRun m x acc
      prefixLoopRun m step.1 (spent + step.2 + 1) xs

theorem prefixLoopRun_value (m : Nat) (acc : List α) (spent : Nat) (xs : List α) :
    (prefixLoopRun m acc spent xs).1 = prefixLoop m acc xs := by
  induction xs generalizing acc spent with
  | nil => rfl
  | cons x xs ih =>
      simp only [prefixLoopRun, ih, boundedInsertRun_value, prefixLoop]

theorem prefixLoopRun_cost_le (m : Nat) (acc : List α) (spent : Nat) (xs : List α)
    (hacc : acc.length ≤ m) :
    (prefixLoopRun m acc spent xs).2 ≤ spent + (2 * m + 4) * xs.length + 1 := by
  induction xs generalizing acc spent with
  | nil => simp [prefixLoopRun]
  | cons x xs ih =>
      have hs := boundedInsertRun_cost_le m x acc hacc
      have ht := ih (boundedInsertRun m x acc).1
        (spent + (boundedInsertRun m x acc).2 + 1)
        (boundedInsertRun_length_le m x acc)
      change (prefixLoopRun m (boundedInsertRun m x acc).1
        (spent + (boundedInsertRun m x acc).2 + 1) xs).2 ≤
          spent + (2 * m + 4) * (xs.length + 1) + 1
      rw [Nat.mul_add, Nat.mul_one]
      omega

def takeSortRun (m : Nat) (xs : List α) : Measured (List α) Nat :=
  prefixLoopRun m [] 1 xs

theorem takeSortRun_value (m : Nat) (xs : List α) :
    (takeSortRun m xs).1 = takeSort m xs := prefixLoopRun_value m [] 1 xs

theorem takeSortRun_cost_le (m : Nat) (xs : List α) :
    (takeSortRun m xs).2 ≤ (2 * m + 4) * xs.length + 2 := by
  have h := prefixLoopRun_cost_le m [] 1 xs (Nat.zero_le m)
  change (prefixLoopRun m [] 1 xs).2 ≤ (2 * m + 4) * xs.length + 2
  omega

/-- The final sequential lookup is charged in addition to the streaming loop. -/
def selectFixedRun (k : Nat) (xs : List α) : Measured (Option α) Nat :=
  CallCount.tick (bind (takeSortRun (k + 1) xs) (fun acc => ListCalls.lookupRun acc k))

theorem selectFixedRun_value (k : Nat) (xs : List α) :
    (selectFixedRun k xs).1 = selectFixed k xs := by
  simp only [selectFixedRun, CallCount.tick_value, bind_value,
    ListCalls.lookupRun_value, takeSortRun_value, selectFixed]

theorem selectFixedRun_cost (k : Nat) (xs : List α) :
    (selectFixedRun k xs).2 =
      (takeSortRun (k + 1) xs).2 + min k (min (k + 1) xs.length) + 2 := by
  simp only [selectFixedRun, CallCount.tick_cost, bind, ListCalls.lookupRun_cost,
    takeSortRun_value, takeSort_length]
  omega

/-- Explicit uniform constants `2,6,1,4`; the bound also covers invalid ranks.
In particular, `k = 0` retains its nonzero linear term. -/
theorem selectFixedRun_cost_le (k : Nat) (xs : List α) :
    (selectFixedRun k xs).2 ≤
      2 * k * xs.length + 6 * xs.length + k + 4 := by
  rw [selectFixedRun_cost]
  have ht := takeSortRun_cost_le (k + 1) xs
  have hl := Nat.min_le_left k (min (k + 1) xs.length)
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at ht
  omega

/-- Exercise 3.3's quantifier order: one set of constants works for every
valid requested rank and input list. -/
theorem selectFixedRun_uniform_bound :
    ∃ C1 C2 C3 C4 : Nat, ∀ (k : Nat) (xs : List α), k < xs.length →
      (selectFixedRun k xs).2 ≤
        C1 * k * xs.length + C2 * xs.length + C3 * k + C4 := by
  refine ⟨2, 6, 1, 4, ?_⟩
  intro k xs _
  simpa only [Nat.one_mul] using selectFixedRun_cost_le k xs

end Resources.FixedRank
