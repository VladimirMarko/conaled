import Applications.Selection.MedianReduction
import Applications.Resources.FixedRank
import Applications.Resources.ListReversal

/-!
Actual source call counts for the rank-to-median reduction, FDSA Exercise 3.5.

Length and both extrema traversals are charged. Both padding lists are built
by measured replication, and both appends pay for their own traversals. Each
declared source function entry costs one; the arithmetic expressions and
primitive comparisons/min/max have zero observation. These counts concern
the reduction's preparation work, before the subsequent median call, and make
no claim about Lean execution time or allocation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.MedianReduction
open Applications.Selection.MedianReduction
universe u
variable {α : Type u}

/-- Recursive replication, including the final zero-count invocation. -/
def replicateRun (a : α) : Nat → Measured (List α) Nat
  | 0 => ([], 1)
  | n + 1 =>
      let r := replicateRun a n
      (a :: r.1, r.2 + 1)

theorem replicateRun_exact (a : α) (n : Nat) :
    replicateRun a n = (List.replicate n a, n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [replicateRun, ih, List.replicate_succ]

/-- Build both pads, append the upper pad to the input, then prepend the
lower pad. This is the association used by the pure `padExtrema`. -/
def padExtremaRun (low high : Nat) (lo hi : α) (xs : List α) :
    Measured (List α) Nat :=
  CallCount.tick (bind (replicateRun lo low) fun lowPad =>
    bind (replicateRun hi high) fun highPad =>
      bind (ListReversal.appendRun xs highPad) fun rest =>
        ListReversal.appendRun lowPad rest)

theorem padExtremaRun_value (low high : Nat) (lo hi : α) (xs : List α) :
    (padExtremaRun low high lo hi xs).1 = padExtrema low high lo hi xs := by
  simp only [padExtremaRun, CallCount.tick_value, bind_value, replicateRun_exact,
    ListReversal.appendRun_exact, padExtrema]

theorem padExtremaRun_cost (low high : Nat) (lo hi : α) (xs : List α) :
    (padExtremaRun low high lo hi xs).2 = 2 * low + high + xs.length + 5 := by
  simp only [padExtremaRun, CallCount.tick_cost, bind, replicateRun_exact,
    ListReversal.appendRun_exact, List.length_replicate]
  omega

theorem padExtremaRun_exact (low high : Nat) (lo hi : α) (xs : List α) :
    padExtremaRun low high lo hi xs =
      (padExtrema low high lo hi xs, 2 * low + high + xs.length + 5) :=
  Prod.ext (padExtremaRun_value low high lo hi xs) (padExtremaRun_cost low high lo hi xs)

variable [LinearOrder α]

/-- Execute both minimum loops, reversing the order in the second one, and
charge the extrema helper. Neither extremum is assumed to have been supplied. -/
def extremaRun (x : α) (xs : List α) : Measured (α × α) Nat :=
  CallCount.tick (bind (FixedRank.minimumLoopRun x 0 xs) fun lo =>
    bind (FixedRank.minimumLoopRun (α := OrderDual α) x 0 xs) fun hi => pure (lo, hi))

theorem extremaRun_value (x : α) (xs : List α) : (extremaRun x xs).1 = extrema x xs := by
  simp only [extremaRun, CallCount.tick_value, bind_value,
    FixedRank.minimumLoopRun_value,
    FixedRank.minimumLoopRun_value (α := OrderDual α) x 0 xs, pure, extrema]

theorem extremaRun_cost (x : α) (xs : List α) :
    (extremaRun x xs).2 = 2 * xs.length + 3 := by
  simp only [extremaRun, CallCount.tick_cost, bind, pure, FixedRank.minimumLoopRun_cost,
    FixedRank.minimumLoopRun_cost (α := OrderDual α) x 0 xs]
  omega

theorem extremaRun_exact (x : α) (xs : List α) :
    extremaRun x xs = (extrema x xs, 2 * xs.length + 3) :=
  Prod.ext (extremaRun_value x xs) (extremaRun_cost x xs)

def reduceToMedianRun (k : Nat) : List α → Measured (List α) Nat
  | [] => ([], 1)
  | x :: xs =>
      CallCount.tick (bind (SymmetricCosts.lengthRun (x :: xs)) fun n =>
        bind (extremaRun x xs) fun bounds =>
          padExtremaRun (n - 1 - 2 * k) (2 * k + 1 - n) bounds.1 bounds.2 (x :: xs))

theorem reduceToMedianRun_nil (k : Nat) : reduceToMedianRun k ([] : List α) = ([], 1) := rfl

theorem reduceToMedianRun_value (k : Nat) (xs : List α) :
    (reduceToMedianRun k xs).1 = reduceToMedian k xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      simp only [reduceToMedianRun, CallCount.tick_value, bind_value,
        SymmetricCosts.lengthRun_exact, extremaRun_value, padExtremaRun_value, reduceToMedian]

theorem reduceToMedianRun_cons_cost (k : Nat) (x : α) (xs : List α) :
    (reduceToMedianRun k (x :: xs)).2 =
      4 * (x :: xs).length + 2 * ((x :: xs).length - 1 - 2 * k) +
        (2 * k + 1 - (x :: xs).length) + 8 := by
  simp only [reduceToMedianRun, CallCount.tick_cost, bind,
    SymmetricCosts.lengthRun_exact, extremaRun_cost, padExtremaRun_cost, List.length_cons]
  omega

theorem reduceToMedianRun_cost (k : Nat) (xs : List α) (hx : xs ≠ []) :
    (reduceToMedianRun k xs).2 =
      4 * xs.length + 2 * (xs.length - 1 - 2 * k) + (2 * k + 1 - xs.length) + 8 := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons x xs => exact reduceToMedianRun_cons_cost k x xs

/-- The validity premise bounds the actual padding, not merely its selected
value. The explicit constants 6 and 6 are independent of both input and rank. -/
theorem reduceToMedianRun_cost_le (k : Nat) (xs : List α) (hk : k < xs.length) :
    (reduceToMedianRun k xs).2 ≤ 6 * xs.length + 6 := by
  have hx : xs ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [reduceToMedianRun_cost k xs hx]
  have h := padding_total_le k xs.length hk
  omega

theorem reduceToMedianRun_uniform_bound :
    ∃ C1 C2 : Nat, ∀ (k : Nat) (xs : List α), k < xs.length →
      (reduceToMedianRun k xs).2 ≤ C1 * xs.length + C2 :=
  ⟨6, 6, reduceToMedianRun_cost_le⟩

end Resources.MedianReduction
