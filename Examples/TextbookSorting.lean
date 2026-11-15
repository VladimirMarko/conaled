import Applications.Sorting.FirstPair
import Examples.SortUniqueness
import SquareKit.Combinators

/-!
# Interchangeable sorting clients across textbook developments

VFA's first-pair comparison preserves occurrences for any Boolean comparator.
FDSA's independent sorting correctness contracts then determine the ordinary
result. The existing exact-square synchronization keeps both implementations
and constructs their agreement witness; no new sorting interface is needed.

The observation here is the complete ordered list of records. This does not
equate execution costs, and antisymmetry on records cannot be replaced by
antisymmetry on noninjective keys. The final boundary case makes that distinction
explicit. The source first-pair operation itself is not a whole-list sort.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TextbookSorting

open Applications.Sorting
open Squares

universe u
variable {α : Type u}

/-- An arbitrary first-pair comparison cannot change the ordinary result of a
complete sorter. No ordering or asymmetry law is required of `swap`. -/
theorem sort_after_compareSwap (r : α → α → Prop) [Std.Antisymm r]
    (f : List α → List α)
    (hf : ∀ xs, (f xs).Pairwise r ∧ (f xs).Perm xs)
    (swap : α → α → Bool) (xs : List α) :
    f (compareSwap swap xs) = f xs :=
  sorters_eq_at r (fun ys => f (compareSwap swap ys)) f xs
    ⟨(hf _).1, (hf _).2.trans (compareSwap_perm swap xs).symm⟩ (hf xs)

/-- The first-pivot implementation, with VFA preprocessing, realizes the
existing stable-sort value specification when records themselves are ordered. -/
def preprocessedQuickSquare [LinearOrder α] (swap : α → α → Bool) :
    Square (exact (List α)) (exact (List α)) where
  impl xs := quickSortOn id (compareSwap swap xs)
  spec := sortOn id
  commutes xs := by
    change quickSortOn id (compareSwap swap xs) = sortOn id xs
    calc
      quickSortOn id (compareSwap swap xs) = quickSortOn id xs :=
        sort_after_compareSwap (fun a b : α => a ≤ b) _
          (quickSortOn_correct id) swap xs
      _ = sortFloorOn id xs := congrFun SortUniqueness.first_pivot_eq_floor xs
      _ = sortOn id xs := sortFloorOn_eq_sortOn id xs

/-- FDSA's independent floor-split recursion realizes the same existing
specification through its retained stable-sort theorem. -/
def floorSquare [LinearOrder α] :
    Square (exact (List α)) (exact (List α)) where
  impl := sortFloorOn id
  spec := sortOn id
  commutes xs := sortFloorOn_eq_sortOn id xs

/-- A joint implementation using the library's agreement pullback. Both
algorithms are retained, including their independent computation recipes. -/
def jointSquare [LinearOrder α] (swap : α → α → Bool) :
    Square (synchronized (id : List α → List α) id)
      (synchronized (id : List α → List α) id) :=
  synchronize (preprocessedQuickSquare swap) floorSquare (fun _ => rfl)

/-- The reusable synchronization law gives agreement of the actual independent
outputs on the same input, for every list and arbitrary preprocessing comparator. -/
theorem paired_outputs [LinearOrder α] (swap : α → α → Bool) (xs : List α) :
    quickSortOn id (compareSwap swap xs) = sortFloorOn id xs :=
  synchronize_agrees (preprocessedQuickSquare swap) floorSquare
    (fun _ => rfl) ⟨(xs, xs), rfl⟩

/-- The independently retained mixed-duplicate expectation is transferred
through the new cross-book synchronized client, not recomputed in isolation. -/
theorem mixed_duplicates :
    quickSortOn id
      (compareSwap (fun a b : Nat => decide (b < a)) [2, 3, 1, 2, 0, 3, 2, 1]) =
      [0, 1, 1, 2, 2, 2, 3, 3] :=
  (paired_outputs _ _).trans SortUniqueness.floor_mixed_duplicates

/-- With constant keys, stable sorting retains the changed occurrence order.
Such a key relation is not antisymmetric on the actual Boolean records. -/
theorem equal_key_order_matters :
    sortFloorOn (fun _ : Bool => (0 : Nat))
        (compareSwap (fun _ _ => true) [false, true]) ≠
      sortFloorOn (fun _ : Bool => (0 : Nat)) [false, true] := by
  rw [sortFloorOn_eq_sortOn, sortFloorOn_eq_sortOn,
    sortOn_sorted_fixed _ _ (by decide), sortOn_sorted_fixed _ _ (by decide)]
  decide

end Examples.TextbookSorting
