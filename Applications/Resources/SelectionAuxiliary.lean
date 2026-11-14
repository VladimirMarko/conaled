import Applications.Resources.InsertionSort
import Applications.Resources.ListCalls
import Applications.Selection.CountRank

/-! Insertion-based selection helpers with the FDSA Appendix B.2 call tariff.
Sorting, lookup and length are the existing measured executions. These
nonrecursive wrappers add no entry charge. The canonical sorted list is only
the value specification; its merge-sort realization supplies no cost here.
Valid source ranks are zero-based. Optional failure makes the operations total
without an inhabitant of the payload type; invalid-input costs describe that
extension, not an additional assertion about the book's out-of-bounds indexing.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SelectionAuxiliary
open Applications.Selection
universe u
variable {α : Type u} [LinearOrder α]

/-- Execute insertion sorting and then the source's sequential lookup. -/
def slowSelectRun (k : Nat) (xs : List α) : Measured (Option α) Nat :=
  bind (InsertionSort.sortRun (· ≤ ·) xs) fun ys => ListCalls.lookupRun ys k

theorem slowSelectRun_value (k : Nat) (xs : List α) :
    (slowSelectRun k xs).1 = (ordered xs)[k]? := by
  rw [slowSelectRun, bind_value, ListCalls.lookupRun_value, InsertionSort.sortRun_value]
  change (Applications.Sorting.insertionOn id xs)[k]? = (ordered xs)[k]?
  rw [← Applications.Sorting.sortOn_eq_insertionOn id xs]

/-- Exact total count, including the declared optional lookup extension. -/
theorem slowSelectRun_cost (k : Nat) (xs : List α) :
    (slowSelectRun k xs).2 =
      (InsertionSort.sortRun (· ≤ ·) xs).2 + min k xs.length + 1 := by
  simp only [slowSelectRun, bind, ListCalls.lookupRun_cost,
    InsertionSort.sortRun_length, Nat.add_assoc]

theorem slowSelectRun_cost_of_lt (k : Nat) (xs : List α) (hk : k < xs.length) :
    (slowSelectRun k xs).2 = (InsertionSort.sortRun (· ≤ ·) xs).2 + k + 1 := by
  rw [slowSelectRun_cost, Nat.min_eq_left (Nat.le_of_lt hk)]

theorem slowSelectRun_some_iff (k : Nat) (xs : List α) (a : α) :
    (slowSelectRun k xs).1 = some a ↔ RankedAt xs k a := by
  rw [slowSelectRun_value, ← ranked_iff_index]

theorem slowSelectRun_none (k : Nat) (xs : List α) :
    (slowSelectRun k xs).1 = none ↔ xs.length ≤ k := by
  rw [slowSelectRun_value, List.getElem?_eq_none_iff, (ordered_perm xs).length_eq]

/-- Book rank k corresponds to public rank k+1, including optional failure. -/
theorem slowSelectRun_public (k : Nat) (xs : List α) :
    (slowSelectRun k xs).1 = sortSelect (k + 1) xs := by
  rw [slowSelectRun_value]
  simp [sortSelect]

/-- The book's deliberately coarse insertion/lookup bound for valid ranks. -/
theorem slowSelectRun_cost_bound (k : Nat) (xs : List α) (hk : k < xs.length) :
    (slowSelectRun k xs).2 ≤ xs.length ^ 2 + 3 * xs.length + 1 := by
  have hs := InsertionSort.sortRun_quadratic (· ≤ ·) xs
  rw [slowSelectRun_cost_of_lt k xs hk]
  nlinarith

theorem slowSelectRun_cost_of_pairwise (k : Nat) (xs : List α)
    (hk : k < xs.length) (hs : xs.Pairwise (· ≤ ·)) :
    (slowSelectRun k xs).2 = 2 * xs.length + k + 2 := by
  rw [slowSelectRun_cost_of_lt k xs hk, InsertionSort.sortRun_cost_of_pairwise _ xs hs]
  omega

theorem slowSelectRun_cost_reverse_range (n k : Nat) (hk : k < n) :
    (slowSelectRun k (List.range n).reverse).2 =
      (n + 1) * (n + 2) / 2 + k + 1 := by
  rw [slowSelectRun_cost_of_lt k _ (by
    simpa only [List.length_reverse, List.length_range] using hk),
    InsertionSort.sortRun_cost_reverse_range]

/-- The source base branch additionally charges entry and its cached length. -/
theorem slowSelectRun_entry_bound (k : Nat) (xs : List α) (hk : k < xs.length) :
    1 + (SymmetricCosts.lengthRun xs).2 + (slowSelectRun k xs).2 ≤
      xs.length ^ 2 + 4 * xs.length + 3 := by
  have hs := slowSelectRun_cost_bound k xs hk
  rw [SymmetricCosts.lengthRun_exact]
  omega

theorem slowSelectRun_cutoff_bound (k : Nat) (xs : List α)
    (hk : k < xs.length) (hn : xs.length ≤ 20) :
    1 + (SymmetricCosts.lengthRun xs).2 + (slowSelectRun k xs).2 ≤ 483 := by
  have hs := slowSelectRun_entry_bound k xs hk
  have hsq : xs.length * xs.length ≤ 20 * 20 := Nat.mul_le_mul hn hn
  nlinarith

/-- Evaluate length once, then use its lower-occurrence index in slow selection. -/
def slowMedianRun (xs : List α) : Measured (Option α) Nat :=
  bind (SymmetricCosts.lengthRun xs) fun n => slowSelectRun ((n - 1) / 2) xs

theorem slowMedianRun_value (xs : List α) :
    (slowMedianRun xs).1 = lowerMedianWith List.head? xs := by
  simp only [slowMedianRun, bind_value, SymmetricCosts.lengthRun_exact, slowSelectRun_value]
  exact (lowerMedian_value List.head? head_pivot_valid xs).symm

theorem slowMedianRun_cost (xs : List α) :
    (slowMedianRun xs).2 = (SymmetricCosts.lengthRun xs).2 +
      (slowSelectRun ((xs.length - 1) / 2) xs).2 := by
  simp only [slowMedianRun, bind, SymmetricCosts.lengthRun_exact]

theorem slowMedianRun_some_iff (xs : List α) (a : α) :
    (slowMedianRun xs).1 = some a ↔ RankedAt xs ((xs.length - 1) / 2) a := by
  rw [slowMedianRun_value, lowerMedian_value List.head? head_pivot_valid, ← ranked_iff_index]

theorem slowMedianRun_none (xs : List α) :
    (slowMedianRun xs).1 = none ↔ xs = [] := by
  rw [slowMedianRun_value, lowerMedian_none List.head? head_pivot_valid]

theorem slowMedianRun_mem (xs : List α) (a : α)
    (ha : (slowMedianRun xs).1 = some a) : a ∈ xs :=
  ((slowMedianRun_some_iff xs a).mp ha).mem

theorem slowMedianRun_cost_bound (xs : List α) (hx : xs ≠ []) :
    (slowMedianRun xs).2 ≤ xs.length ^ 2 + 4 * xs.length + 2 := by
  have hn : 0 < xs.length := List.length_pos_iff.mpr hx
  have hi : (xs.length - 1) / 2 < xs.length := by omega
  have hs := slowSelectRun_cost_bound ((xs.length - 1) / 2) xs hi
  rw [slowMedianRun_cost, SymmetricCosts.lengthRun_exact]
  omega

/-- The last chunk may have any positive size up to five. -/
theorem slowMedianRun_small_bound (xs : List α) (hx : xs ≠ [])
    (hn : xs.length ≤ 5) : (slowMedianRun xs).2 ≤ 47 := by
  have hs := slowMedianRun_cost_bound xs hx
  have hsq : xs.length * xs.length ≤ 5 * 5 := Nat.mul_le_mul hn hn
  nlinarith

end Resources.SelectionAuxiliary
