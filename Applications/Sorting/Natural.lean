import Applications.Sorting.NaturalRuns
import Applications.Sorting.BottomUp

/-!
# Natural merge sort

The FDSA §2.6 sorter feeds the actual natural runs into the ordinary adjacent-run
merger. The scanner and merger may use independent Boolean operations for the
law-free occurrence laws. Source key sorting scans with strict `<` and merges
with left-tie `≤`. Sortedness follows from the existing two component contracts;
these value results make no comparison, runtime or general stability claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting

universe u v
variable {α : Type u} {κ : Type v}

/-- Detect runs, then merge those same runs with the ordinary bottom-up merger. -/
def sortNaturalBy (lt cmp : α → α → Bool) (xs : List α) : List α :=
  mergeAllBy cmp (runsBy lt xs)

theorem sortNaturalBy_eq_mergeAllBy (lt cmp : α → α → Bool) (xs : List α) :
    sortNaturalBy lt cmp xs = mergeAllBy cmp (runsBy lt xs) := rfl

@[simp] theorem sortNaturalBy_nil (lt cmp : α → α → Bool) :
    sortNaturalBy lt cmp [] = [] := by
  simp only [sortNaturalBy, runsBy_nil, mergeAllBy_nil]

@[simp] theorem sortNaturalBy_singleton (lt cmp : α → α → Bool) (a : α) :
    sortNaturalBy lt cmp [a] = [a] := by
  simp only [sortNaturalBy, runsBy_singleton, mergeAllBy_singleton]

/-- Every full payload occurrence survives, regardless of comparator laws. -/
theorem sortNaturalBy_perm (lt cmp : α → α → Bool) (xs : List α) :
    (sortNaturalBy lt cmp xs).Perm xs :=
  (mergeAllBy_perm cmp (runsBy lt xs)).trans (runsBy_perm lt xs)

theorem sortNaturalBy_multiset (lt cmp : α → α → Bool) (xs : List α) :
    (sortNaturalBy lt cmp xs : Multiset α) = (xs : Multiset α) :=
  Multiset.coe_eq_coe.mpr (sortNaturalBy_perm lt cmp xs)

theorem sortNaturalBy_length (lt cmp : α → α → Bool) (xs : List α) :
    (sortNaturalBy lt cmp xs).length = xs.length :=
  (sortNaturalBy_perm lt cmp xs).length_eq

theorem mem_sortNaturalBy (lt cmp : α → α → Bool) (xs : List α) (a : α) :
    a ∈ sortNaturalBy lt cmp xs ↔ a ∈ xs :=
  (sortNaturalBy_perm lt cmp xs).mem_iff

/-- Compatibility is needed only on input members, separately for each operation. -/
theorem sortNaturalBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (lt cmp : α → α → Bool) (xs : List α)
    (hlt : ∀ a ∈ xs, ∀ b ∈ xs,
      (lt a b = true → key a ≤ key b) ∧ (lt a b = false → key b ≤ key a))
    (hcmp : ∀ a ∈ xs, ∀ b ∈ xs,
      (cmp a b = true → key a ≤ key b) ∧ (cmp a b = false → key b ≤ key a)) :
    KeySorted key (sortNaturalBy lt cmp xs) := by
  apply mergeAllBy_sorted_compatible_on key cmp (runsBy lt xs)
  · intro a ha b hb
    exact hcmp a ((runsBy_perm lt xs).mem_iff.mp ha)
      b ((runsBy_perm lt xs).mem_iff.mp hb)
  · exact runsBy_sorted_compatible_on key lt xs hlt

/-- A sole detected run is returned unchanged; the merger needs no order premise. -/
theorem sortNaturalBy_of_runs_eq_singleton (lt cmp : α → α → Bool) (xs ys : List α)
    (h : runsBy lt xs = [ys]) : sortNaturalBy lt cmp xs = ys := by
  rw [sortNaturalBy, h, mergeAllBy_singleton]

theorem sortNaturalBy_of_ascending_chain (lt cmp : α → α → Bool) (xs : List α)
    (hne : xs ≠ []) (h : xs.IsChain (fun a b => lt b a = false)) :
    sortNaturalBy lt cmp xs = xs :=
  sortNaturalBy_of_runs_eq_singleton lt cmp xs xs
    (runsBy_of_ascending_chain lt xs hne h)

theorem sortNaturalBy_of_descending_chain (lt cmp : α → α → Bool) (xs : List α)
    (hne : xs ≠ []) (h : xs.IsChain (fun a b => lt b a = true)) :
    sortNaturalBy lt cmp xs = xs.reverse :=
  sortNaturalBy_of_runs_eq_singleton lt cmp xs xs.reverse
    (runsBy_of_descending_chain lt xs hne h)

/-- The source branch choices compare only keys, never payloads. -/
abbrev sortNaturalOn [LT κ] [DecidableLT κ] [LE κ] [DecidableLE κ]
    (key : α → κ) (xs : List α) : List α :=
  sortNaturalBy (fun a b => decide (key a < key b))
    (fun a b => decide (key a ≤ key b)) xs

theorem sortNaturalOn_correct [LinearOrder κ] (key : α → κ) (xs : List α) :
    KeySorted key (sortNaturalOn key xs) ∧ (sortNaturalOn key xs).Perm xs := by
  refine ⟨?_, sortNaturalBy_perm _ _ xs⟩
  apply sortNaturalBy_sorted_compatible_on key
  · intro a _ b _
    exact ⟨fun h => le_of_lt (of_decide_eq_true h),
      fun h => le_of_not_gt (of_decide_eq_false h)⟩
  · intro a _ b _
    exact ⟨of_decide_eq_true, fun h =>
      (le_total (key a) (key b)).resolve_left (of_decide_eq_false h)⟩

/-- Empty input is handled directly; every nonempty sorted input supplies one run. -/
theorem sortNaturalOn_of_sorted [LinearOrder κ] (key : α → κ) (xs : List α)
    (hs : KeySorted key xs) : sortNaturalOn key xs = xs := by
  cases xs with
  | nil => exact sortNaturalBy_nil _ _
  | cons a xs =>
    exact sortNaturalBy_of_runs_eq_singleton _ _ _ _
      (runsOn_of_sorted key (a :: xs) hs (by simp))

/-- This value law only needs the stated strict comparisons, not order axioms. -/
theorem sortNaturalOn_of_strictly_descending
    [LT κ] [DecidableLT κ] [LE κ] [DecidableLE κ]
    (key : α → κ) (xs : List α) (hs : xs.Pairwise (fun a b => key b < key a)) :
    sortNaturalOn key xs = xs.reverse := by
  cases xs with
  | nil => exact sortNaturalBy_nil _ _
  | cons a xs =>
    exact sortNaturalBy_of_runs_eq_singleton _ _ _ _
      (runsOn_of_strictly_descending key (a :: xs) hs (by simp))

end Applications.Sorting
