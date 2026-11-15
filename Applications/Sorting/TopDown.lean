import Applications.Sorting.Sort

/-! The floor-left top-down merge sort from FDSA §2.4.
The two contiguous halves preserve the input order across equal-key blocks.
This value algorithm is separate from its comparison observation; equality
with the library's ceil-left merge sort does not identify their work counts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting
universe u v
variable {α : Type u} {κ : Type v}

/-- Split at floor(length/2); lists of length zero or one are returned directly. -/
def sortFloorBy (cmp : α → α → Bool) (xs : List α) : List α :=
  if h : xs.length ≤ 1 then xs
  else List.merge (sortFloorBy cmp (xs.take (xs.length / 2)))
    (sortFloorBy cmp (xs.drop (xs.length / 2))) cmp
termination_by xs.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop]
    omega

theorem sortFloorBy_of_length_le (cmp : α → α → Bool) (xs : List α)
    (h : xs.length ≤ 1) : sortFloorBy cmp xs = xs := by
  rw [sortFloorBy]
  split
  · rfl
  · omega

theorem sortFloorBy_step (cmp : α → α → Bool) (xs : List α)
    (h : 1 < xs.length) :
    sortFloorBy cmp xs = List.merge (sortFloorBy cmp (xs.take (xs.length / 2)))
      (sortFloorBy cmp (xs.drop (xs.length / 2))) cmp := by
  rw [sortFloorBy]
  split
  · omega
  · rfl

@[simp] theorem sortFloorBy_nil (cmp : α → α → Bool) :
    sortFloorBy cmp [] = [] := sortFloorBy_of_length_le cmp [] (by simp)

@[simp] theorem sortFloorBy_singleton (cmp : α → α → Bool) (x : α) :
    sortFloorBy cmp [x] = [x] := sortFloorBy_of_length_le cmp [x] (by simp)

/-- Permutation uses no order laws for the supplied Boolean comparator. -/
theorem sortFloorBy_perm (cmp : α → α → Bool) (xs : List α) :
    (sortFloorBy cmp xs).Perm xs := by
  by_cases h : xs.length ≤ 1
  · rw [sortFloorBy_of_length_le cmp xs h]
  · rw [sortFloorBy_step cmp xs (by omega)]
    exact (List.merge_perm_append cmp).trans
      (((sortFloorBy_perm cmp _).append (sortFloorBy_perm cmp _)).trans
        (List.Perm.of_eq (List.take_append_drop _ xs)))
termination_by xs.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop]
    omega

theorem sortFloorBy_length (cmp : α → α → Bool) (xs : List α) :
    (sortFloorBy cmp xs).length = xs.length := (sortFloorBy_perm cmp xs).length_eq

theorem mem_sortFloorBy (cmp : α → α → Bool) (xs : List α) (x : α) :
    x ∈ sortFloorBy cmp xs ↔ x ∈ xs := (sortFloorBy_perm cmp xs).mem_iff

/-- Only comparisons on actual input members need respect the observed key order. -/
theorem sortFloorBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (xs : List α)
    (hc : ∀ a ∈ xs, ∀ b ∈ xs, (cmp a b = true → key a ≤ key b) ∧
      (cmp a b = false → key b ≤ key a)) :
    KeySorted key (sortFloorBy cmp xs) := by
  by_cases h : xs.length ≤ 1
  · rw [sortFloorBy_of_length_le cmp xs h]
    cases xs with
    | nil => simp [KeySorted]
    | cons x xs =>
      cases xs with
      | nil => simp [KeySorted]
      | cons y ys => simp at h
  · rw [sortFloorBy_step cmp xs (by omega)]
    apply merge_sorted_compatible_on key cmp
    · intro a ha b hb
      apply hc a _ b _
      · exact List.mem_of_mem_take ((sortFloorBy_perm cmp _).mem_iff.mp ha)
      · exact List.mem_of_mem_drop ((sortFloorBy_perm cmp _).mem_iff.mp hb)
    · exact sortFloorBy_sorted_compatible_on key cmp _ (fun a ha b hb =>
        hc a (List.mem_of_mem_take ha) b (List.mem_of_mem_take hb))
    · exact sortFloorBy_sorted_compatible_on key cmp _ (fun a ha b hb =>
        hc a (List.mem_of_mem_drop ha) b (List.mem_of_mem_drop hb))
termination_by xs.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop]
    omega

abbrev sortFloorOn [LE κ] [DecidableLE κ] (key : α → κ) (xs : List α) : List α :=
  sortFloorBy (fun x y => decide (key x ≤ key y)) xs

theorem sortFloorOn_correct [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    (key : α → κ) (xs : List α) :
    KeySorted key (sortFloorOn key xs) ∧ (sortFloorOn key xs).Perm xs := by
  refine ⟨?_, sortFloorBy_perm _ _⟩
  apply sortFloorBy_sorted_compatible_on key
  intro a _ b _
  exact ⟨of_decide_eq_true, fun h =>
    (Std.le_total (a := key a) (b := key b)).resolve_left (of_decide_eq_false h)⟩

/-- Contiguous splitting and left-biased equal-key merge preserve each occurrence. -/
theorem sortFloorOn_stable [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    [DecidableEq κ] (key : α → κ) (xs : List α) :
    Stable key xs (sortFloorOn key xs) := by
  intro k
  by_cases h : xs.length ≤ 1
  · rw [sortFloorOn, sortFloorBy_of_length_le _ xs h]
  · change (sortFloorBy _ xs).filter _ = _
    rw [sortFloorBy_step _ xs (by omega)]
    change (mergeBy key (sortFloorOn key (xs.take (xs.length / 2)))
      (sortFloorOn key (xs.drop (xs.length / 2)))).filter _ = _
    rw [mergeBy_filter key _ _ (sortFloorOn_correct key _).1
      (sortFloorOn_correct key _).1,
      sortFloorOn_stable key (xs.take (xs.length / 2)) k,
      sortFloorOn_stable key (xs.drop (xs.length / 2)) k,
      ← List.filter_append, List.take_append_drop]
termination_by xs.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop]
    omega

theorem sortFloorOn_spec [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    [DecidableEq κ] (key : α → κ) (xs : List α) :
    StableSort key xs (sortFloorOn key xs) :=
  ⟨(sortFloorOn_correct key xs).1, (sortFloorOn_correct key xs).2,
    sortFloorOn_stable key xs⟩

/-- This equality concerns returned lists, not the different splitting costs. -/
theorem sortFloorOn_eq_sortOn [LE κ] [DecidableLE κ] [Std.IsLinearOrder κ]
    [DecidableEq κ] (key : α → κ) (xs : List α) :
    sortFloorOn key xs = sortOn key xs :=
  (sortFloorOn_spec key xs).unique (sortOn_spec key xs)

end Applications.Sorting
