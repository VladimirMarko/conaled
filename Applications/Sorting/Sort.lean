import Applications.Sorting.Merge

/-! Merge sort and insertion sort share the independent stable-sorting contract. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting
open List
universe u v w
variable {α : Type u} {β : Type v} {κ : Type w}

abbrev sortBy (cmp : α → α → Bool) (xs : List α) : List α := xs.mergeSort cmp

abbrev sortOn [LE κ] [DecidableLE κ] (key : α → κ) (xs : List α) : List α :=
  sortBy (fun x y => decide (key x ≤ key y)) xs

abbrev insertionOn [LE κ] [DecidableLE κ] (key : α → κ) (xs : List α) : List α :=
  xs.insertionSort (fun x y => key x ≤ key y)

theorem sortBy_perm (cmp : α → α → Bool) (xs : List α) :
    (sortBy cmp xs).Perm xs := List.mergeSort_perm xs cmp

theorem sortBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (xs : List α)
    (hc : ∀ a ∈ xs, ∀ b ∈ xs, (cmp a b = true → key a ≤ key b) ∧
      (cmp a b = false → key b ≤ key a)) :
    KeySorted key (sortBy cmp xs) := by
  match xs with
  | [] => simp [sortBy, KeySorted]
  | [x] => simp [sortBy, KeySorted]
  | x :: y :: xs => 
    rw [sortBy, List.mergeSort]
    simp only [List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd]
    apply merge_sorted_compatible_on key cmp
    · intro a ha b hb
      apply hc a _ b _
      · apply List.mem_of_mem_take
        exact (List.mergeSort_perm _ cmp).mem_iff.mp ha
      · apply List.mem_of_mem_drop
        exact (List.mergeSort_perm _ cmp).mem_iff.mp hb
    · exact sortBy_sorted_compatible_on key cmp _ (fun a ha b hb => hc a
        (List.mem_of_mem_take ha) b (List.mem_of_mem_take hb))
    · exact sortBy_sorted_compatible_on key cmp _ (fun a ha b hb => hc a
        (List.mem_of_mem_drop ha) b (List.mem_of_mem_drop hb))
termination_by xs.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop, List.length_cons]
    omega

theorem sortBy_sorted_compatible [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool)
    (hc : ∀ a b, (cmp a b = true → key a ≤ key b) ∧
      (cmp a b = false → key b ≤ key a)) (xs : List α) :
    KeySorted key (sortBy cmp xs) :=
  sortBy_sorted_compatible_on key cmp xs (fun a _ b _ => hc a b)

theorem sortOn_correct [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    (key : α → κ) (xs : List α) :
    KeySorted key (sortOn key xs) ∧ (sortOn key xs).Perm xs := by
  refine ⟨?_, sortBy_perm _ _⟩
  apply sortBy_sorted_compatible key
  intro a b
  exact ⟨of_decide_eq_true, fun h => 
    (Std.le_total (a := key a) (b := key b)).resolve_left (of_decide_eq_false h)⟩

theorem sortOn_stable [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ] [DecidableEq κ]
    (key : α → κ) (xs : List α) : Stable key xs (sortOn key xs) := by
  apply stable_of_sublist key (sortBy_perm _ _)
  intro k
  apply List.sublist_mergeSort (le := fun a b => decide (key a ≤ key b))
  · intro a b c hab hbc
    exact decide_eq_true (Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  · intro a b
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using
      (Std.le_total (a := key a) (b := key b))
  · apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    have ha' : key a = k := of_decide_eq_true (List.mem_filter.mp ha).2
    have hb' : key b = k := of_decide_eq_true (List.mem_filter.mp hb).2
    simp only [ha', hb', decide_eq_true_eq]
    exact Std.le_refl _
  · exact List.filter_sublist

theorem sortOn_spec [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ] [DecidableEq κ]
    (key : α → κ) (xs : List α) : StableSort key xs (sortOn key xs) :=
  ⟨(sortOn_correct key xs).1, (sortOn_correct key xs).2, sortOn_stable key xs⟩

theorem sortOn_sorted_fixed [LE κ] [DecidableLE κ]
    (key : α → κ) (xs : List α) (hx : KeySorted key xs) : sortOn key xs = xs := by
  apply List.mergeSort_of_pairwise
  simpa only [KeySorted, decide_eq_true_eq] using hx

theorem insertionOn_spec [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ] [DecidableEq κ]
    (key : α → κ) (xs : List α) : StableSort key xs (insertionOn key xs) := by
  let r := fun a b : α => key a ≤ key b
  let : Std.Total r := ⟨fun a b => Std.le_total (a := key a) (b := key b)⟩
  let : IsTrans α r := ⟨fun _ _ _ hab hbc => Std.le_trans hab hbc⟩
  refine ⟨List.pairwise_insertionSort r xs, List.perm_insertionSort r xs, ?_⟩
  apply stable_of_sublist key (List.perm_insertionSort r xs)
  intro k
  apply List.sublist_insertionSort
  · apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    have ha' : key a = k := of_decide_eq_true (List.mem_filter.mp ha).2
    have hb' : key b = k := of_decide_eq_true (List.mem_filter.mp hb).2
    change key a ≤ key b
    rw [ha', hb']
    exact Std.le_refl _
  · exact List.filter_sublist

/-- Agreement follows from independent observations, with no order on payloads. -/
theorem sortOn_eq_insertionOn [LE κ] [DecidableLE κ] [Std.IsLinearOrder κ] [DecidableEq κ]
    (key : α → κ) (xs : List α) : sortOn key xs = insertionOn key xs :=
  (sortOn_spec key xs).unique (insertionOn_spec key xs)

/-- Sorted-block merging and whole-input sorting have the same stable observation. -/
theorem mergeBy_eq_sortOn [LE κ] [DecidableLE κ] [Std.IsLinearOrder κ] [DecidableEq κ]
    (key : α → κ) (xs ys : List α) (hx : KeySorted key xs) (hy : KeySorted key ys) :
    mergeBy key xs ys = sortOn key (xs ++ ys) :=
  (mergeBy_spec key xs ys hx hy).unique (sortOn_spec key (xs ++ ys))

theorem sortOn_map [LE κ] [DecidableLE κ] [Std.IsLinearOrder κ] [DecidableEq κ]
    (key : α → κ) (key' : β → κ) (f : α → β) (hf : ∀ x, key' (f x) = key x)
    (xs : List α) : sortOn key' (xs.map f) = (sortOn key xs).map f :=
  (sortOn_spec key' _).unique ((sortOn_spec key xs).map f hf)

end Applications.Sorting
