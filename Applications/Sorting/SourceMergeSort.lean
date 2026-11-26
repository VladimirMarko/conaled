import Applications.Sorting.SourceMerge
import Applications.Sorting.Alternating

/-!
# VFA's order-preserving alternating merge sort

The splitter retains each alternating subsequence in its original order. It is
distinct from contiguous halves and from reversed accumulator piles. The sort
uses those actual halves and ordinary left-tie merge. Its ordering and occurrence
contracts do not assert stability: alternating split can reorder tied records.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting.SourceMergeSort

universe u v w
variable {α : Type u} {κ : Type v} {β : Type w}

/-- A two-step list induction principle, with separate empty and singleton cases. -/
theorem list_induction_two (P : List α → Prop) (h0 : P [])
    (h1 : ∀ x, P [x]) (hs : ∀ x y xs, P xs → P (x :: y :: xs)) :
    ∀ xs, P xs
  | [] => h0
  | [x] => h1 x
  | x :: y :: xs => hs x y xs (list_induction_two P h0 h1 hs xs)

/-- The source splitter preserves the order within both alternating halves. -/
def split : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: xs => (x :: (split xs).1, y :: (split xs).2)

@[simp] theorem split_nil : split ([] : List α) = ([], []) := rfl

@[simp] theorem split_singleton (x : α) : split [x] = ([x], []) := rfl

theorem split_cons_cons (x y : α) (xs : List α) :
    split (x :: y :: xs) = (x :: (split xs).1, y :: (split xs).2) := rfl

/-- The left side has the extra element when the input length is odd. -/
theorem split_lengths (xs : List α) :
    (split xs).1.length = (xs.length + 1) / 2 ∧
      (split xs).2.length = xs.length / 2 := by
  refine list_induction_two (fun xs : List α =>
    (split xs).1.length = (xs.length + 1) / 2 ∧
      (split xs).2.length = xs.length / 2) ?_ ?_ ?_ xs
  · simp [split]
  · intro x; simp [split]
  · intro x y xs ih
    simp only [split_cons_cons, List.length_cons]
    constructor <;> omega

theorem split_length_add (xs : List α) :
    (split xs).1.length + (split xs).2.length = xs.length := by
  have h := split_lengths xs
  omega

theorem split_length_le (xs : List α) :
    (split xs).1.length ≤ xs.length ∧ (split xs).2.length ≤ xs.length := by
  have h := split_length_add xs
  omega

/-- Both recursive arguments strictly decrease exactly at the recursive cases. -/
theorem split_length_lt (xs : List α) (h : 1 < xs.length) :
    (split xs).1.length < xs.length ∧ (split xs).2.length < xs.length := by
  have hs := split_lengths xs
  omega

theorem split_perm (xs : List α) : xs.Perm ((split xs).1 ++ (split xs).2) := by
  refine list_induction_two (fun xs : List α =>
    xs.Perm ((split xs).1 ++ (split xs).2)) ?_ ?_ ?_ xs
  · simp [split]
  · intro x; simp [split]
  · intro x y xs ih
    simp only [split_cons_cons, List.cons_append]
    exact (ih.cons y |>.cons x).trans (List.perm_middle.symm.cons x)

/-- Each half retains the relative order of its occurrences from the input. -/
theorem split_sublists (xs : List α) :
    (split xs).1.Sublist xs ∧ (split xs).2.Sublist xs := by
  refine list_induction_two (fun xs : List α =>
    (split xs).1.Sublist xs ∧ (split xs).2.Sublist xs) ?_ ?_ ?_ xs
  · simp [split]
  · intro x; simp [split]
  · intro x y xs ih
    exact ⟨(ih.1.cons y).cons_cons x, (ih.2.cons_cons y).cons x⟩

theorem split_map (f : α → β) (xs : List α) :
    split (xs.map f) = ((split xs).1.map f, (split xs).2.map f) := by
  refine list_induction_two (fun xs : List α =>
    split (xs.map f) = ((split xs).1.map f, (split xs).2.map f)) ?_ ?_ ?_ xs
  · rfl
  · intro x; rfl
  · intro x y xs ih
    simp only [List.map_cons, split_cons_cons, ih]

/-- FDSA's accumulator splitter reverses each VFA subsequence before retaining
the supplied accumulator. Equality of sorted outputs would not identify these
intermediate lists; this theorem relates the actual splitting recurrences. -/
theorem halve_eq_reverse_split (xs left right : List α) :
    halve xs (left, right) =
      ((split xs).1.reverse ++ left, (split xs).2.reverse ++ right) := by
  refine list_induction_two (fun xs : List α => ∀ left right,
    halve xs (left, right) =
      ((split xs).1.reverse ++ left, (split xs).2.reverse ++ right)) ?_ ?_ ?_ xs left right
  · intro left right; rfl
  · intro x left right; rfl
  · intro x y xs ih left right
    rw [halve_cons_cons, ih, split_cons_cons]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- The source's length-founded recurrence, generalized to any Boolean comparator. -/
def sortBy (cmp : α → α → Bool) (xs : List α) : List α :=
  if _h : xs.length ≤ 1 then xs
  else List.merge (sortBy cmp (split xs).1) (sortBy cmp (split xs).2) cmp
termination_by xs.length
decreasing_by
  all_goals have hl := split_length_lt xs (by omega); omega

theorem sortBy_of_length_le (cmp : α → α → Bool) (xs : List α)
    (h : xs.length ≤ 1) : sortBy cmp xs = xs := by
  rw [sortBy]
  split
  · rfl
  · omega

theorem sortBy_step (cmp : α → α → Bool) (xs : List α) (h : 1 < xs.length) :
    sortBy cmp xs = List.merge (sortBy cmp (split xs).1) (sortBy cmp (split xs).2) cmp := by
  rw [sortBy]
  split
  · omega
  · rfl

@[simp] theorem sortBy_nil (cmp : α → α → Bool) : sortBy cmp [] = [] :=
  sortBy_of_length_le cmp [] (by simp)

@[simp] theorem sortBy_singleton (cmp : α → α → Bool) (x : α) :
    sortBy cmp [x] = [x] := sortBy_of_length_le cmp [x] (by simp)

/-- Induction follows the two actual recursive source calls and their returned values. -/
theorem sortBy_induction (cmp : α → α → Bool) (P : List α → List α → Prop)
    (h0 : P [] []) (h1 : ∀ x, P [x] [x])
    (hs : ∀ xs, 1 < xs.length →
      P (split xs).1 (sortBy cmp (split xs).1) →
      P (split xs).2 (sortBy cmp (split xs).2) →
      P xs (List.merge (sortBy cmp (split xs).1) (sortBy cmp (split xs).2) cmp))
    (xs : List α) : P xs (sortBy cmp xs) := by
  by_cases h : xs.length ≤ 1
  · rw [sortBy_of_length_le cmp xs h]
    cases xs with
    | nil => exact h0
    | cons x xs =>
        cases xs with
        | nil => exact h1 x
        | cons y ys => simp at h
  · rw [sortBy_step cmp xs (by omega)]
    exact hs xs (by omega)
      (sortBy_induction cmp P h0 h1 hs (split xs).1)
      (sortBy_induction cmp P h0 h1 hs (split xs).2)
termination_by xs.length
decreasing_by
  all_goals have hl := split_length_lt xs (by omega); omega

/-- Occurrence preservation needs no laws at all for the comparator. -/
theorem sortBy_perm (cmp : α → α → Bool) (xs : List α) : (sortBy cmp xs).Perm xs := by
  refine sortBy_induction cmp (fun xs ys => ys.Perm xs) ?_ ?_ ?_ xs
  · rfl
  · intro x; rfl
  · intro xs _ hl hr
    exact (List.merge_perm_append cmp).trans ((hl.append hr).trans (split_perm xs).symm)

theorem sortBy_length (cmp : α → α → Bool) (xs : List α) :
    (sortBy cmp xs).length = xs.length := (sortBy_perm cmp xs).length_eq

theorem mem_sortBy (cmp : α → α → Bool) (xs : List α) (x : α) :
    x ∈ sortBy cmp xs ↔ x ∈ xs := (sortBy_perm cmp xs).mem_iff

/-- Only comparisons between actual input members need agree with key order. -/
theorem sortBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (xs : List α)
    (hc : ∀ a ∈ xs, ∀ b ∈ xs, (cmp a b = true → key a ≤ key b) ∧
      (cmp a b = false → key b ≤ key a)) : KeySorted key (sortBy cmp xs) := by
  by_cases h : xs.length ≤ 1
  · rw [sortBy_of_length_le cmp xs h]
    cases xs with
    | nil => simp [KeySorted]
    | cons x xs =>
        cases xs with
        | nil => simp [KeySorted]
        | cons y ys => simp at h
  · rw [sortBy_step cmp xs (by omega)]
    apply merge_sorted_compatible_on key cmp
    · intro a ha b hb
      exact hc a ((split_sublists xs).1.subset ((sortBy_perm cmp _).mem_iff.mp ha))
        b ((split_sublists xs).2.subset ((sortBy_perm cmp _).mem_iff.mp hb))
    · exact sortBy_sorted_compatible_on key cmp _ (fun a ha b hb =>
        hc a ((split_sublists xs).1.subset ha) b ((split_sublists xs).1.subset hb))
    · exact sortBy_sorted_compatible_on key cmp _ (fun a ha b hb =>
        hc a ((split_sublists xs).2.subset ha) b ((split_sublists xs).2.subset hb))
termination_by xs.length
decreasing_by
  all_goals have hl := split_length_lt xs (by omega); omega

abbrev sortOn [LE κ] [DecidableLE κ] (key : α → κ) (xs : List α) : List α :=
  sortBy (fun x y => decide (key x ≤ key y)) xs

/-- Key ordering does not require an order or equality test on the payloads. -/
theorem sortOn_correct [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    (key : α → κ) (xs : List α) :
    KeySorted key (sortOn key xs) ∧ (sortOn key xs).Perm xs := by
  refine ⟨?_, sortBy_perm _ _⟩
  apply sortBy_sorted_compatible_on key
  intro a _ b _
  exact ⟨of_decide_eq_true, fun h =>
    (Std.le_total (a := key a) (b := key b)).resolve_left (of_decide_eq_false h)⟩

end Applications.Sorting.SourceMergeSort
