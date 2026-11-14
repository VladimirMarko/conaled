import Applications.Selection.CountRank

/-!
Single-pass selection of a fixed small occurrence rank, FDSA Exercises 3.1–3.3.

The outer loops consume the original list in tail position. The general loop
retains at most `k + 1` sorted occurrences; insertion and truncation traverse
only that bounded accumulator. Empty and invalid inputs return `none`, and
equal occurrences are retained. The book indices here are zero-based; the
existing public selector remains one-based. Source call counts for these
actual constructions are in `Applications.Resources.FixedRank`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection.FixedRank
universe u
variable {α : Type u} [LinearOrder α]

/-- Tail-recursive minimum with an already observed candidate. -/
def minimumLoop (best : α) : List α → α
  | [] => best
  | x :: xs => minimumLoop (min best x) xs

/-- A nonempty input supplies its own initial candidate. -/
def select0 : List α → Option α
  | [] => none
  | x :: xs => some (minimumLoop x xs)

theorem minimumLoop_spec (best : α) (xs : List α) :
    minimumLoop best xs ∈ best :: xs ∧
      ∀ y ∈ best :: xs, minimumLoop best xs ≤ y := by
  induction xs generalizing best with
  | nil => simp [minimumLoop]
  | cons x xs ih =>
      obtain ⟨hm, hlo⟩ := ih (min best x)
      change minimumLoop (min best x) xs ∈ best :: x :: xs ∧
        ∀ y ∈ best :: x :: xs, minimumLoop (min best x) xs ≤ y
      constructor
      · rcases List.mem_cons.mp hm with hm | hm
        · rw [hm]
          by_cases h : best ≤ x
          · simp [min_eq_left h]
          · simp [min_eq_right (le_of_not_ge h)]
        · exact List.mem_cons_of_mem best (List.mem_cons_of_mem x hm)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_trans (hlo _ List.mem_cons_self) (min_le_left _ _)
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_trans (hlo _ List.mem_cons_self) (min_le_right _ _)
        · exact hlo y (List.mem_cons_of_mem _ hy)

theorem select0_none_iff (xs : List α) : select0 xs = none ↔ xs = [] := by
  cases xs <;> simp [select0]

theorem select0_some_iff_min (xs : List α) (a : α) :
    select0 xs = some a ↔ a ∈ xs ∧ ∀ x ∈ xs, a ≤ x := by
  cases xs with
  | nil => simp [select0]
  | cons x xs =>
      constructor
      · intro h
        have ha : minimumLoop x xs = a := Option.some.inj h
        rw [← ha]
        exact minimumLoop_spec x xs
      · intro h
        have hm := minimumLoop_spec x xs
        have ha : minimumLoop x xs = a :=
          le_antisymm (hm.2 a h.1) (h.2 _ hm.1)
        exact congrArg some ha

theorem select0_value (xs : List α) : select0 xs = (ordered xs)[0]? := by
  cases h : select0 xs with
  | none =>
      have hx := (select0_none_iff xs).mp h
      subst xs
      simp [ordered, Applications.Sorting.sortOn_eq_insertionOn,
        Applications.Sorting.insertionOn]
  | some a =>
      exact (ordered_getElem?_zero_iff_min.mpr
        ((select0_some_iff_min xs a).mp h)).symm

theorem select0_some_iff_ranked (xs : List α) (a : α) :
    select0 xs = some a ↔ RankedAt xs 0 a := by
  rw [select0_value, ranked_iff_index]

theorem select0_pivot_valid : PivotValid (select0 : List α → Option α) := by
  intro xs hx
  cases xs with
  | nil => exact (hx rfl).elim
  | cons x xs => exact ⟨minimumLoop x xs, rfl, (minimumLoop_spec x xs).1⟩

theorem select0_spec (xs : List α) (hx : xs ≠ []) :
    ∃ a, select0 xs = some a ∧ RankedAt xs 0 a := by
  obtain ⟨a, ha, _⟩ := select0_pivot_valid xs hx
  exact ⟨a, ha, (select0_some_iff_ranked xs a).mp ha⟩

/-- Keep the two smallest occurrences seen so far; ties are not removed. -/
def secondLoop (lo hi : α) : List α → α
  | [] => hi
  | x :: xs =>
      if x ≤ lo then secondLoop x lo xs
      else secondLoop lo (min x hi) xs

/-- Exercise 3.2's actual one-pass adaptation. Its correctness is derived
below from the width-two instance of Exercise 3.3. -/
def select1 : List α → Option α
  | [] => none
  | [_] => none
  | x :: y :: xs => some (secondLoop (min x y) (max x y) xs)

/-- Insert one occurrence and keep only the first `m` accumulator entries. -/
def boundedInsert (m : Nat) (x : α) (acc : List α) : List α :=
  (List.orderedInsert (· ≤ ·) x acc).take m

theorem boundedInsert_length_le (m : Nat) (x : α) (acc : List α) :
    (boundedInsert m x acc).length ≤ m := by
  rw [boundedInsert, List.length_take]
  exact Nat.min_le_left _ _

private theorem take_orderedInsert_take (m : Nat) (x : α) (ys : List α) :
    (List.orderedInsert (· ≤ ·) x (ys.take m)).take m =
      (List.orderedInsert (· ≤ ·) x ys).take m := by
  induction ys generalizing m with
  | nil => simp
  | cons y ys ih =>
      cases m with
      | zero => rfl
      | succ m =>
          by_cases h : x ≤ y
          · simp only [List.take_succ_cons, List.orderedInsert_cons, h, ↓reduceIte]
            apply congrArg (List.cons x)
            change ((y :: ys).take (m + 1)).take m = (y :: ys).take m
            rw [List.take_take, Nat.min_eq_left (Nat.le_succ m)]
          · simp only [List.take_succ_cons, List.orderedInsert_cons, h, ↓reduceIte]
            exact congrArg (List.cons y) (ih m)

theorem ordered_cons_eq_insert (x : α) (xs : List α) :
    ordered (x :: xs) = List.orderedInsert (· ≤ ·) x (ordered xs) := by
  simp only [ordered, Applications.Sorting.sortOn_eq_insertionOn,
    Applications.Sorting.insertionOn, List.insertionSort_cons, id_eq]

theorem boundedInsert_prefix (m : Nat) (x : α) (seen : List α) :
    boundedInsert m x ((ordered seen).take m) = (ordered (x :: seen)).take m := by
  rw [boundedInsert, take_orderedInsert_take, ordered_cons_eq_insert]

/-- The original input tail is the sole recursive argument consumed here. -/
def prefixLoop (m : Nat) (acc : List α) : List α → List α
  | [] => acc
  | x :: xs => prefixLoop m (boundedInsert m x acc) xs

/-- The reversed history is a proof invariant, not an algorithmic reversal. -/
theorem prefixLoop_prefix (m : Nat) (seen xs : List α) :
    prefixLoop m ((ordered seen).take m) xs =
      (ordered (xs.reverse ++ seen)).take m := by
  induction xs generalizing seen with
  | nil => simp [prefixLoop]
  | cons x xs ih =>
      rw [prefixLoop, boundedInsert_prefix, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

def takeSort (m : Nat) (xs : List α) : List α := prefixLoop m [] xs

theorem takeSort_value (m : Nat) (xs : List α) :
    takeSort m xs = (ordered xs).take m := by
  have h := prefixLoop_prefix m ([] : List α) xs
  rw [show ordered ([] : List α) = [] from by
        simp [ordered, Applications.Sorting.sortOn_eq_insertionOn,
          Applications.Sorting.insertionOn], List.take_nil, List.append_nil,
    ordered_eq_of_perm (List.reverse_perm xs)] at h
  exact h

theorem takeSort_length (m : Nat) (xs : List α) :
    (takeSort m xs).length = min m xs.length := by
  rw [takeSort_value, List.length_take, (ordered_perm xs).length_eq]

/-- Zero-based fixed-rank selection, including optional failure for `k ≥ n`. -/
def selectFixed (k : Nat) (xs : List α) : Option α := (takeSort (k + 1) xs)[k]?

theorem selectFixed_value (k : Nat) (xs : List α) :
    selectFixed k xs = (ordered xs)[k]? := by
  rw [selectFixed, takeSort_value, List.getElem?_take_of_succ]

theorem selectFixed_some_iff_ranked (k : Nat) (xs : List α) (a : α) :
    selectFixed k xs = some a ↔ RankedAt xs k a := by
  rw [selectFixed_value, ranked_iff_index]

theorem selectFixed_some_iff_count_bounds (k : Nat) (xs : List α) (a : α) :
    selectFixed k xs = some a ↔
      xs.countP (fun x => decide (x < a)) ≤ k ∧
        xs.countP (fun x => decide (a < x)) < xs.length - k := by
  rw [selectFixed_some_iff_ranked, ranked_iff_count_bounds]

theorem selectFixed_none_iff (k : Nat) (xs : List α) :
    selectFixed k xs = none ↔ xs.length ≤ k := by
  rw [selectFixed_value, List.getElem?_eq_none_iff, (ordered_perm xs).length_eq]

theorem selectFixed_spec (k : Nat) (xs : List α) (hk : k < xs.length) :
    ∃ a, selectFixed k xs = some a ∧ RankedAt xs k a := by
  cases h : selectFixed k xs with
  | none =>
      have hn := (selectFixed_none_iff k xs).mp h
      omega
  | some a => exact ⟨a, rfl, (selectFixed_some_iff_ranked k xs a).mp h⟩

/-- The shared public selector uses rank `k + 1` for the book index `k`. -/
theorem selectFixed_eq_selectWith (choose : List α → Option α)
    (hv : PivotValid choose) (k : Nat) (xs : List α) :
    selectFixed k xs = selectWith choose (k + 1) xs := by
  rw [selectFixed_value, selectWith_succ_value choose hv]

theorem select0_eq_selectFixed (xs : List α) : select0 xs = selectFixed 0 xs := by
  rw [select0_value, selectFixed_value]

/-- This step identity is valid even before imposing an order on `lo, hi`.
The initial pair in `select1` is sorted by `min` and `max`. -/
theorem boundedInsert_two (x lo hi : α) :
    boundedInsert 2 x [lo, hi] =
      if x ≤ lo then [x, lo] else [lo, min x hi] := by
  by_cases hx : x ≤ lo
  · simp [boundedInsert, List.orderedInsert, hx]
  · by_cases hh : x ≤ hi
    · rw [ite_eq_right hx, min_eq_left hh]
      simp [boundedInsert, List.orderedInsert, hx, hh]
    · rw [ite_eq_right hx, min_eq_right (le_of_not_ge hh)]
      simp [boundedInsert, List.orderedInsert, hx, hh]

/-- Exact correspondence of the two actual tail loops, not just their final
rank specifications. -/
theorem prefixLoop_two (lo hi : α) (xs : List α) :
    (prefixLoop 2 [lo, hi] xs)[1]? = some (secondLoop lo hi xs) := by
  induction xs generalizing lo hi with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : x ≤ lo
      · simp only [prefixLoop, boundedInsert_two, secondLoop, h, ↓reduceIte]
        exact ih x lo
      · simp only [prefixLoop, boundedInsert_two, secondLoop, h, ↓reduceIte]
        exact ih lo (min x hi)

theorem boundedInsert_singleton (x y : α) :
    boundedInsert 2 y [x] = [min x y, max x y] := by
  by_cases h : y ≤ x
  · rw [min_eq_right h, max_eq_left h]
    simp [boundedInsert, List.orderedInsert, h]
  · have hxy : x ≤ y := le_of_not_ge h
    rw [min_eq_left hxy, max_eq_right hxy]
    simp [boundedInsert, List.orderedInsert, h]

/-- Exercise 3.3(2): derive the specialized algorithm from the width-two loop. -/
theorem select1_eq_selectFixed (xs : List α) : select1 xs = selectFixed 1 xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y xs =>
          change some (secondLoop (min x y) (max x y) xs) =
            (prefixLoop 2 (boundedInsert 2 y [x]) xs)[1]?
          rw [boundedInsert_singleton, prefixLoop_two]

theorem select1_value (xs : List α) : select1 xs = (ordered xs)[1]? := by
  rw [select1_eq_selectFixed, selectFixed_value]

theorem select1_some_iff_ranked (xs : List α) (a : α) :
    select1 xs = some a ↔ RankedAt xs 1 a := by
  rw [select1_eq_selectFixed, selectFixed_some_iff_ranked]

theorem select1_none_iff (xs : List α) : select1 xs = none ↔ xs.length ≤ 1 := by
  rw [select1_eq_selectFixed, selectFixed_none_iff]

theorem select1_spec (xs : List α) (hx : 1 < xs.length) :
    ∃ a, select1 xs = some a ∧ RankedAt xs 1 a := by
  rw [select1_eq_selectFixed]
  exact selectFixed_spec 1 xs hx

end Applications.Selection.FixedRank
