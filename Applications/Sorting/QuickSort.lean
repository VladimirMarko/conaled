import Applications.Sorting.Stable

/-! First-pivot two-way quicksort and an append-free accumulator realization.
The ordinary recurrence retains both source append occurrences. The strict-left
Boolean partition and its complement preserve occurrences without order laws;
the key specialization identifies the complement with the source nonstrict-right
filter under a linear order. These are value laws, not resource equalities.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting
universe u v
variable {α : Type u} {κ : Type v}

/-- First pivot, strict-left filter, complementary right filter, and two appends. -/
def quickSortBy (lt : α → α → Bool) : List α → List α
  | [] => []
  | pivot :: xs =>
      quickSortBy lt (xs.filter (fun x => lt x pivot)) ++
        ([pivot] ++ quickSortBy lt (xs.filter (fun x => !(lt x pivot))))
termination_by xs => xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

@[simp] theorem quickSortBy_nil (lt : α → α → Bool) :
    quickSortBy lt [] = [] := by rw [quickSortBy]

theorem quickSortBy_cons (lt : α → α → Bool) (pivot : α) (xs : List α) :
    quickSortBy lt (pivot :: xs) =
      quickSortBy lt (xs.filter (fun x => lt x pivot)) ++
        ([pivot] ++ quickSortBy lt (xs.filter (fun x => !(lt x pivot)))) := by
  rw [quickSortBy]

@[simp] theorem quickSortBy_singleton (lt : α → α → Bool) (x : α) :
    quickSortBy lt [x] = [x] := by simp [quickSortBy_cons]

/-- Complementary filtering retains every occurrence, for every Boolean predicate. -/
theorem quickSortBy_perm (lt : α → α → Bool) (xs : List α) :
    (quickSortBy lt xs).Perm xs := by
  match xs with
  | [] => simp
  | pivot :: ys =>
    rw [quickSortBy_cons]
    exact ((quickSortBy_perm lt (ys.filter (fun x => lt x pivot))).append
      ((quickSortBy_perm lt (ys.filter (fun x => !(lt x pivot)))).cons pivot)).trans
        (List.perm_middle.trans ((List.filter_append_perm _ _).cons pivot))
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem quickSortBy_length (lt : α → α → Bool) (xs : List α) :
    (quickSortBy lt xs).length = xs.length := (quickSortBy_perm lt xs).length_eq

theorem mem_quickSortBy (lt : α → α → Bool) (xs : List α) (x : α) :
    x ∈ quickSortBy lt xs ↔ x ∈ xs := (quickSortBy_perm lt xs).mem_iff

/-- Comparator compatibility is required only for members of this input.
The observed key relation needs only transitivity, with no decision procedure. -/
theorem quickSortBy_sorted_compatible_on [LE κ] [IsTrans κ (· ≤ ·)]
    (key : α → κ) (lt : α → α → Bool) (xs : List α)
    (hc : ∀ a ∈ xs, ∀ b ∈ xs, (lt a b = true → key a ≤ key b) ∧
      (lt a b = false → key b ≤ key a)) :
    KeySorted key (quickSortBy lt xs) := by
  match xs with
  | [] => simp [KeySorted]
  | pivot :: ys =>
    rw [quickSortBy_cons]
    have hleft : KeySorted key (quickSortBy lt (ys.filter (fun x => lt x pivot))) :=
      quickSortBy_sorted_compatible_on key lt _ (fun a ha b hb =>
        hc a (List.mem_cons_of_mem pivot (List.mem_filter.mp ha).1)
          b (List.mem_cons_of_mem pivot (List.mem_filter.mp hb).1))
    have hright : KeySorted key
        (quickSortBy lt (ys.filter (fun x => !(lt x pivot)))) :=
      quickSortBy_sorted_compatible_on key lt _ (fun a ha b hb =>
        hc a (List.mem_cons_of_mem pivot (List.mem_filter.mp ha).1)
          b (List.mem_cons_of_mem pivot (List.mem_filter.mp hb).1))
    have hlow : ∀ a ∈ quickSortBy lt (ys.filter (fun x => lt x pivot)),
        key a ≤ key pivot := by
      intro a ha
      have hf := List.mem_filter.mp ((mem_quickSortBy lt _ a).mp ha)
      exact (hc a (List.mem_cons_of_mem pivot hf.1) pivot List.mem_cons_self).1 hf.2
    have hhigh : ∀ b ∈ quickSortBy lt (ys.filter (fun x => !(lt x pivot))),
        key pivot ≤ key b := by
      intro b hb
      have hf := List.mem_filter.mp ((mem_quickSortBy lt _ b).mp hb)
      have hfalse : lt b pivot = false := by simpa using hf.2
      exact (hc b (List.mem_cons_of_mem pivot hf.1) pivot List.mem_cons_self).2 hfalse
    apply List.pairwise_append.mpr
    refine ⟨hleft, List.pairwise_cons.mpr ⟨hhigh, hright⟩, ?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hlow a ha
    · exact Std.le_trans (hlow a ha) (hhigh b hb)
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Keys carry comparison operations; payloads need no order or equality instance. -/
abbrev quickSortOn [LT κ] [DecidableLT κ] (key : α → κ) (xs : List α) : List α :=
  quickSortBy (fun x y => decide (key x < key y)) xs

private theorem right_filter_eq [LinearOrder κ] (key : α → κ)
    (pivot : α) (xs : List α) :
    xs.filter (fun x => !(decide (key x < key pivot))) =
      xs.filter (fun x => decide (key pivot ≤ key x)) := by
  apply List.filter_congr
  intro x _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, not_lt]

/-- This is the exact strict-left/nonstrict-right source recurrence. -/
theorem quickSortOn_cons [LinearOrder κ] (key : α → κ) (pivot : α) (xs : List α) :
    quickSortOn key (pivot :: xs) =
      quickSortOn key (xs.filter (fun x => decide (key x < key pivot))) ++
        ([pivot] ++ quickSortOn key (xs.filter (fun x => decide (key pivot ≤ key x)))) := by
  unfold quickSortOn
  rw [quickSortBy_cons, right_filter_eq]

theorem quickSortOn_correct [LinearOrder κ] (key : α → κ) (xs : List α) :
    KeySorted key (quickSortOn key xs) ∧ (quickSortOn key xs).Perm xs := by
  refine ⟨?_, quickSortBy_perm _ _⟩
  apply quickSortBy_sorted_compatible_on key
  intro a _ b _
  exact ⟨fun h => le_of_lt (of_decide_eq_true h),
    fun h => le_of_not_gt (of_decide_eq_false h)⟩

/-- The right result becomes the suffix of the left call. Assembly uses cons only.
Termination measures the first input, independently of the growing suffix. -/
def quickSortAccBy (lt : α → α → Bool) : List α → List α → List α
  | [], suffix => suffix
  | pivot :: xs, suffix =>
      quickSortAccBy lt (xs.filter (fun x => lt x pivot))
        (pivot :: quickSortAccBy lt (xs.filter (fun x => !(lt x pivot))) suffix)
termination_by xs _ => xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

@[simp] theorem quickSortAccBy_nil (lt : α → α → Bool) (suffix : List α) :
    quickSortAccBy lt [] suffix = suffix := by rw [quickSortAccBy]

theorem quickSortAccBy_cons (lt : α → α → Bool) (pivot : α) (xs suffix : List α) :
    quickSortAccBy lt (pivot :: xs) suffix =
      quickSortAccBy lt (xs.filter (fun x => lt x pivot))
        (pivot :: quickSortAccBy lt (xs.filter (fun x => !(lt x pivot))) suffix) := by
  rw [quickSortAccBy]

@[simp] theorem quickSortAccBy_singleton (lt : α → α → Bool) (x : α) (suffix : List α) :
    quickSortAccBy lt [x] suffix = x :: suffix := by simp [quickSortAccBy_cons]

/-- Every suffix is preserved verbatim; no order law or sorted-suffix premise is used. -/
theorem quickSortAccBy_eq_append (lt : α → α → Bool) (xs suffix : List α) :
    quickSortAccBy lt xs suffix = quickSortBy lt xs ++ suffix := by
  match xs with
  | [] => simp
  | pivot :: ys =>
    calc
      quickSortAccBy lt (pivot :: ys) suffix =
          quickSortAccBy lt (ys.filter (fun x => lt x pivot))
            (pivot :: quickSortAccBy lt (ys.filter (fun x => !(lt x pivot))) suffix) :=
        quickSortAccBy_cons lt pivot ys suffix
      _ = quickSortBy lt (ys.filter (fun x => lt x pivot)) ++
          (pivot :: quickSortAccBy lt (ys.filter (fun x => !(lt x pivot))) suffix) :=
        quickSortAccBy_eq_append lt _ _
      _ = quickSortBy lt (ys.filter (fun x => lt x pivot)) ++
          (pivot :: (quickSortBy lt (ys.filter (fun x => !(lt x pivot))) ++ suffix)) :=
        congrArg (fun tail => quickSortBy lt (ys.filter (fun x => lt x pivot)) ++
          (pivot :: tail)) (quickSortAccBy_eq_append lt _ suffix)
      _ = quickSortBy lt (pivot :: ys) ++ suffix := by
        rw [quickSortBy_cons]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem quickSortAccBy_perm (lt : α → α → Bool) (xs suffix : List α) :
    (quickSortAccBy lt xs suffix).Perm (xs ++ suffix) := by
  rw [quickSortAccBy_eq_append]
  exact (quickSortBy_perm lt xs).append (List.Perm.refl suffix)

abbrev quickSortAccOn [LT κ] [DecidableLT κ] (key : α → κ)
    (xs suffix : List α) : List α :=
  quickSortAccBy (fun x y => decide (key x < key y)) xs suffix

/-- Key specialization of the proposed Exercise 2.2 cons-only solution. -/
theorem quickSortAccOn_cons [LinearOrder κ] (key : α → κ)
    (pivot : α) (xs suffix : List α) :
    quickSortAccOn key (pivot :: xs) suffix =
      quickSortAccOn key (xs.filter (fun x => decide (key x < key pivot)))
        (pivot :: quickSortAccOn key (xs.filter (fun x => decide (key pivot ≤ key x)))
          suffix) := by
  unfold quickSortAccOn
  rw [quickSortAccBy_cons, right_filter_eq]

theorem quickSortAccOn_eq_append [LT κ] [DecidableLT κ]
    (key : α → κ) (xs suffix : List α) :
    quickSortAccOn key xs suffix = quickSortOn key xs ++ suffix :=
  quickSortAccBy_eq_append _ xs suffix

/-- Empty-suffix sorting is a consequence of the all-suffix simulation. -/
theorem quickSortAccOn_correct [LinearOrder κ] (key : α → κ) (xs : List α) :
    KeySorted key (quickSortAccOn key xs []) ∧ (quickSortAccOn key xs []).Perm xs := by
  rw [quickSortAccOn_eq_append, List.append_nil]
  exact quickSortOn_correct key xs

end Applications.Sorting
