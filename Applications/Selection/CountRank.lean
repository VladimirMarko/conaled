import Applications.Selection.Consumers

/-!
Occurrence-count characterizations of selection, including duplicates.

The zero-based specification is the existing RankedAt relation. The public
selector remains one-based and partial through Option. These laws connect the
two interfaces without imposing distinctness or choosing an inhabitant for an
empty input type. They cover the elementary selection arguments in FDSA §3.1.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection
universe u
variable {α : Type u}

theorem RankedAt.mem [LE α] {xs : List α} {k : Nat} {a : α}
    (h : RankedAt xs k a) : a ∈ xs := by
  obtain ⟨pre, post, hp, _, _, _⟩ := h
  exact hp.mem_iff.mp (by simp)

theorem RankedAt.lt_length [LE α] {xs : List α} {k : Nat} {a : α}
    (h : RankedAt xs k a) : k < xs.length := by
  obtain ⟨pre, post, hp, hk, _, _⟩ := h
  have hl := hp.length_eq
  simp only [List.length_append, List.length_cons] at hl
  omega

variable [LinearOrder α]

/-- Equal occurrences may surround the chosen occurrence. Strict counts are
therefore bounded, rather than equal to the chosen index. -/
theorem RankedAt.count_bounds {xs : List α} {k : Nat} {a : α}
    (h : RankedAt xs k a) :
    xs.countP (fun x => decide (x < a)) ≤ k ∧
      xs.countP (fun x => decide (a < x)) < xs.length - k := by
  obtain ⟨pre, post, hp, hk, hlo, hhi⟩ := h
  have hpr : pre.countP (fun x => decide (a < x)) = 0 :=
    List.countP_eq_zero.mpr (fun x hx => by
      simpa only [decide_eq_true_eq] using not_lt_of_ge (hlo x hx))
  have hql : post.countP (fun x => decide (x < a)) = 0 :=
    List.countP_eq_zero.mpr (fun x hx => by
      simpa only [decide_eq_true_eq] using not_lt_of_ge (hhi x hx))
  have hpl : pre.countP (fun x => decide (x < a)) ≤ pre.length :=
    List.countP_le_length
  have hqr : post.countP (fun x => decide (a < x)) ≤ post.length :=
    List.countP_le_length
  have hl := hp.countP_eq (fun x => decide (x < a))
  have hr := hp.countP_eq (fun x => decide (a < x))
  have hlen := hp.length_eq
  simp only [List.countP_append, List.countP_cons, lt_self_iff_false,
    decide_false, Bool.false_eq_true, ↓reduceIte, hpr, hql,
    List.length_append, List.length_cons] at hl hr hlen
  omega

/-- The middle branch supplies the nonempty equal block; the pivot need not
have been assumed to occur in the input. -/
theorem partition_equal_getElem? (p : α) (xs : List α) (j : Nat)
    (hj : j < (partition3 p xs).2.1.length) :
    (partition3 p xs).2.1[j]? = some p := by
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨hj, ?_⟩
  exact ((partition_equal_mem p xs _).mp (List.getElem_mem hj)).2

/-- The literal book branches are valid for an arbitrary pivot, even outside
the input range. This is a value law, without a termination claim. -/
theorem ordered_getElem?_partition (p : α) (xs : List α) (k : Nat) :
    (ordered xs)[k]? =
      if k < (partition3 p xs).1.length then
        (ordered (partition3 p xs).1)[k]?
      else if k < (partition3 p xs).1.length + (partition3 p xs).2.1.length then
        some p
      else
        (ordered (partition3 p xs).2.2)
          [k - (partition3 p xs).1.length - (partition3 p xs).2.1.length]? := by
  rw [← dispatch_value (fun j ys => (ordered ys)[j]?) p k xs
    (fun _ => rfl) (fun _ => rfl)]
  unfold dispatch
  by_cases hl : k < (partition3 p xs).1.length
  · simp only [hl, ↓reduceIte]
  · by_cases he : k < (partition3 p xs).1.length + (partition3 p xs).2.1.length
    · simp only [hl, he, ↓reduceIte]
      exact partition_equal_getElem? p xs _ (by omega)
    · simp only [hl, he, ↓reduceIte]

/-- The strict upper-count inequality already implies a valid input index;
no separate nonempty, in-bounds, or distinctness hypothesis is needed. -/
theorem ranked_iff_count_bounds {xs : List α} {k : Nat} {a : α} :
    RankedAt xs k a ↔
      xs.countP (fun x => decide (x < a)) ≤ k ∧
        xs.countP (fun x => decide (a < x)) < xs.length - k := by
  refine ⟨RankedAt.count_bounds, ?_⟩
  intro h
  have hl : (partition3 a xs).1.length ≤ k := by
    simpa only [partition3_eq_filters, List.countP_eq_length_filter] using h.1
  have hg : (partition3 a xs).2.2.length < xs.length - k := by
    simpa only [partition3_eq_filters, List.countP_eq_length_filter] using h.2
  have hlen := partition_lengths a xs
  have he : k < (partition3 a xs).1.length + (partition3 a xs).2.1.length := by
    omega
  apply ranked_iff_index.mpr
  rw [ordered_getElem?_partition a xs k, if_neg (by omega), if_pos he]

theorem count_bounds_unique {xs : List α} {k : Nat} {a b : α}
    (ha : xs.countP (fun x => decide (x < a)) ≤ k ∧
      xs.countP (fun x => decide (a < x)) < xs.length - k)
    (hb : xs.countP (fun x => decide (x < b)) ≤ k ∧
      xs.countP (fun x => decide (b < x)) < xs.length - k) : a = b :=
  (ranked_iff_count_bounds.mpr ha).unique (ranked_iff_count_bounds.mpr hb)

/-- The sublist statement in particular preserves occurrence multiplicities
in the source's submultiset argument. -/
theorem filter_le_sublist_filter_lt (xs : List α) {a b : α} (hab : a < b) :
    xs.filter (fun x => decide (x ≤ a)) <+
      xs.filter (fun x => decide (x < b)) := by
  apply List.sublist_filter_iff.mpr
  refine ⟨xs.filter (fun x => decide (x ≤ a)), List.filter_sublist, ?_⟩
  symm
  apply List.filter_eq_self.mpr
  intro x hx
  simp only [List.mem_filter, decide_eq_true_eq] at hx
  simpa only [decide_eq_true_eq] using lt_of_le_of_lt hx.2 hab

theorem count_le_add_count_gt (xs : List α) (a : α) :
    xs.countP (fun x => decide (x ≤ a)) +
      xs.countP (fun x => decide (a < x)) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ≤ a
    · simp only [List.countP_cons, hx, decide_true,
        show ¬a < x from not_lt_of_ge hx, decide_false,
        Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have hax : a < x := lt_of_not_ge hx
      simp only [List.countP_cons, hx, hax, decide_true, decide_false,
        Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega

theorem ordered_eq_of_pairwise_perm {xs ys : List α}
    (hs : ys.Pairwise (· ≤ ·)) (hp : ys.Perm xs) : ordered xs = ys := by
  exact ((ordered_perm xs).trans hp.symm).eq_of_pairwise
    (fun _ _ _ _ hab hba => le_antisymm hab hba) (ordered_pairwise xs) hs

theorem ordered_eq_of_perm {xs ys : List α} (hp : xs.Perm ys) :
    ordered xs = ordered ys :=
  ordered_eq_of_pairwise_perm (ordered_pairwise ys) ((ordered_perm ys).trans hp.symm)

/-- Permutation invariance includes invalid indices through the Option result. -/
theorem ordered_getElem?_perm {xs ys : List α} (hp : xs.Perm ys) (k : Nat) :
    (ordered xs)[k]? = (ordered ys)[k]? := by rw [ordered_eq_of_perm hp]

/-- Book index zero corresponds to public rank one, not public failure rank zero. -/
theorem selectWith_succ_value (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (k : Nat) : selectWith choose (k + 1) xs = (ordered xs)[k]? := by
  simpa using selectWith_value choose hv xs (k + 1) (by omega)

theorem selectWith_succ_some_iff_count_bounds (choose : List α → Option α)
    (hv : PivotValid choose) (xs : List α) (k : Nat) (a : α) :
    selectWith choose (k + 1) xs = some a ↔
      xs.countP (fun x => decide (x < a)) ≤ k ∧
        xs.countP (fun x => decide (a < x)) < xs.length - k := by
  rw [selectWith_succ_value choose hv xs k, ← ranked_iff_index, ranked_iff_count_bounds]

theorem ordered_getElem?_mem {xs : List α} {k : Nat} {a : α}
    (ha : (ordered xs)[k]? = some a) : a ∈ xs :=
  (ranked_iff_index.mpr ha).mem

theorem ranked_zero_iff_min {xs : List α} {a : α} :
    RankedAt xs 0 a ↔ a ∈ xs ∧ ∀ x ∈ xs, a ≤ x := by
  constructor
  · intro h
    refine ⟨h.mem, ?_⟩
    obtain ⟨pre, post, hp, hk, _, hhi⟩ := h
    have he : pre = [] := List.length_eq_zero_iff.mp hk
    subst pre
    intro x hx
    have hx' : x ∈ a :: post := hp.mem_iff.mpr hx
    rcases List.mem_cons.mp hx' with rfl | hx'
    · exact le_rfl
    · exact hhi x hx'
  · rintro ⟨ha, hlo⟩
    have hl : xs.countP (fun x => decide (x < a)) = 0 :=
      List.countP_eq_zero.mpr (fun x hx => by
        simpa only [decide_eq_true_eq] using not_lt_of_ge (hlo x hx))
    have hg : xs.countP (fun x => decide (a < x)) < xs.length := by
      have hle : xs.countP (fun x => decide (a < x)) ≤ xs.length :=
        List.countP_le_length
      by_contra h
      have he : xs.countP (fun x => decide (a < x)) = xs.length := by omega
      have hself := (List.countP_eq_length.mp he) a ha
      simpa using hself
    exact ranked_iff_count_bounds.mpr ⟨by omega, by simpa using hg⟩

theorem ordered_getElem?_zero_iff_min {xs : List α} {a : α} :
    (ordered xs)[0]? = some a ↔ a ∈ xs ∧ ∀ x ∈ xs, a ≤ x := by
  rw [← ranked_iff_index, ranked_zero_iff_min]

/-- The inputs need not be sorted; only the cross-list bound is required. -/
theorem ordered_append (xs ys : List α)
    (hxy : ∀ x ∈ xs, ∀ y ∈ ys, x ≤ y) :
    ordered (xs ++ ys) = ordered xs ++ ordered ys := by
  apply ordered_eq_of_pairwise_perm
  · rw [List.pairwise_append]
    refine ⟨ordered_pairwise xs, ordered_pairwise ys, ?_⟩
    intro x hx y hy
    exact hxy x ((ordered_perm xs).mem_iff.mp hx) y ((ordered_perm ys).mem_iff.mp hy)
  · exact (ordered_perm xs).append (ordered_perm ys)

/-- Option indexing extends the source's valid-index recurrence to all indices. -/
theorem ordered_getElem?_append (xs ys : List α)
    (hxy : ∀ x ∈ xs, ∀ y ∈ ys, x ≤ y) (k : Nat) :
    (ordered (xs ++ ys))[k]? =
      if k < xs.length then (ordered xs)[k]? else (ordered ys)[k - xs.length]? := by
  rw [ordered_append xs ys hxy]
  by_cases hk : k < xs.length
  · rw [if_pos hk, List.getElem?_append_left (by simpa only [(ordered_perm xs).length_eq] using hk)]
  · rw [if_neg hk, List.getElem?_append_right (by simpa only [(ordered_perm xs).length_eq] using Nat.le_of_not_gt hk),
      (ordered_perm xs).length_eq]

/-- In a sorted list, every strictly smaller occurrence is before the selected
occurrence. Sublist is stronger than the source's submultiset containment. -/
theorem sorted_filter_lt_sublist_take {ys : List α} {k : Nat} {a : α}
    (hs : ys.Pairwise (· ≤ ·)) (ha : ys[k]? = some a) :
    ys.filter (fun x => decide (x < a)) <+ ys.take k := by
  induction ys generalizing k with
  | nil => simp at ha
  | cons x ys ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst a
      have he : ys.filter (fun y => decide (y < x)) = [] :=
        List.filter_eq_nil_iff.mpr (fun y hy => by
          simpa only [decide_eq_true_eq] using
            not_lt_of_ge ((List.pairwise_cons.mp hs).1 y hy))
      simp [he]
    | succ k =>
      have ht : ys[k]? = some a := ha
      have hh := ih (List.pairwise_cons.mp hs).2 ht
      by_cases hx : x < a
      · simpa [List.filter_cons, hx] using hh.cons_cons x
      · simpa [List.filter_cons, hx] using hh.cons x

theorem sorted_filter_gt_sublist_drop {ys : List α} {k : Nat} {a : α}
    (hs : ys.Pairwise (· ≤ ·)) (ha : ys[k]? = some a) :
    ys.filter (fun x => decide (a < x)) <+ ys.drop (k + 1) := by
  induction ys generalizing k with
  | nil => simp at ha
  | cons x ys ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst a
      simpa using (List.filter_sublist (p := fun y => decide (x < y)) (l := ys))
    | succ k =>
      have ht : ys[k]? = some a := ha
      have hx : x ≤ a := (List.pairwise_cons.mp hs).1 a (List.mem_of_getElem? ht)
      simpa [List.filter_cons, not_lt_of_ge hx] using
        ih (List.pairwise_cons.mp hs).2 ht

/-- The lower occurrence convention is also valid for empty input as none. -/
theorem lowerMedian_value (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) : lowerMedianWith choose xs = (ordered xs)[(xs.length - 1) / 2]? := by
  by_cases hx : xs = []
  · subst xs
    simp [lowerMedianWith, selectWith, ordered]
  · have hn : 0 < xs.length := List.length_pos.mpr hx
    rw [lowerMedianWith, selectWith_value choose hv xs _ (by omega)]
    congr 1
    omega

theorem lowerMedian_count_bounds (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (a : α) (ha : lowerMedianWith choose xs = some a) :
    xs.countP (fun x => decide (x < a)) ≤ (xs.length - 1) / 2 ∧
      xs.countP (fun x => decide (a < x)) ≤ xs.length / 2 := by
  rw [lowerMedian_value choose hv xs] at ha
  have h := (ranked_iff_index.mpr ha).count_bounds
  omega

theorem lowerMedian_mem (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (a : α) (ha : lowerMedianWith choose xs = some a) : a ∈ xs :=
  (lowerMedian_ranked choose hv xs a ha).mem

end Applications.Selection
