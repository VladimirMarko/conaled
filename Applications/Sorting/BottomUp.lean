import Applications.Sorting.Merge
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Multiset.AddSub

/-! The adjacent-run bottom-up merge sort from FDSA §2.5 and Exercise 2.6.

The ordinary pass keeps the order of adjacent merged runs. The tail pass
conses each completed run onto an arbitrary accumulator and therefore reverses
the order of completed runs. Both use the canonical `List.merge`; the keyed
specializations choose the left occurrence when keys are equal.
These value laws do not identify comparison counts or allocation costs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting
universe u v
variable {α : Type u} {κ : Type v}

/-- Merge adjacent runs, retaining an unpaired final run unchanged. -/
def mergePairsBy (cmp : α → α → Bool) : List (List α) → List (List α)
  | [] => []
  | [xs] => [xs]
  | xs :: ys :: xss => List.merge xs ys cmp :: mergePairsBy cmp xss

@[simp] theorem mergePairsBy_nil (cmp : α → α → Bool) :
    mergePairsBy cmp [] = [] := rfl

@[simp] theorem mergePairsBy_singleton (cmp : α → α → Bool) (xs : List α) :
    mergePairsBy cmp [xs] = [xs] := rfl

theorem mergePairsBy_step (cmp : α → α → Bool) (xs ys : List α)
    (xss : List (List α)) :
    mergePairsBy cmp (xs :: ys :: xss) =
      List.merge xs ys cmp :: mergePairsBy cmp xss := rfl

/-- One pass leaves exactly ceil(number of runs / 2) runs, including empty runs. -/
theorem mergePairsBy_length (cmp : α → α → Bool) (xss : List (List α)) :
    (mergePairsBy cmp xss).length = (xss.length + 1) / 2 := by
  match xss with
  | [] => rfl
  | [xs] => rfl
  | xs :: ys :: rest =>
    rw [mergePairsBy_step, List.length_cons, mergePairsBy_length cmp rest]
    simp only [List.length_cons]
    omega

theorem mergePairsBy_length_lt (cmp : α → α → Bool) (xss : List (List α))
    (h : 1 < xss.length) : (mergePairsBy cmp xss).length < xss.length := by
  rw [mergePairsBy_length]
  omega

/-- The flattened pass is a permutation for every comparator, without order laws. -/
theorem mergePairsBy_flatten_perm (cmp : α → α → Bool) (xss : List (List α)) :
    (mergePairsBy cmp xss).flatten.Perm xss.flatten := by
  match xss with
  | [] => rfl
  | [xs] => rfl
  | xs :: ys :: rest =>
    simpa only [mergePairsBy_step, List.flatten_cons, List.append_assoc] using
      (List.merge_perm_append cmp (xs := xs) (ys := ys)).append
        (mergePairsBy_flatten_perm cmp rest)

theorem mergePairsBy_flatten_length (cmp : α → α → Bool) (xss : List (List α)) :
    (mergePairsBy cmp xss).flatten.length = xss.flatten.length :=
  (mergePairsBy_flatten_perm cmp xss).length_eq

theorem mergePairsBy_sum_lengths (cmp : α → α → Bool) (xss : List (List α)) :
    ((mergePairsBy cmp xss).map List.length).sum = (xss.map List.length).sum := by
  simpa only [List.length_flatten] using mergePairsBy_flatten_length cmp xss

theorem mergePairsBy_multiset (cmp : α → α → Bool) (xss : List (List α)) :
    ((mergePairsBy cmp xss).flatten : Multiset α) = (xss.flatten : Multiset α) :=
  Multiset.coe_eq_coe.mpr (mergePairsBy_flatten_perm cmp xss)

/-- The book's sum of run multisets is the standard multiset of the flattening. -/
theorem multiset_flatten_eq_sum (xss : List (List α)) :
    (xss.flatten : Multiset α) =
      (xss.map (fun xs => (xs : Multiset α))).sum := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    rw [List.flatten_cons, List.map_cons, List.sum_cons, ← ih]
    rfl

/-- Input-local compatibility suffices to preserve sortedness of each run. -/
theorem mergePairsBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (xss : List (List α))
    (hc : ∀ a ∈ xss.flatten, ∀ b ∈ xss.flatten,
      (cmp a b = true → key a ≤ key b) ∧ (cmp a b = false → key b ≤ key a))
    (hs : ∀ xs ∈ xss, KeySorted key xs) :
    ∀ ys ∈ mergePairsBy cmp xss, KeySorted key ys := by
  match xss with
  | [] => simp
  | [xs] => simpa only [mergePairsBy_singleton] using hs
  | xs :: ys :: rest =>
    intro zs hz
    rw [mergePairsBy_step] at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · apply merge_sorted_compatible_on key cmp xs ys
      · intro a ha b hb
        exact hc a (List.mem_flatten_of_mem (by simp) ha)
          b (List.mem_flatten_of_mem (by simp) hb)
      · exact hs xs (by simp)
      · exact hs ys (by simp)
    · apply mergePairsBy_sorted_compatible_on key cmp rest _ _ zs hz
      · intro a ha b hb
        apply hc a _ b _
        · simp only [List.flatten_cons, List.mem_append]
          exact Or.inr (Or.inr ha)
        · simp only [List.flatten_cons, List.mem_append]
          exact Or.inr (Or.inr hb)
      · intro zs hzs
        exact hs zs (by simp [hzs])

/-- Uniform run lengths double only when no unpaired final run is left. -/
theorem mergePairsBy_uniform_length (cmp : α → α → Bool) (xss : List (List α))
    (m : Nat) (he : Even xss.length) (hl : ∀ xs ∈ xss, xs.length = m) :
    ∀ ys ∈ mergePairsBy cmp xss, ys.length = 2 * m := by
  match xss with
  | [] => simp
  | [xs] =>
    rcases he with ⟨k, hk⟩
    simp only [List.length_cons, List.length_nil] at hk
    omega
  | xs :: ys :: rest =>
    have hrest : Even rest.length := by
      rcases he with ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      simp only [List.length_cons] at hk
      omega
    intro zs hz
    rw [mergePairsBy_step] at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · rw [List.length_merge, hl xs (by simp), hl ys (by simp)]
      omega
    · exact mergePairsBy_uniform_length cmp rest m hrest
        (fun zs hzs => hl zs (by simp [hzs])) zs hz

/-- Repeated adjacent passes, terminating by the strictly decreasing run count. -/
def mergeAllBy (cmp : α → α → Bool) (xss : List (List α)) : List α :=
  match xss with
  | [] => []
  | [xs] => xs
  | xs :: ys :: rest => mergeAllBy cmp (mergePairsBy cmp (xs :: ys :: rest))
termination_by xss.length
decreasing_by
  exact mergePairsBy_length_lt cmp _ (by simp)

@[simp] theorem mergeAllBy_nil (cmp : α → α → Bool) : mergeAllBy cmp [] = [] := by
  rw [mergeAllBy]

@[simp] theorem mergeAllBy_singleton (cmp : α → α → Bool) (xs : List α) :
    mergeAllBy cmp [xs] = xs := by
  rw [mergeAllBy]

theorem mergeAllBy_step (cmp : α → α → Bool) (xs ys : List α)
    (xss : List (List α)) :
    mergeAllBy cmp (xs :: ys :: xss) =
      mergeAllBy cmp (mergePairsBy cmp (xs :: ys :: xss)) := by
  rw [mergeAllBy]

theorem mergeAllBy_perm (cmp : α → α → Bool) (xss : List (List α)) :
    (mergeAllBy cmp xss).Perm xss.flatten := by
  match xss with
  | [] => simp
  | [xs] => simp
  | xs :: ys :: rest =>
    rw [mergeAllBy_step]
    exact (mergeAllBy_perm cmp (mergePairsBy cmp (xs :: ys :: rest))).trans
      (mergePairsBy_flatten_perm cmp (xs :: ys :: rest))
termination_by xss.length
decreasing_by
  exact mergePairsBy_length_lt cmp _ (by simp)

theorem mergeAllBy_length (cmp : α → α → Bool) (xss : List (List α)) :
    (mergeAllBy cmp xss).length = xss.flatten.length :=
  (mergeAllBy_perm cmp xss).length_eq

theorem mergeAllBy_multiset (cmp : α → α → Bool) (xss : List (List α)) :
    (mergeAllBy cmp xss : Multiset α) = (xss.flatten : Multiset α) :=
  Multiset.coe_eq_coe.mpr (mergeAllBy_perm cmp xss)

theorem mergeAllBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (xss : List (List α))
    (hc : ∀ a ∈ xss.flatten, ∀ b ∈ xss.flatten,
      (cmp a b = true → key a ≤ key b) ∧ (cmp a b = false → key b ≤ key a))
    (hs : ∀ xs ∈ xss, KeySorted key xs) : KeySorted key (mergeAllBy cmp xss) := by
  match xss with
  | [] => simp [KeySorted]
  | [xs] => simpa only [mergeAllBy_singleton] using hs xs (by simp)
  | xs :: ys :: rest =>
    rw [mergeAllBy_step]
    apply mergeAllBy_sorted_compatible_on key cmp (mergePairsBy cmp (xs :: ys :: rest))
    · intro a ha b hb
      exact hc a ((mergePairsBy_flatten_perm cmp _).mem_iff.mp ha)
        b ((mergePairsBy_flatten_perm cmp _).mem_iff.mp hb)
    · exact mergePairsBy_sorted_compatible_on key cmp _ hc hs
termination_by xss.length
decreasing_by
  exact mergePairsBy_length_lt cmp _ (by simp)

/-- Bottom-up sorting starts with one singleton run per occurrence. -/
def sortBottomUpBy (cmp : α → α → Bool) (xs : List α) : List α :=
  mergeAllBy cmp (xs.map fun x => [x])

@[simp] theorem sortBottomUpBy_nil (cmp : α → α → Bool) : sortBottomUpBy cmp [] = [] := by
  simp only [sortBottomUpBy, List.map_nil, mergeAllBy_nil]

@[simp] theorem sortBottomUpBy_singleton (cmp : α → α → Bool) (x : α) :
    sortBottomUpBy cmp [x] = [x] := by
  simp only [sortBottomUpBy, List.map_singleton, mergeAllBy_singleton]

private theorem singletonRuns_flatten (xs : List α) :
    (xs.map fun x => [x]).flatten = xs := List.flatMap_singleton' xs

theorem sortBottomUpBy_perm (cmp : α → α → Bool) (xs : List α) :
    (sortBottomUpBy cmp xs).Perm xs := by
  simpa only [sortBottomUpBy, singletonRuns_flatten] using
    mergeAllBy_perm cmp (xs.map fun x => [x])

theorem sortBottomUpBy_length (cmp : α → α → Bool) (xs : List α) :
    (sortBottomUpBy cmp xs).length = xs.length := (sortBottomUpBy_perm cmp xs).length_eq

theorem sortBottomUpBy_multiset (cmp : α → α → Bool) (xs : List α) :
    (sortBottomUpBy cmp xs : Multiset α) = (xs : Multiset α) :=
  Multiset.coe_eq_coe.mpr (sortBottomUpBy_perm cmp xs)

theorem sortBottomUpBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (xs : List α)
    (hc : ∀ a ∈ xs, ∀ b ∈ xs,
      (cmp a b = true → key a ≤ key b) ∧ (cmp a b = false → key b ≤ key a)) :
    KeySorted key (sortBottomUpBy cmp xs) := by
  apply mergeAllBy_sorted_compatible_on key cmp
  · simpa only [singletonRuns_flatten] using hc
  · intro ys hy
    rcases List.mem_map.mp hy with ⟨x, _, rfl⟩
    simp [KeySorted]

abbrev sortBottomUpOn [LE κ] [DecidableLE κ] (key : α → κ) (xs : List α) : List α :=
  sortBottomUpBy (fun a b => decide (key a ≤ key b)) xs

theorem sortBottomUpOn_correct [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    (key : α → κ) (xs : List α) :
    KeySorted key (sortBottomUpOn key xs) ∧ (sortBottomUpOn key xs).Perm xs := by
  refine ⟨?_, sortBottomUpBy_perm _ _⟩
  apply sortBottomUpBy_sorted_compatible_on key
  intro a _ b _
  exact ⟨of_decide_eq_true, fun h =>
    (Std.le_total (a := key a) (b := key b)).resolve_left (of_decide_eq_false h)⟩

/-- Exercise 2.6: tail recursion with one cons per completed run and no append. -/
def mergePairsRevBy (cmp : α → α → Bool) (acc : List (List α)) :
    List (List α) → List (List α)
  | [] => acc
  | [xs] => xs :: acc
  | xs :: ys :: xss => mergePairsRevBy cmp (List.merge xs ys cmp :: acc) xss

@[simp] theorem mergePairsRevBy_nil (cmp : α → α → Bool) (acc : List (List α)) :
    mergePairsRevBy cmp acc [] = acc := rfl

@[simp] theorem mergePairsRevBy_singleton (cmp : α → α → Bool)
    (acc : List (List α)) (xs : List α) : mergePairsRevBy cmp acc [xs] = xs :: acc := rfl

theorem mergePairsRevBy_step (cmp : α → α → Bool) (acc : List (List α))
    (xs ys : List α) (xss : List (List α)) :
    mergePairsRevBy cmp acc (xs :: ys :: xss) =
      mergePairsRevBy cmp (List.merge xs ys cmp :: acc) xss := rfl

/-- The exact accumulator invariant; reversal occurs at the run level. -/
theorem mergePairsRevBy_eq_reverse_append (cmp : α → α → Bool)
    (acc xss : List (List α)) :
    mergePairsRevBy cmp acc xss = (mergePairsBy cmp xss).reverse ++ acc := by
  match xss with
  | [] => rfl
  | [xs] => rfl
  | xs :: ys :: rest =>
    rw [mergePairsRevBy_step,
      mergePairsRevBy_eq_reverse_append cmp (List.merge xs ys cmp :: acc) rest,
      mergePairsBy_step, List.reverse_cons, List.append_assoc]
    rfl

theorem mergePairsRevBy_length (cmp : α → α → Bool) (acc xss : List (List α)) :
    (mergePairsRevBy cmp acc xss).length = acc.length + (xss.length + 1) / 2 := by
  rw [mergePairsRevBy_eq_reverse_append, List.length_append, List.length_reverse,
    mergePairsBy_length]
  omega

theorem mergePairsRevBy_empty_length_lt (cmp : α → α → Bool) (xss : List (List α))
    (h : 1 < xss.length) : (mergePairsRevBy cmp [] xss).length < xss.length := by
  rw [mergePairsRevBy_length]
  simp only [List.length_nil, Nat.zero_add]
  omega

theorem mergePairsRevBy_flatten_perm (cmp : α → α → Bool) (acc xss : List (List α)) :
    (mergePairsRevBy cmp acc xss).flatten.Perm (acc.flatten ++ xss.flatten) := by
  rw [mergePairsRevBy_eq_reverse_append, List.flatten_append]
  exact (((List.reverse_perm _).flatten.trans (mergePairsBy_flatten_perm cmp xss)).append
    (List.Perm.refl acc.flatten)).trans List.perm_append_comm

theorem mergePairsRevBy_flatten_length (cmp : α → α → Bool) (acc xss : List (List α)) :
    (mergePairsRevBy cmp acc xss).flatten.length = acc.flatten.length + xss.flatten.length := by
  simpa only [List.length_append] using (mergePairsRevBy_flatten_perm cmp acc xss).length_eq

/-- The arbitrary-accumulator multiset equation printed for the tail pass. -/
theorem mergePairsRevBy_multiset (cmp : α → α → Bool) (acc xss : List (List α)) :
    ((mergePairsRevBy cmp acc xss).flatten : Multiset α) =
      (acc.flatten : Multiset α) + (xss.flatten : Multiset α) := by
  rw [Multiset.coe_add]
  exact Multiset.coe_eq_coe.mpr (mergePairsRevBy_flatten_perm cmp acc xss)

theorem mergePairsRevBy_empty_flatten_perm (cmp : α → α → Bool)
    (xss : List (List α)) : (mergePairsRevBy cmp [] xss).flatten.Perm xss.flatten := by
  simpa only [List.flatten_nil, List.nil_append] using
    mergePairsRevBy_flatten_perm cmp [] xss

/-- Accumulator runs need only be sorted individually; this pass does not merge them. -/
theorem mergePairsRevBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (acc xss : List (List α))
    (hc : ∀ a ∈ xss.flatten, ∀ b ∈ xss.flatten,
      (cmp a b = true → key a ≤ key b) ∧ (cmp a b = false → key b ≤ key a))
    (ha : ∀ xs ∈ acc, KeySorted key xs) (hs : ∀ xs ∈ xss, KeySorted key xs) :
    ∀ ys ∈ mergePairsRevBy cmp acc xss, KeySorted key ys := by
  rw [mergePairsRevBy_eq_reverse_append]
  intro ys hy
  rcases List.mem_append.mp hy with hy | hy
  · exact mergePairsBy_sorted_compatible_on key cmp xss hc hs ys (List.mem_reverse.mp hy)
  · exact ha ys hy

/-- Repeated tail passes still terminate by run count, despite changing run order. -/
def mergeAllRevBy (cmp : α → α → Bool) (xss : List (List α)) : List α :=
  match xss with
  | [] => []
  | [xs] => xs
  | xs :: ys :: rest => mergeAllRevBy cmp (mergePairsRevBy cmp [] (xs :: ys :: rest))
termination_by xss.length
decreasing_by
  exact mergePairsRevBy_empty_length_lt cmp _ (by simp)

@[simp] theorem mergeAllRevBy_nil (cmp : α → α → Bool) : mergeAllRevBy cmp [] = [] := by
  rw [mergeAllRevBy]

@[simp] theorem mergeAllRevBy_singleton (cmp : α → α → Bool) (xs : List α) :
    mergeAllRevBy cmp [xs] = xs := by
  rw [mergeAllRevBy]

theorem mergeAllRevBy_step (cmp : α → α → Bool) (xs ys : List α)
    (xss : List (List α)) :
    mergeAllRevBy cmp (xs :: ys :: xss) =
      mergeAllRevBy cmp (mergePairsRevBy cmp [] (xs :: ys :: xss)) := by
  rw [mergeAllRevBy]

theorem mergeAllRevBy_perm (cmp : α → α → Bool) (xss : List (List α)) :
    (mergeAllRevBy cmp xss).Perm xss.flatten := by
  match xss with
  | [] => simp
  | [xs] => simp
  | xs :: ys :: rest =>
    rw [mergeAllRevBy_step]
    exact (mergeAllRevBy_perm cmp (mergePairsRevBy cmp [] (xs :: ys :: rest))).trans
      (mergePairsRevBy_empty_flatten_perm cmp (xs :: ys :: rest))
termination_by xss.length
decreasing_by
  exact mergePairsRevBy_empty_length_lt cmp _ (by simp)

theorem mergeAllRevBy_length (cmp : α → α → Bool) (xss : List (List α)) :
    (mergeAllRevBy cmp xss).length = xss.flatten.length :=
  (mergeAllRevBy_perm cmp xss).length_eq

theorem mergeAllRevBy_multiset (cmp : α → α → Bool) (xss : List (List α)) :
    (mergeAllRevBy cmp xss : Multiset α) = (xss.flatten : Multiset α) :=
  Multiset.coe_eq_coe.mpr (mergeAllRevBy_perm cmp xss)

theorem mergeAllRevBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (xss : List (List α))
    (hc : ∀ a ∈ xss.flatten, ∀ b ∈ xss.flatten,
      (cmp a b = true → key a ≤ key b) ∧ (cmp a b = false → key b ≤ key a))
    (hs : ∀ xs ∈ xss, KeySorted key xs) : KeySorted key (mergeAllRevBy cmp xss) := by
  match xss with
  | [] => simp [KeySorted]
  | [xs] => simpa only [mergeAllRevBy_singleton] using hs xs (by simp)
  | xs :: ys :: rest =>
    rw [mergeAllRevBy_step]
    apply mergeAllRevBy_sorted_compatible_on key cmp
      (mergePairsRevBy cmp [] (xs :: ys :: rest))
    · intro a ha b hb
      exact hc a ((mergePairsRevBy_empty_flatten_perm cmp _).mem_iff.mp ha)
        b ((mergePairsRevBy_empty_flatten_perm cmp _).mem_iff.mp hb)
    · exact mergePairsRevBy_sorted_compatible_on key cmp [] _ hc (by simp) hs
termination_by xss.length
decreasing_by
  exact mergePairsRevBy_empty_length_lt cmp _ (by simp)

/-- The tail-pass variant sorts correctly but need not preserve equal-key payload order. -/
def sortBottomUpRevBy (cmp : α → α → Bool) (xs : List α) : List α :=
  mergeAllRevBy cmp (xs.map fun x => [x])

@[simp] theorem sortBottomUpRevBy_nil (cmp : α → α → Bool) :
    sortBottomUpRevBy cmp [] = [] := by
  simp only [sortBottomUpRevBy, List.map_nil, mergeAllRevBy_nil]

@[simp] theorem sortBottomUpRevBy_singleton (cmp : α → α → Bool) (x : α) :
    sortBottomUpRevBy cmp [x] = [x] := by
  simp only [sortBottomUpRevBy, List.map_singleton, mergeAllRevBy_singleton]

theorem sortBottomUpRevBy_perm (cmp : α → α → Bool) (xs : List α) :
    (sortBottomUpRevBy cmp xs).Perm xs := by
  simpa only [sortBottomUpRevBy, singletonRuns_flatten] using
    mergeAllRevBy_perm cmp (xs.map fun x => [x])

theorem sortBottomUpRevBy_length (cmp : α → α → Bool) (xs : List α) :
    (sortBottomUpRevBy cmp xs).length = xs.length := (sortBottomUpRevBy_perm cmp xs).length_eq

theorem sortBottomUpRevBy_multiset (cmp : α → α → Bool) (xs : List α) :
    (sortBottomUpRevBy cmp xs : Multiset α) = (xs : Multiset α) :=
  Multiset.coe_eq_coe.mpr (sortBottomUpRevBy_perm cmp xs)

theorem sortBottomUpRevBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (xs : List α)
    (hc : ∀ a ∈ xs, ∀ b ∈ xs,
      (cmp a b = true → key a ≤ key b) ∧ (cmp a b = false → key b ≤ key a)) :
    KeySorted key (sortBottomUpRevBy cmp xs) := by
  apply mergeAllRevBy_sorted_compatible_on key cmp
  · simpa only [singletonRuns_flatten] using hc
  · intro ys hy
    rcases List.mem_map.mp hy with ⟨x, _, rfl⟩
    simp [KeySorted]

abbrev sortBottomUpRevOn [LE κ] [DecidableLE κ] (key : α → κ) (xs : List α) : List α :=
  sortBottomUpRevBy (fun a b => decide (key a ≤ key b)) xs

theorem sortBottomUpRevOn_correct [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    (key : α → κ) (xs : List α) :
    KeySorted key (sortBottomUpRevOn key xs) ∧ (sortBottomUpRevOn key xs).Perm xs := by
  refine ⟨?_, sortBottomUpRevBy_perm _ _⟩
  apply sortBottomUpRevBy_sorted_compatible_on key
  intro a _ b _
  exact ⟨of_decide_eq_true, fun h =>
    (Std.le_total (a := key a) (b := key b)).resolve_left (of_decide_eq_false h)⟩

end Applications.Sorting
