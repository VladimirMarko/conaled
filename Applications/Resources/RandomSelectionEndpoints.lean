import Applications.Resources.RandomSelectionEqual
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup

/-! Actual endpoint steps for the universal distinct-input worst path.

The input need not be sorted. At a positive worker rank the chosen occurrence
is a minimum; at rank zero it is a maximum. Distinctness makes its equal bucket
a singleton, so every nonterminal chosen step removes exactly one occurrence.
The child keeps the required order statistic and pays the existing source cost.

These local facts do not by themselves assert a whole-path probability or a
quadratic lower bound. Those require the actual recursive PMF and trace.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomSelection
open Applications.Selection
universe u
variable {α : Type u} [LinearOrder α]

/-- The specified bad-endpoint policy, expressed on an actual current occurrence.
It chooses minima while the worker rank is positive, then maxima at rank zero. -/
def EndpointPivot (k : Nat) (xs : List α) (i : Fin xs.length) : Prop :=
  if k = 0 then ∀ a ∈ xs, a ≤ xs[i.val]'i.isLt
  else ∀ a ∈ xs, xs[i.val]'i.isLt ≤ a

theorem partition_equal_singleton_of_nodup (p : α) (xs : List α)
    (hxs : xs.Nodup) (hp : p ∈ xs) : (partition3 p xs).2.1 = [p] := by
  rw [partition3_eq_filters]
  change xs.filter (fun a => decide (a = p)) = [p]
  simpa only [List.count_eq_one_of_mem hxs hp, List.replicate_one] using
    (List.filter_eq (l := xs) p)

theorem partition_left_eq_nil_of_minimum (p : α) (xs : List α)
    (hmin : ∀ a ∈ xs, p ≤ a) : (partition3 p xs).1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  obtain ⟨hx, hlt⟩ := (partition_left_mem p xs a).mp ha
  exact (not_lt_of_ge (hmin a hx)) hlt

theorem partition_right_eq_nil_of_maximum (p : α) (xs : List α)
    (hmax : ∀ a ∈ xs, a ≤ p) : (partition3 p xs).2.2 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  obtain ⟨hx, hlt⟩ := (partition_right_mem p xs a).mp ha
  exact (not_lt_of_ge (hmax a hx)) hlt

theorem partition_left_nodup (p : α) (xs : List α) (hxs : xs.Nodup) :
    (partition3 p xs).1.Nodup := by
  rw [partition3_eq_filters]
  exact List.Nodup.filter _ hxs

theorem partition_right_nodup (p : α) (xs : List α) (hxs : xs.Nodup) :
    (partition3 p xs).2.2.Nodup := by
  rw [partition3_eq_filters]
  exact List.Nodup.filter _ hxs

/-- The minimum is witnessed by an actual occurrence even in an unsorted list.
No inhabited payload or distinctness premise is needed for existence. -/
theorem exists_minimum_occurrence (xs : List α) (hne : xs ≠ []) :
    ∃ i : Fin xs.length, ∀ a ∈ xs, xs[i.val]'i.isLt ≤ a := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (List.min_mem hne)
  refine ⟨⟨j, hj⟩, ?_⟩
  intro a ha
  change xs[j]'hj ≤ a
  rw [he]
  exact List.min_le_of_mem ha

theorem exists_maximum_occurrence (xs : List α) (hne : xs ≠ []) :
    ∃ i : Fin xs.length, ∀ a ∈ xs, a ≤ xs[i.val]'i.isLt := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (List.max_mem hne)
  refine ⟨⟨j, hj⟩, ?_⟩
  intro a ha
  change a ≤ xs[j]'hj
  rw [he]
  exact List.le_max_of_mem ha

theorem exists_endpointPivot (k : Nat) (xs : List α) (hne : xs ≠ []) :
    ∃ i : Fin xs.length, EndpointPivot k xs i := by
  by_cases hk : k = 0
  · obtain ⟨i, hi⟩ := exists_maximum_occurrence xs hne
    exact ⟨i, by simpa only [EndpointPivot, hk, ↓reduceIte] using hi⟩
  · obtain ⟨i, hi⟩ := exists_minimum_occurrence xs hne
    exact ⟨i, by simpa only [EndpointPivot, hk, ↓reduceIte] using hi⟩

/-- Distinctness makes the endpoint occurrence unique, not merely its value. -/
theorem endpointPivot_unique (k : Nat) (xs : List α) (hxs : xs.Nodup)
    (i j : Fin xs.length) (hi : EndpointPivot k xs i) (hj : EndpointPivot k xs j) :
    i = j := by
  apply List.nodup_iff_injective_getElem.mp hxs
  by_cases hk : k = 0
  · simp only [EndpointPivot, hk, ↓reduceIte] at hi hj
    exact le_antisymm (hj _ (List.getElem_mem i.isLt)) (hi _ (List.getElem_mem j.isLt))
  · simp only [EndpointPivot, hk, ↓reduceIte] at hi hj
    exact le_antisymm (hi _ (List.getElem_mem j.isLt)) (hj _ (List.getElem_mem i.isLt))

theorem minimum_strict_child_length (p : α) (xs : List α) (hxs : xs.Nodup)
    (hp : p ∈ xs) (hmin : ∀ a ∈ xs, p ≤ a) :
    (partition3 p xs).2.2.length + 1 = xs.length := by
  have hl := partition_left_eq_nil_of_minimum p xs hmin
  have he := partition_equal_singleton_of_nodup p xs hxs hp
  have ht := partition_lengths p xs
  simp only [hl, he, List.length_nil, List.length_cons] at ht
  omega

theorem maximum_strict_child_length (p : α) (xs : List α) (hxs : xs.Nodup)
    (hp : p ∈ xs) (hmax : ∀ a ∈ xs, a ≤ p) :
    (partition3 p xs).1.length + 1 = xs.length := by
  have hr := partition_right_eq_nil_of_maximum p xs hmax
  have he := partition_equal_singleton_of_nodup p xs hxs hp
  have ht := partition_lengths p xs
  simp only [hr, he, List.length_nil, List.length_cons] at ht
  omega

/-- A positive rank survives the minimum pivot in the actual right child.
The cost includes the actual indexed lookup and measured reached lengths. -/
theorem stepRun_minimum_positive (k : Nat) (xs : List α) (hxs : xs.Nodup)
    (i : Fin xs.length) (hmin : ∀ a ∈ xs, xs[i.val]'i.isLt ≤ a) (hk : 0 < k) :
    stepRun k xs i =
      (Sum.inl (k - 1, (partition3 (xs[i.val]'i.isLt) xs).2.2),
        2 * xs.length + i.val + 7) := by
  have hl := partition_left_eq_nil_of_minimum (xs[i.val]'i.isLt) xs hmin
  have he := partition_equal_singleton_of_nodup (xs[i.val]'i.isLt) xs hxs
    (List.getElem_mem i.isLt)
  have hk' : ¬ k < 1 := by omega
  rw [stepRun_eq]
  simp only [hl, he, List.length_nil, List.length_cons, Nat.zero_add,
    Nat.add_zero, Nat.sub_zero, Nat.not_lt_zero, hk', ↓reduceIte]

/-- At rank zero, a maximum pivot removes one larger value until the singleton.
This is the actual left branch, so its equal-block length is not charged. -/
theorem stepRun_maximum_zero (xs : List α) (hxs : xs.Nodup)
    (i : Fin xs.length) (hmax : ∀ a ∈ xs, a ≤ xs[i.val]'i.isLt)
    (hn : 1 < xs.length) :
    stepRun 0 xs i =
      (Sum.inl (0, (partition3 (xs[i.val]'i.isLt) xs).1),
        3 * xs.length + i.val + 4) := by
  have hl := maximum_strict_child_length (xs[i.val]'i.isLt) xs hxs
    (List.getElem_mem i.isLt) hmax
  have hp : 0 < (partition3 (xs[i.val]'i.isLt) xs).1.length := by omega
  rw [stepRun_eq]
  simp only [hp, ↓reduceIte]
  apply Prod.ext
  · rfl
  · change 2 * xs.length + i.val + (partition3 (xs[i.val]'i.isLt) xs).1.length + 5 =
      3 * xs.length + i.val + 4
    omega

/-- Every nonsingleton distinct valid state has its specified endpoint child.
The worker rank is its natural predecessor (which remains zero after zero),
the child has exactly one fewer occurrence, and its sorted-index target agrees
with the parent's. No sorted-input or endpoint-target restriction is imposed. -/
theorem exists_endpoint_child (k : Nat) (xs : List α) (hxs : xs.Nodup)
    (hk : k < xs.length) (hn : 1 < xs.length) :
    ∃ (i : Fin xs.length) (ys : List α),
      EndpointPivot k xs i ∧ (stepRun k xs i).1 = Sum.inl (k - 1, ys) ∧
      ys.Nodup ∧ ys.length + 1 = xs.length ∧ k - 1 < ys.length ∧
      (ordered ys)[k - 1]? = (ordered xs)[k]? := by
  have hne : xs ≠ [] := List.length_pos_iff.mp (by omega)
  by_cases hk0 : k = 0
  · subst k
    obtain ⟨i, hi⟩ := exists_maximum_occurrence xs hne
    let ys := (partition3 (xs[i.val]'i.isLt) xs).1
    have hs : (stepRun 0 xs i).1 = Sum.inl (0, ys) :=
      congrArg Prod.fst (stepRun_maximum_zero xs hxs i hi hn)
    have hl : ys.length + 1 = xs.length :=
      maximum_strict_child_length (xs[i.val]'i.isLt) xs hxs (List.getElem_mem i.isLt) hi
    have hv := stepRun_semantics 0 xs i
    rw [hs] at hv
    exact ⟨i, ys, hi, hs, partition_left_nodup _ xs hxs, hl,
      (stepRun_child 0 xs i 0 ys hs).2 hk, hv⟩
  · obtain ⟨i, hi⟩ := exists_minimum_occurrence xs hne
    let ys := (partition3 (xs[i.val]'i.isLt) xs).2.2
    have hs : (stepRun k xs i).1 = Sum.inl (k - 1, ys) :=
      congrArg Prod.fst (stepRun_minimum_positive k xs hxs i hi (Nat.pos_of_ne_zero hk0))
    have hl : ys.length + 1 = xs.length :=
      minimum_strict_child_length (xs[i.val]'i.isLt) xs hxs (List.getElem_mem i.isLt) hi
    have hv := stepRun_semantics k xs i
    rw [hs] at hv
    refine ⟨i, ys, ?_, hs, partition_right_nodup _ xs hxs, hl,
      (stepRun_child k xs i (k - 1) ys hs).2 hk, hv⟩
    simpa only [EndpointPivot, hk0, ↓reduceIte] using hi

end Resources.RandomSelection
