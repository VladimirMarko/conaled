import Applications.Selection.MedianOfMedians
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
Source-error witnesses and connected uses of the mathematical pivot bounds.
All computations retain duplicate occurrences and the short final chunk.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MedianOfMedians
open Applications.Selection Applications.Sequences.Chunks

/-- The payload adapter uses the lower occurrence of an even-sized list. -/
theorem lower_even_value : lowerMedianValue ([2, 7] : List Nat) (by decide) = 2 :=
  (lowerMedianValue_ranked _ _).unique (ranked_iff_count_bounds.mpr (by decide))

theorem lower_even_adapter : lowerMedianWith lastPivot ([2, 7] : List Nat) = some 2 := by
  rw [lowerMedianWith_eq_some_value _ last_pivot_valid _ (by decide), lower_even_value]

/-- The p.37 strict-half assertion fails for the greater-than orientation:
two chunks have medians 2 and 7, and exactly one exceeds their lower median. -/
theorem two_full_chunk_medians : chunkMedians 5 (List.range 10) = [2, 7] := by
  decide

theorem two_full_chunk_pivot : medianOfMedians 5 (List.range 10) = some 2 := by
  apply (medianOfMedians_some_iff_ranked 5 _ 2).mpr
  rw [two_full_chunk_medians]
  exact ranked_iff_count_bounds.mpr (by decide)

theorem two_full_chunk_pivot_mem : 2 ∈ List.range 10 :=
  medianOfMedians_mem 5 _ _ two_full_chunk_pivot

theorem strict_half_is_false :
    (chunkMedians 5 (List.range 10)).countP (fun x => decide (2 < x)) = 1 ∧
      (chunkMedians 5 (List.range 10)).length / 2 = 1 ∧
      ¬(chunkMedians 5 (List.range 10)).countP (fun x => decide (2 < x)) <
        (chunkMedians 5 (List.range 10)).length / 2 := by
  rw [two_full_chunk_medians]
  decide

theorem corrected_non_strict_half :
    (chunkMedians 5 (List.range 10)).countP (fun x => decide (2 < x)) ≤ 1 := by
  simpa using (medianOfMedians_median_counts 5 _ 2 two_full_chunk_pivot).2

theorem greater_median_group_is_one :
    (chunkMedianGroups 5 (List.range 10) (fun x => decide (2 < x))).1.length = 1 := by
  rw [chunkMedianGroups_related_length, two_full_chunk_medians]
  decide

theorem complementary_group_is_one :
    (chunkMedianGroups 5 (List.range 10) (fun x => decide (2 < x))).2.length = 1 := by
  have h := chunkMedianGroups_lengths 5 (List.range 10) (fun x => decide (2 < x))
  rw [greater_median_group_is_one] at h
  norm_num [Nat.ceilDiv_eq_add_pred_div] at h
  omega

/-- The final chunk [5,6] is retained, and its lower median is 5. -/
theorem short_final_chunk_medians : chunkMedians 5 (List.range 7) = [2, 5] := by
  decide

theorem short_final_chunk_pivot : medianOfMedians 5 (List.range 7) = some 2 := by
  apply (medianOfMedians_some_iff_ranked 5 _ 2).mpr
  rw [short_final_chunk_medians]
  exact ranked_iff_count_bounds.mpr (by decide)

theorem short_final_chunk_balance :
    (List.range 7).countP (fun x => decide (x < 2)) ≤ 7 ∧
      (List.range 7).countP (fun x => decide (2 < x)) ≤ 7 := by
  simpa using medianOfMedians_count_bounds 5 _ 2 (by decide) short_final_chunk_pivot

/-- Equal medians are kept as two occurrences, including the singleton chunk. -/
theorem duplicate_chunk_medians : chunkMedians 5 (List.replicate 6 4) = [4, 4] := by
  decide

theorem duplicate_pivot : medianOfMedians 5 (List.replicate 6 4) = some 4 := by
  apply (medianOfMedians_some_iff_ranked 5 _ 4).mpr
  rw [duplicate_chunk_medians]
  exact ranked_iff_count_bounds.mpr (by decide)

theorem duplicate_strict_sides (p : Nat)
    (hp : medianOfMedians 5 (List.replicate 6 4) = some p) :
    (List.replicate 6 4).countP (fun x => decide (x < p)) = 0 ∧
      (List.replicate 6 4).countP (fun x => decide (p < x)) = 0 := by
  have he : p = 4 := Option.some.inj (hp.symm.trans duplicate_pivot)
  subst p
  decide

theorem duplicate_groups :
    chunkMedianGroups 5 (List.replicate 6 4) (fun x => decide (4 < x)) =
      ([], [[4, 4, 4, 4, 4], [4]]) := by
  decide

theorem duplicate_groups_multiset :
    ([[4, 4, 4, 4, 4], [4]] : Multiset (List Nat)) =
      (chop 5 (List.replicate 6 4) : Multiset (List Nat)) := by
  have h := chunkMedianGroups_multiset 5 (List.replicate 6 4) (fun x => decide (4 < x))
  rw [duplicate_groups] at h
  simpa using h

/-- The two contribution lemmas are uniform over chunks, not just full groups. -/
theorem five_chunk_lower_contribution (xs ys : List Nat) (hy : ys ∈ chop 5 xs) (p : Nat)
    (hp : p ≤ lowerMedianValue ys (chop_mem_ne_nil 5 xs ys hy)) :
    ys.countP (fun x => decide (x < p)) ≤ 2 :=
  chunk_count_lt_of_median_ge 5 xs ys hy p hp

theorem five_chunk_upper_contribution (xs ys : List Nat) (hy : ys ∈ chop 5 xs) (p : Nat)
    (hp : lowerMedianValue ys (chop_mem_ne_nil 5 xs ys hy) ≤ p) :
    ys.countP (fun x => decide (p < x)) ≤ 2 :=
  chunk_count_gt_of_median_le 5 xs ys hy p hp

theorem five_chunk_total_contribution (xs ys : List Nat) (hy : ys ∈ chop 5 xs)
    (r : Nat → Bool) : ys.countP r ≤ 5 :=
  List.countP_le_length.trans (length_mem_chop 5 xs ys hy)

/-- Size one specializes the general bound to the median's half bound. -/
theorem singleton_group_balance (xs : List Nat) (p : Nat)
    (hp : medianOfMedians 1 xs = some p) :
    xs.countP (fun x => decide (x < p)) ≤ xs.length / 2 ∧
      xs.countP (fun x => decide (p < x)) ≤ xs.length / 2 := by
  simpa using medianOfMedians_count_bounds 1 xs p (by decide) hp

theorem source_real_ceiling (n : Nat) :
    (7 * n + 30) ⌈/⌉ 10 = ⌈(7 : ℝ) * n / 10 + 3⌉₊ :=
  size_five_ceiling ℝ n

theorem source_real_balance (xs : List Nat) (p : Nat)
    (hp : medianOfMedians 5 xs = some p) :
    xs.countP (fun x => decide (x < p)) ≤ ⌈(7 : ℝ) * xs.length / 10 + 3⌉₊ ∧
      xs.countP (fun x => decide (p < x)) ≤ ⌈(7 : ℝ) * xs.length / 10 + 3⌉₊ :=
  medianOfMedians_five_ceil_bounds ℝ xs p hp

theorem empty_pivot : medianOfMedians 5 ([] : List Nat) = none :=
  (medianOfMedians_none 5 []).mpr (Or.inr rfl)

theorem zero_size_pivot (xs : List Nat) : medianOfMedians 0 xs = none :=
  (medianOfMedians_none 0 xs).mpr (Or.inl rfl)

/-- Empty-input counts need no selected value or nonempty-input hypothesis. -/
theorem empty_strict_counts (p : Nat) :
    ([] : List Nat).countP (fun x => decide (x < p)) = 0 ∧
      ([] : List Nat).countP (fun x => decide (p < x)) = 0 := ⟨rfl, rfl⟩

theorem mathematical_policy_is_valid :
    PivotValid (medianOfMedians 5 : List Nat → Option Nat) :=
  medianOfMedians_pivot_valid 5 (by decide)

end Examples.MedianOfMedians
