import Applications.Resources.MedianReduction

/-!
Connected instances of the rank-to-median reduction and its actual source cost.
The cases cover both padding orientations, tied extrema, the central rank,
empty/singleton boundaries and failure of the valid-rank claims outside their
domain. No global sentinel is used, as the integer-extrema case also illustrates.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MedianReduction
open Applications.Selection Applications.Selection.FixedRank
open Applications.Selection.MedianReduction Resources.MedianReduction

theorem extrema_mixed : extrema (4 : Nat) [1, 7, 1] = (1, 7) :=
  extrema_eq_of_bounds 4 [1, 7, 1] 1 7 (by decide) (by decide) (by decide) (by decide)

theorem extrema_tied : extrema (3 : Nat) [3, 3] = (3, 3) :=
  extrema_eq_of_bounds 3 [3, 3] 3 3 (by decide) (by decide) (by decide) (by decide)

theorem extrema_integer : extrema (-2 : Int) [7, -2, 0] = (-2, 7) :=
  extrema_eq_of_bounds (-2) [7, -2, 0] (-2) 7
    (by decide) (by decide) (by decide) (by decide)

/-- Two length-three tails and the extrema wrapper cost nine calls. -/
theorem extrema_execution : extremaRun (4 : Nat) [1, 7, 1] = ((1, 7), 9) := by
  apply Prod.ext
  · rw [extremaRun_value]
    exact extrema_mixed
  · exact extremaRun_cost 4 [1, 7, 1]

theorem replication_execution : replicateRun (5 : Int) 3 = ([5, 5, 5], 4) :=
  replicateRun_exact 5 3

/-- All seven values are equal, yet the original second occurrence shifts
to index three. Its strict lower count stays zero. -/
theorem tied_padding_rank : RankedAt (padExtrema 2 3 (1 : Nat) 1 [1, 1]) 3 1 :=
  ranked_padExtrema 2 3 1 1 [1, 1] 1 1
    (ranked_iff_count_bounds.mpr (by decide)) le_rfl le_rfl

theorem first_padding :
    reduceToMedian 0 ([4, 1, 7, 1] : List Nat) = [1, 1, 1, 4, 1, 7, 1] := by
  simp only [reduceToMedian, extrema_mixed]
  rfl

theorem last_padding :
    reduceToMedian 3 ([4, 1, 7, 1] : List Nat) = [4, 1, 7, 1, 7, 7, 7] := by
  simp only [reduceToMedian, extrema_mixed]
  rfl

theorem lower_middle_padding :
    reduceToMedian 1 ([4, 1, 7, 1] : List Nat) = [1, 4, 1, 7, 1] := by
  simp only [reduceToMedian, extrema_mixed]
  rfl

theorem upper_middle_padding :
    reduceToMedian 2 ([4, 1, 7, 1] : List Nat) = [4, 1, 7, 1, 7] := by
  simp only [reduceToMedian, extrema_mixed]
  rfl

theorem already_central : reduceToMedian 1 ([4, 1, 1] : List Nat) = [4, 1, 1] := rfl

theorem singleton_unchanged {α : Type} [LinearOrder α] (x : α) :
    reduceToMedian 0 [x] = [x] := rfl

theorem empty_median_failure (k : Nat) :
    lowerMedianWith List.head? (reduceToMedian k ([] : List Nat)) = none := by
  rw [reduceToMedian_nil]
  exact (lowerMedianWith_none _ head_pivot_valid _).mpr rfl

/-- The lower median after padding agrees even with a different valid policy. -/
theorem lower_middle_median :
    lowerMedianWith lastPivot (reduceToMedian 1 ([4, 1, 7, 1] : List Nat)) = some 1 := by
  rw [reduceToMedian_value _ last_pivot_valid 1 _ (by decide)]
  exact (selectFixed_some_iff_count_bounds _ _ _).mpr (by decide)

theorem upper_middle_payload :
    lowerMedianValue (reduceToMedian 2 ([4, 1, 7, 1] : List Nat))
      (reduceToMedian_nonempty 2 _ (by decide)) = 4 := by
  have h := reduceToMedian_payload_value 2 ([4, 1, 7, 1] : List Nat)
    (by decide) (by decide)
  have hv : selectFixed 2 ([4, 1, 7, 1] : List Nat) = some 4 :=
    (selectFixed_some_iff_count_bounds _ _ _).mpr (by decide)
  rw [hv] at h
  exact Option.some.inj h

/-- Valid inputs give a nonempty odd output, bounded size and exact central
index simultaneously. The premises remain satisfiable with duplicates. -/
theorem reduction_shape {α : Type} [LinearOrder α] (k : Nat) (xs : List α)
    (hk : k < xs.length) :
    reduceToMedian k xs ≠ [] ∧ (reduceToMedian k xs).length % 2 = 1 ∧
      (reduceToMedian k xs).length ≤ 2 * xs.length - 1 ∧
      ((reduceToMedian k xs).length - 1) / 2 = k + (xs.length - 1 - 2 * k) := by
  have hx : xs ≠ [] := List.ne_nil_of_length_pos (by omega)
  exact ⟨reduceToMedian_nonempty k xs hx, reduceToMedian_odd k xs hx,
    reduceToMedian_length_le k xs hk, reduceToMedian_center k xs hx⟩

/-- Both pad constructions and both appends are visible in this exact count. -/
theorem padding_execution :
    padExtremaRun 3 0 (1 : Nat) 7 [4, 1, 7, 1] = ([1, 1, 1, 4, 1, 7, 1], 15) :=
  padExtremaRun_exact 3 0 1 7 [4, 1, 7, 1]

theorem first_execution :
    reduceToMedianRun 0 ([4, 1, 7, 1] : List Nat) = ([1, 1, 1, 4, 1, 7, 1], 30) := by
  apply Prod.ext
  · rw [reduceToMedianRun_value]
    exact first_padding
  · exact reduceToMedianRun_cost 0 [4, 1, 7, 1] (by decide)

theorem last_execution :
    reduceToMedianRun 3 ([4, 1, 7, 1] : List Nat) = ([4, 1, 7, 1, 7, 7, 7], 27) := by
  apply Prod.ext
  · rw [reduceToMedianRun_value]
    exact last_padding
  · exact reduceToMedianRun_cost 3 [4, 1, 7, 1] (by decide)

/-- No padding is needed at this rank, but extrema, length and the zero-sized
padding/append calls still cost twenty source entries. -/
theorem central_execution :
    reduceToMedianRun 1 ([4, 1, 1] : List Nat) = ([4, 1, 1], 20) := by
  apply Prod.ext
  · rw [reduceToMedianRun_value]
    exact already_central
  · exact reduceToMedianRun_cost 1 [4, 1, 1] (by decide)

theorem singleton_execution {α : Type} [LinearOrder α] (x : α) :
    reduceToMedianRun 0 [x] = ([x], 12) := by
  apply Prod.ext
  · rw [reduceToMedianRun_value]
    exact singleton_unchanged x
  · exact reduceToMedianRun_cost 0 [x] (by simp)

theorem empty_execution (k : Nat) : reduceToMedianRun k ([] : List Nat) = ([], 1) :=
  reduceToMedianRun_nil k

/-- The rank-zero family attains the displayed affine bound for every
nonempty input, independently of its values or repetitions. -/
theorem first_rank_attains_bound {α : Type} [LinearOrder α] (xs : List α)
    (hx : xs ≠ []) : (reduceToMedianRun 0 xs).2 = 6 * xs.length + 6 := by
  rw [reduceToMedianRun_cost 0 xs hx]
  have hn : 0 < xs.length := List.length_pos_iff.mpr hx
  omega

theorem measured_reduction_contract {α : Type} [LinearOrder α]
    (choose : List α → Option α) (hv : PivotValid choose) (k : Nat) (xs : List α)
    (hk : k < xs.length) :
    (reduceToMedianRun k xs).1 ≠ [] ∧
      lowerMedianWith choose (reduceToMedianRun k xs).1 = selectWith choose (k + 1) xs ∧
      (reduceToMedianRun k xs).2 ≤ 6 * xs.length + 6 := by
  have hx : xs ≠ [] := List.ne_nil_of_length_pos (by omega)
  have h := reduceToMedian_spec choose hv k xs hx hk
  rw [reduceToMedianRun_value]
  exact ⟨h.1, h.2, reduceToMedianRun_cost_le k xs hk⟩

/-- Outside the valid-rank domain, this total preparation still constructs a
nonempty list, but it cannot turn a failed selection into a successful one. -/
theorem invalid_rank_values :
    lowerMedianWith List.head? (reduceToMedian 1 ([7] : List Nat)) = some 7 ∧
      selectFixed 1 ([7] : List Nat) = none := by
  constructor
  · rw [show reduceToMedian 1 ([7] : List Nat) = [7, 7, 7] from rfl,
      lowerMedianWith_value _ head_pivot_valid]
    exact ranked_iff_index.mp (ranked_iff_count_bounds.mpr (by decide))
  · exact (selectFixed_none_iff 1 [7]).mpr (by decide)

theorem invalid_rank_cost_exceeds_valid_bound :
    6 * ([7] : List Nat).length + 6 < (reduceToMedianRun 1 ([7] : List Nat)).2 := by
  rw [reduceToMedianRun_cost 1 [7] (by decide)]
  decide

theorem uniform_reduction_constants :
    ∃ C1 C2 : Nat, ∀ (k : Nat) (xs : List Nat), k < xs.length →
      (reduceToMedianRun k xs).2 ≤ C1 * xs.length + C2 :=
  reduceToMedianRun_uniform_bound

end Examples.MedianReduction
