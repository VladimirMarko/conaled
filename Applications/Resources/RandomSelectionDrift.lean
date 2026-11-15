import Applications.Resources.RandomSelectionMean
import Applications.Resources.RandomQuickSortRank
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.Linarith

/-! Linear expectations of the actual occurrence-pivot selection run.

The existing stable occurrence permutation refines equal values by their input
positions. Strict lower and upper partitions fit inside the corresponding rank
sides even with duplicates. Their maximum is only a pointwise upper bound for
the child selected by `stepRun`; it is not a substitute probability process.

Finite uniform averaging gives conditional size drift at most three quarters.
Well-founded induction on the actual child then proves scan expectation at most
four times the input length. The existing same-run source bridge supplies the
source-call expectation bound. These worker-rank statements also cover the
invalid extension; they do not change the one-based `select` boundary.

The exact tail and worst-case witnesses need further trace arguments. No
independence of successive sizes or conclusion of those arguments is assumed.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomSelection
open Applications.Selection
open scoped BigOperators ENNReal
universe u
variable {α : Type u}

/-- Sum of the larger refined-rank side over every occurrence rank. -/
def rankSideSum (n : Nat) : Nat :=
  ∑ r ∈ Finset.range n, max r (n - 1 - r)

@[simp] theorem rankSideSum_zero : rankSideSum 0 = 0 := by
  simp [rankSideSum]

@[simp] theorem rankSideSum_one : rankSideSum 1 = 0 := by
  simp [rankSideSum]

/-- Remove both endpoints; each of the remaining rank sides grows by one. -/
theorem rankSideSum_add_two (n : Nat) :
    rankSideSum (n + 2) = rankSideSum n + 3 * n + 2 := by
  have hmiddle :
      (∑ r ∈ Finset.range n, max (r + 1) (n + 2 - 1 - (r + 1))) =
        rankSideSum n + n := by
    calc
      _ = ∑ r ∈ Finset.range n, (max r (n - 1 - r) + 1) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrn : r < n := Finset.mem_range.mp hr
        omega
      _ = _ := by simp [rankSideSum, Finset.sum_add_distrib]
  rw [rankSideSum, Finset.sum_range_succ, Finset.sum_range_succ', hmiddle]
  omega

/-- Natural arithmetic form of the three-quarter average bound, including
the empty sum and singleton. No rounding or parity case is discarded. -/
theorem rankSideSum_bound (n : Nat) : 4 * rankSideSum n ≤ 3 * n * n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih _ihnext =>
      rw [rankSideSum_add_two]
      nlinarith

private theorem four_mul_three_quarters : (4 : ℝ≥0∞) * (3 / 4) = 3 := by
  rw [div_eq_mul_inv, mul_left_comm,
    ENNReal.mul_inv_cancel (by simp) ENNReal.ofNat_ne_top, mul_one]

/-- Averaging the larger refined-rank side over a positive size. -/
theorem rankSideSum_mean_le (n : Nat) (hn : 0 < n) :
    (n : ℝ≥0∞)⁻¹ * (rankSideSum n : ℝ≥0∞) ≤ (3 / 4 : ℝ≥0∞) * n := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  apply (ENNReal.inv_mul_le_iff hn0 (ENNReal.natCast_ne_top n)).2
  apply (ENNReal.mul_le_mul_iff_right (a := (4 : ℝ≥0∞)) (by simp)
    ENNReal.ofNat_ne_top).mp
  calc
    4 * (rankSideSum n : ℝ≥0∞) ≤ 3 * (n : ℝ≥0∞) * n := by
      exact_mod_cast rankSideSum_bound n
    _ = (4 * (3 / 4)) * (n : ℝ≥0∞) * n := by rw [four_mul_three_quarters]
    _ = 4 * ((n : ℝ≥0∞) * ((3 / 4) * n)) := by ac_rfl

noncomputable section
section Ordered
variable [LinearOrder α]

/-- Strict value order implies strict refined occurrence-rank order without
requiring distinct input values. -/
theorem occurrenceRank_lt_of_lt (xs : List α) (i j : Fin xs.length)
    (hij : xs[i.val] < xs[j.val]) :
    RandomQuickSort.occurrenceRank id xs i < RandomQuickSort.occurrenceRank id xs j := by
  let f : Fin xs.length → α := fun r => xs[r.val]'r.isLt
  change (Tuple.sort f).symm i < (Tuple.sort f).symm j
  apply lt_of_not_ge
  intro hji
  have hs := Tuple.monotone_sort f hji
  have hvalues : xs[j.val] ≤ xs[i.val] := by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, f] using hs
  exact (not_le_of_gt hij) hvalues

/-- Equal values retain their original occurrence order in the rank coupling. -/
theorem occurrenceRank_tie (xs : List α) (i j : Fin xs.length)
    (hij : i < j) (hvalue : xs[i.val] = xs[j.val]) :
    RandomQuickSort.occurrenceRank id xs i < RandomQuickSort.occurrenceRank id xs j := by
  let f : Fin xs.length → α := fun r => xs[r.val]'r.isLt
  have hstable := (Tuple.eq_sort_iff (f := f) (σ := Tuple.sort f)).mp rfl
  change (Tuple.sort f).symm i < (Tuple.sort f).symm j
  apply lt_of_not_ge
  intro hji
  have hne : (Tuple.sort f).symm j ≠ (Tuple.sort f).symm i := by
    intro he
    exact (ne_of_lt hij) ((Tuple.sort f).symm.injective he).symm
  have hequal :
      f (Tuple.sort f ((Tuple.sort f).symm j)) =
        f (Tuple.sort f ((Tuple.sort f).symm i)) := by
    simpa only [Equiv.apply_symm_apply, f] using hvalue.symm
  have hs := hstable.2 _ _ (lt_of_le_of_ne hji hne) hequal
  have hreverse : j < i := by
    simpa only [Equiv.apply_symm_apply] using hs
  exact (not_lt_of_ge hij.le) hreverse

/-- The actual uniform occurrence draw has uniform refined rank, including
all duplicate tie positions. This is a permutation pushforward, not resampling
from the set of distinct values. -/
theorem occurrenceRank_uniform (head : α) (tail : List α) :
    PMF.map (RandomQuickSort.occurrenceRank id (head :: tail))
      (RandomQuickSort.uniformIndex tail.length) =
        RandomQuickSort.uniformIndex tail.length := by
  let ρ : Equiv.Perm (Fin (tail.length + 1)) :=
    RandomQuickSort.occurrenceRank id (head :: tail)
  apply PMF.ext
  intro r
  change PMF.map ρ (RandomQuickSort.uniformIndex tail.length) r = _
  rw [PMF.map_apply]
  have heq (j : Fin (tail.length + 1)) : r = ρ j ↔ j = ρ.symm r := by
    constructor
    · intro h
      apply ρ.injective
      simpa only [Equiv.apply_symm_apply] using h.symm
    · intro h
      rw [h, Equiv.apply_symm_apply]
  simp only [heq, tsum_ite_eq, RandomQuickSort.uniformIndex_apply]

omit [LinearOrder α] in
private theorem filter_length_eq_card_indices (xs : List α) (p : α → Bool) :
    (xs.filter p).length =
      (Finset.univ.filter (fun i : Fin xs.length => p (xs[i.val]'i.isLt))).card := by
  let f : Fin xs.length → α := fun i => xs[i.val]'i.isLt
  have hxs : (List.finRange xs.length).map f = xs := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem
  calc
    (xs.filter p).length = (((List.finRange xs.length).map f).filter p).length :=
      congrArg (fun ys => (ys.filter p).length) hxs.symm
    _ = ((List.finRange xs.length).filter (p ∘ f)).length := by
      rw [List.filter_map, List.length_map]
    _ = (((List.finRange xs.length).filter (p ∘ f)).toFinset).card :=
      (List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)).symm
    _ = _ := by
      rw [List.toFinset_filter, List.toFinset_finRange]
      rfl

/-- Every strict lower occurrence precedes the pivot's refined rank, and
every strict upper occurrence follows it. Extra equal occurrences only shrink
the strict partitions relative to these rank sides. -/
theorem strict_side_rank_bounds (xs : List α) (i : Fin xs.length) :
    (partition3 (xs[i.val]'i.isLt) xs).1.length ≤
        (RandomQuickSort.occurrenceRank id xs i).val ∧
      (partition3 (xs[i.val]'i.isLt) xs).2.2.length ≤
        xs.length - 1 - (RandomQuickSort.occurrenceRank id xs i).val := by
  let ρ := RandomQuickSort.occurrenceRank id xs
  constructor
  · rw [partition3_eq_filters, filter_length_eq_card_indices]
    let s := Finset.univ.filter (fun j : Fin xs.length => xs[j.val] < xs[i.val])
    have himage : s.image ρ ⊆ Finset.Iio (ρ i) := by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_Iio.mpr
        (occurrenceRank_lt_of_lt xs j i (Finset.mem_filter.mp hj).2)
    have hc := Finset.card_le_card himage
    rw [Finset.card_image_of_injective _ ρ.injective, Fin.card_Iio] at hc
    simpa only [s, decide_eq_true_eq] using hc
  · rw [partition3_eq_filters, filter_length_eq_card_indices]
    let s := Finset.univ.filter (fun j : Fin xs.length => xs[i.val] < xs[j.val])
    have himage : s.image ρ ⊆ Finset.Ioi (ρ i) := by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_Ioi.mpr
        (occurrenceRank_lt_of_lt xs i j (Finset.mem_filter.mp hj).2)
    have hc := Finset.card_le_card himage
    rw [Finset.card_image_of_injective _ ρ.injective, Fin.card_Ioi] at hc
    simpa only [s, decide_eq_true_eq] using hc

/-- Size of the actual selected child, with zero continuation on a direct
equal-block return. It is an observation of `stepRun`, not a size recurrence. -/
def nextSize (k : Nat) (xs : List α) (i : Fin xs.length) : Nat :=
  match (stepRun k xs i).1 with
  | Sum.inl (_, ys) => ys.length
  | Sum.inr _ => 0

/-- The larger rank side is a pathwise majorant for the chosen child. -/
theorem nextSize_le_rankSide (k : Nat) (xs : List α) (i : Fin xs.length) :
    nextSize k xs i ≤
      max (RandomQuickSort.occurrenceRank id xs i).val
        (xs.length - 1 - (RandomQuickSort.occurrenceRank id xs i).val) := by
  have hb := strict_side_rank_bounds xs i
  rw [nextSize, stepRun_eq]
  split_ifs
  · exact hb.1.trans (le_max_left _ _)
  · exact Nat.zero_le _
  · exact hb.2.trans (le_max_right _ _)

/-- Reindex the actual occurrence sum by its rank permutation. -/
theorem nextSize_sum_le (k : Nat) (xs : List α) :
    (∑ i : Fin xs.length, nextSize k xs i) ≤ rankSideSum xs.length := by
  let ρ := RandomQuickSort.occurrenceRank id xs
  calc
    _ ≤ ∑ i : Fin xs.length, max (ρ i).val (xs.length - 1 - (ρ i).val) := by
      apply Finset.sum_le_sum
      intro i _
      exact nextSize_le_rankSide k xs i
    _ = ∑ r : Fin xs.length, max r.val (xs.length - 1 - r.val) :=
      Equiv.sum_comp ρ (fun r => max r.val (xs.length - 1 - r.val))
    _ = rankSideSum xs.length :=
      Fin.sum_univ_eq_sum_range (fun r => max r (xs.length - 1 - r)) xs.length

/-- Conditional expected next size under the actual fresh uniform current
occurrence draw. There is no distinctness or target-rank restriction. -/
theorem nextSize_drift (k : Nat) (head : α) (tail : List α) :
    (∑ i : Fin (tail.length + 1),
      RandomQuickSort.uniformIndex tail.length i *
        (nextSize k (head :: tail) i : ℝ≥0∞)) ≤
          (3 / 4 : ℝ≥0∞) * (tail.length + 1 : Nat) := by
  have hs : (∑ i : Fin (tail.length + 1), nextSize k (head :: tail) i) ≤
      rankSideSum (tail.length + 1) := nextSize_sum_le k (head :: tail)
  simp only [RandomQuickSort.uniformIndex_apply, ← Finset.mul_sum]
  calc
    _ ≤ (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) *
        (rankSideSum (tail.length + 1) : ℝ≥0∞) := by
      apply mul_le_mul_right
      rw [← Nat.cast_sum]
      exact_mod_cast hs
    _ ≤ _ := rankSideSum_mean_le (tail.length + 1) (Nat.succ_pos _)

/-- Strong induction follows only the actual selected strict child. It uses
the established conditional drift and the exact checked scan recurrence. -/
theorem scanExpectation_linear_le (k : Nat) (xs : List α) :
    scanExpectation k xs ≤ 4 * (xs.length : ℝ≥0∞) := by
  match xs with
  | [] => simp
  | head :: tail =>
      have hc (i : Fin (tail.length + 1)) :
          (match (stepRun k (head :: tail) i).1 with
            | Sum.inl (j, ys) => scanExpectation j ys
            | Sum.inr _ => 0) ≤ 4 * (nextSize k (head :: tail) i : ℝ≥0∞) := by
        cases hstep : (stepRun k (head :: tail) i).1 with
        | inl state =>
            rcases state with ⟨j, ys⟩
            simpa only [nextSize, hstep] using scanExpectation_linear_le j ys
        | inr _p => simp [nextSize, hstep]
      rw [scanExpectation_cons]
      calc
        _ ≤ ((tail.length + 1 : Nat) : ℝ≥0∞) +
            (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) *
              ∑ i : Fin (tail.length + 1),
                4 * (nextSize k (head :: tail) i : ℝ≥0∞) := by
          apply add_le_add_right
          apply mul_le_mul_right
          exact Finset.sum_le_sum (fun i _ => hc i)
        _ = ((tail.length + 1 : Nat) : ℝ≥0∞) +
            4 * (∑ i : Fin (tail.length + 1),
              RandomQuickSort.uniformIndex tail.length i *
                (nextSize k (head :: tail) i : ℝ≥0∞)) := by
          simp only [RandomQuickSort.uniformIndex_apply, ← Finset.mul_sum]
          ac_rfl
        _ ≤ ((tail.length + 1 : Nat) : ℝ≥0∞) +
            4 * ((3 / 4 : ℝ≥0∞) * (tail.length + 1 : Nat)) :=
          add_le_add_right (mul_le_mul_right (nextSize_drift k head tail) 4) _
        _ = _ := by
          simp only [List.length_cons]
          rw [← mul_assoc, four_mul_three_quarters]
          ring
termination_by xs.length
decreasing_by
  exact (stepRun_child k (head :: tail) i j ys hstep).1

/-- Actual scan expectation is uniformly linear for every worker input. -/
theorem scanExpectation_linear_bounds (k : Nat) (xs : List α) :
    (xs.length : ℝ≥0∞) ≤ scanExpectation k xs ∧
      scanExpectation k xs ≤ 4 * (xs.length : ℝ≥0∞) :=
  ⟨scanExpectation_initial_le k xs, scanExpectation_linear_le k xs⟩

/-- Transport the finite lower expectation bound to the actual real mean. -/
theorem scanMean_linear_le (k : Nat) (xs : List α) :
    scanMean k xs ≤ 4 * (xs.length : ℝ) := by
  have hb : 4 * (xs.length : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top _)
  rw [scanMean_eq_toReal]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast] using
    ENNReal.toReal_mono hb (scanExpectation_linear_le k xs)

theorem scanMean_linear_bounds (k : Nat) (xs : List α) :
    (xs.length : ℝ) ≤ scanMean k xs ∧ scanMean k xs ≤ 4 * (xs.length : ℝ) :=
  ⟨scanMean_initial_le k xs, scanMean_linear_le k xs⟩

/-- The same actual source-call model has linear expectation. Its coefficient
nine and invalid-empty offset two are the already checked pathwise bridge. -/
theorem sourceExpectation_linear_bounds (k : Nat) (xs : List α) :
    (xs.length : ℝ≥0∞) ≤ sourceExpectation k xs ∧
      sourceExpectation k xs ≤ 36 * (xs.length : ℝ≥0∞) + 2 := by
  constructor
  · exact (scanExpectation_initial_le k xs).trans (sourceExpectation_comparison k xs).1
  · calc
      _ ≤ 9 * scanExpectation k xs + 2 := (sourceExpectation_comparison k xs).2
      _ ≤ 9 * (4 * (xs.length : ℝ≥0∞)) + 2 :=
        add_le_add_left (mul_le_mul_right (scanExpectation_linear_le k xs) 9) 2
      _ = _ := by ring

theorem sourceMean_linear_bounds (k : Nat) (xs : List α) :
    (xs.length : ℝ) ≤ sourceMean k xs ∧
      sourceMean k xs ≤ 36 * (xs.length : ℝ) + 2 := by
  have hw := scanMean_linear_bounds k xs
  have hc := sourceMean_comparison k xs
  constructor
  · exact hw.1.trans hc.1
  · linarith [hw.2, hc.2]

end Ordered
end
end Resources.RandomSelection
