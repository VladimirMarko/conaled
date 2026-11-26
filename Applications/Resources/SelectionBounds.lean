import Applications.Resources.Selection
import Applications.Resources.SelectionRecurrence

/-! The actual nested selector is bounded by FDSA's scalar recurrence.

The pivot observation is derived from the checked measured execution and its
rank law. Both strict bucket sizes then use the duplicate-aware balance result.
The cost induction retains the actual selected branch and charges the entry,
cached length, chopping, median map, one-pass partition and reached lengths.
It assumes no execution bound, growth law or payload finiteness.

The book's valid-rank bound is extended to the public invalid-rank guard. One
pair of affine constants works before the payload type, list and rank are
chosen. These are source-call counts, with the tariff of Selection.lean.
Mathematical source: FDSA Chapter 3, printed pp.40–44, (3.14) and Theorem3.10.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Selection
open Applications.Selection
open Resources.SelectionAuxiliary Resources.SelectionMedians Resources.SelectionRecurrence
universe u
variable {α : Type u} [LinearOrder α]

/-- The first recursive input has exactly the scalar's first child size. -/
theorem chunkMediansRun_length_eq_pivotSize (xs : List α) :
    (chunkMediansRun 5 xs).1.length = pivotSize xs.length := by
  rw [chunkMediansRun_length, Nat.ceilDiv_eq_add_pred_div]
  unfold pivotSize
  omega

/-- Actual recursive median selection agrees with the mathematical pivot,
including the empty optional result. This uses the proved worker value law. -/
theorem selectRun_median_value (xs : List α) :
    (selectRun (((xs.length ⌈/⌉ 5) - 1) / 2) (chunkMediansRun 5 xs).1).1 =
      medianOfMedians 5 xs := by
  rw [selectRun_value, chunkMediansRun_value, medianOfMedians,
    lowerMedianWith_value _ head_pivot_valid, length_chunkMedians]

/-- The observed recursive pivot controls both strict sides, even with ties. -/
theorem selectRun_pivot_size_bounds (xs : List α) (p : α)
    (hp : (selectRun (((xs.length ⌈/⌉ 5) - 1) / 2)
      (chunkMediansRun 5 xs).1).1 = some p) :
    (partition3 p xs).1.length ≤ sideSize xs.length ∧
      (partition3 p xs).2.2.length ≤ sideSize xs.length := by
  have hpm : medianOfMedians 5 xs = some p :=
    (selectRun_median_value xs).symm.trans hp
  have h := medianOfMedians_five_count_bounds xs p hpm
  have hl : (partition3 p xs).1.length = xs.countP (fun x => decide (x < p)) := by
    simp only [partition3_eq_filters, List.countP_eq_length_filter]
  have hr : (partition3 p xs).2.2.length = xs.countP (fun x => decide (p < x)) := by
    simp only [partition3_eq_filters, List.countP_eq_length_filter]
  rw [hl, hr]
  simp only [Nat.ceilDiv_eq_add_pred_div] at h
  unfold sideSize
  constructor <;> omega

/-- A common upper budget includes both reached bucket-length traversals.
The left branch actually omits the equal length; including it here is safe.
The two recursive selection counts are absent from this local expression. -/
theorem selectRun_local_cost_bound (xs : List α) (p : α) :
    1 + (SymmetricCosts.lengthRun xs).2 + (chunkMediansRun 5 xs).2 +
      (Partition.partitionRun p xs).2 + (SymmetricCosts.lengthRun (partition3 p xs).1).2 +
      (SymmetricCosts.lengthRun (partition3 p xs).2.1).2 ≤ 19 * xs.length + 54 := by
  have hc := chunkMediansRun_five_bound xs
  have hparts := partition_lengths p xs
  have hl : (partition3 p xs).1.length ≤ xs.length := by omega
  have he : (partition3 p xs).2.1.length ≤ xs.length := by omega
  simp only [SymmetricCosts.lengthRun_exact, Partition.partitionRun_cost]
  omega

/-- FDSA (3.14): the actual valid-rank execution is bounded by the scalar F.
Both child ranks are proved valid before applying their size induction. -/
theorem selectRun_cost_le_F_of_lt (k : Nat) (xs : List α) (hk : k < xs.length) :
    (selectRun k xs).2 ≤ F xs.length := by
  suffices h : ∀ n (ys : List α), ys.length = n →
      ∀ j, j < ys.length → (selectRun j ys).2 ≤ F n by
    exact h xs.length xs rfl k hk
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ys hyn j hj
    by_cases hs : ys.length ≤ 20
    · rw [selectRun_small j ys hj hs]
      change 1 + (SymmetricCosts.lengthRun ys).2 + (slowSelectRun j ys).2 ≤ F n
      rw [F_of_le_twenty n (by omega)]
      exact slowSelectRun_cutoff_bound j ys hj hs
    · have large : 20 < ys.length := Nat.lt_of_not_ge hs
      have large_n : 20 < n := by omega
      let ms := (chunkMediansRun 5 ys).1
      let i := ((ys.length ⌈/⌉ 5) - 1) / 2
      have hm : ms.length = pivotSize n := by
        dsimp only [ms]
        rw [chunkMediansRun_length_eq_pivotSize, hyn]
      have hmshort : ms.length < n := by
        rw [hm]
        exact (pivotSize_lt_iff n).mpr (by omega)
      have hmpos : 0 < ms.length := by
        rw [hm]
        unfold pivotSize
        omega
      have hi : i < ms.length := by
        have hmlen : ms.length = ys.length ⌈/⌉ 5 := chunkMediansRun_length 5 ys
        dsimp only [i]
        omega
      obtain ⟨p, hp⟩ := selectRunWith_exists 5 20 (by decide) (by decide) i ms hi
      change (selectRun i ms).1 = some p at hp
      have hpm : medianOfMedians 5 ys = some p :=
        (selectRun_median_value ys).symm.trans hp
      have strict := partition_strict_sizes p ys (medianOfMedians_mem 5 ys p hpm)
      have sides := selectRun_pivot_size_bounds ys p hp
      have pivot_cost := ih ms.length hmshort ms rfl i hi
      have pivot_bound : (selectRun i ms).2 ≤ F (pivotSize n) := by
        simpa only [hm] using pivot_cost
      have toll := selectRun_local_cost_bound ys p
      rw [selectRun_cost_step j ys hj large p hp, F_of_twenty_lt n large_n]
      change 1 + (SymmetricCosts.lengthRun ys).2 + (chunkMediansRun 5 ys).2 +
        (selectRun i ms).2 + (Partition.partitionRun p ys).2 +
        (SymmetricCosts.lengthRun (partition3 p ys).1).2 +
        (if j < (partition3 p ys).1.length then (selectRun j (partition3 p ys).1).2
        else (SymmetricCosts.lengthRun (partition3 p ys).2.1).2 +
          if j < (partition3 p ys).1.length + (partition3 p ys).2.1.length then 0
          else (selectRun (j - (partition3 p ys).1.length - (partition3 p ys).2.1.length)
            (partition3 p ys).2.2).2) ≤ F (pivotSize n) + F (sideSize n) + 19 * n + 54
      by_cases hl : j < (partition3 p ys).1.length
      · rw [ite_eq_left hl]
        have child := ih (partition3 p ys).1.length (by omega)
          (partition3 p ys).1 rfl j hl
        have child_bound : (selectRun j (partition3 p ys).1).2 ≤ F (sideSize n) := by
          simpa only [hyn] using child.trans (F_monotone sides.1)
        omega
      · rw [ite_eq_right hl]
        by_cases he : j < (partition3 p ys).1.length + (partition3 p ys).2.1.length
        · rw [ite_eq_left he]
          omega
        · rw [ite_eq_right he]
          have parts := partition_lengths p ys
          have hj' : j - (partition3 p ys).1.length - (partition3 p ys).2.1.length <
              (partition3 p ys).2.2.length := by omega
          have child := ih (partition3 p ys).2.2.length (by omega)
            (partition3 p ys).2.2 rfl
            (j - (partition3 p ys).1.length - (partition3 p ys).2.1.length) hj'
          have child_bound :
              (selectRun (j - (partition3 p ys).1.length - (partition3 p ys).2.1.length)
                (partition3 p ys).2.2).2 ≤ F (sideSize n) := by
            simpa only [hyn] using child.trans (F_monotone sides.2)
          omega

/-- The entry/length-only invalid extension also fits the same scalar. -/
theorem invalid_cost_le_F (n : Nat) : n + 2 ≤ F n := by
  by_cases hn : n ≤ 20
  · rw [F_of_le_twenty n hn]
    omega
  · rw [F_of_twenty_lt n (Nat.lt_of_not_ge hn)]
    omega

/-- The source bound extends uniformly to every public rank, including empty
lists and invalid indices. No inhabitedness assumption is needed. -/
theorem selectRun_cost_le_F (k : Nat) (xs : List α) :
    (selectRun k xs).2 ≤ F xs.length := by
  by_cases hk : k < xs.length
  · exact selectRun_cost_le_F_of_lt k xs hk
  · rw [selectRun_of_invalid k xs (Nat.le_of_not_gt hk)]
    exact invalid_cost_le_F xs.length

/-- One pair of constants works before the payload type, list and rank are
chosen. In particular the constants cannot depend on the selected value. -/
theorem selectRun_exists_uniform_affine_bound :
    ∃ A B : Nat, ∀ (β : Type u) [LinearOrder β] (xs : List β) (k : Nat),
      (selectRun k xs).2 ≤ A * xs.length + B := by
  obtain ⟨A, B, bound⟩ := Resources.SelectionRecurrence.exists_affine_bound
  refine ⟨A, B, ?_⟩
  intro β inst ys j
  exact (selectRun_cost_le_F j ys).trans (bound ys.length)

/-- For positive input sizes the same uniform affine constants give one
multiplicative linear constant; empty inputs retain the affine statement. -/
theorem selectRun_exists_uniform_linear_bound :
    ∃ C : Nat, ∀ (β : Type u) [LinearOrder β] (xs : List β) (k : Nat),
      0 < xs.length → (selectRun k xs).2 ≤ C * xs.length := by
  obtain ⟨A, B, bound⟩ := selectRun_exists_uniform_affine_bound
  refine ⟨A + B, ?_⟩
  intro β inst ys j hy
  have h := bound β ys j
  have hb : B ≤ B * ys.length := by nlinarith
  nlinarith

/-- Any size-indexed family of actual executions has ordinary linear growth.
Ranks may vary and need not be valid; their optional extension is already
covered. The hypothesis describes input sizes, not an assumed cost bound. -/
theorem selectRun_family_isBigO (inputs : Nat → List α) (ranks : Nat → Nat)
    (lengths : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => ((selectRun (ranks n) (inputs n)).2 : ℝ))
      (fun n => (n : ℝ)) := by
  obtain ⟨C, bound⟩ := selectRun_exists_uniform_linear_bound
  apply Resources.isBigO_of_nat_bound
    (fun n => (selectRun (ranks n) (inputs n)).2) (fun n => n) C 1
  intro n hn
  have positive : 0 < (inputs n).length := by rw [lengths n]; omega
  have h := bound α (inputs n) (ranks n) positive
  simpa only [lengths n] using h

end Resources.Selection
