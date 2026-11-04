import Applications.Resources.SelectionGenericEnvelope
import Applications.Resources.GroupSelectionRecurrence

/-! Actual generic selection counts satisfy the sufficient linear bound.

The finite base is fixed from the group and both cutoffs before any payload
type, input values or rank is chosen. The checked actual size envelope covers
the entire prefix even when the algorithm's cutoff exceeds the scalar cutoff.
Above both cutoffs, the actual pivot observation gives the duplicate-aware
side bounds. The induction retains one pivot call, at most one selected side,
and the source's proved local charges.

These scalar abbreviations do not alter the executable selector or its tariff.
Groups at least five are sufficient for this contracting recurrence argument;
no impossibility claim is made about other grouping sizes or strategies.
Mathematical source: FDSA Exercise 3.8 and the Chapter 3 source-call analysis.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Selection
open Applications.Selection
open Resources.SelectionMedians Resources.SelectionEnvelope
universe u
variable {α : Type u} [LinearOrder α]

noncomputable section

/-- The actual median-list size is exactly the generic scalar's first child. -/
theorem chunkMediansRun_length_eq_groupPivotChild (d : Nat) (xs : List α)
    (hd : 0 < d) :
    (chunkMediansRun d xs).1.length = GroupSelectionRecurrence.pivotChild d xs.length := by
  rw [chunkMediansRun_length]
  unfold GroupSelectionRecurrence.pivotChild GroupSelectionRecurrence.pivotFraction
  have quotient : (1 / (d : ℝ)) * (xs.length : ℝ) + 0 =
      (xs.length : ℝ) / (d : ℝ) := by ring
  rw [quotient, ceil_nat_div ℝ xs.length d hd]

/-- The observed recursive median controls both strict sides with ties and a
short final chunk retained. No distinctness or assumed balance is supplied. -/
theorem selectRunWith_pivot_size_bounds (d cutoff : Nat)
    (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (xs : List α) (p : α)
    (hp : (selectRunWith d cutoff hd hc (((xs.length ⌈/⌉ d) - 1) / 2)
      (chunkMediansRun d xs).1).1 = some p) :
    (partition3 p xs).1.length ≤ GroupSelectionRecurrence.sideChild d xs.length ∧
      (partition3 p xs).2.2.length ≤ GroupSelectionRecurrence.sideChild d xs.length := by
  have hpm : medianOfMedians d xs = some p :=
    (selectRunWith_median_value d cutoff hd hc xs).symm.trans hp
  have counts := medianOfMedians_count_bounds d xs p (by omega) hpm
  have hm : xs.length ⌈/⌉ d = GroupSelectionRecurrence.pivotChild d xs.length := by
    simpa only [chunkMediansRun_length] using
      chunkMediansRun_length_eq_groupPivotChild d xs (by omega)
  rw [hm] at counts
  have hl : (partition3 p xs).1.length = xs.countP (fun x => decide (x < p)) := by
    simp only [partition3_eq_filters, List.countP_eq_length_filter]
  have hr : (partition3 p xs).2.2.length = xs.countP (fun x => decide (p < x)) := by
    simp only [partition3_eq_filters, List.countP_eq_length_filter]
  rw [hl, hr]
  exact ⟨GroupSelectionRecurrence.two_group_bound_le_child d xs.length _ (by omega) counts.1,
    GroupSelectionRecurrence.two_group_bound_le_child d xs.length _ (by omega) counts.2⟩

/-- A uniform finite base, chosen before the payload type, list and rank. -/
def genericSelectionBase (d cutoff : Nat) : Nat :=
  envelope d (max cutoff (GroupSelectionRecurrence.cutoff d))

/-- The existing contracting scalar with the actual proved local tariff.
It is a cost majorant, not a replacement implementation of selection. -/
def genericSelectionMajorant (d cutoff : Nat) (hd : 5 ≤ d) (n : Nat) : Nat :=
  GroupSelectionRecurrence.majorant d (genericSelectionBase d cutoff)
    (tollCoefficient d) 7 hd n

theorem genericSelectionMajorant_small (d cutoff : Nat) (hd : 5 ≤ d)
    (n : Nat) (small : n ≤ GroupSelectionRecurrence.cutoff d) :
    genericSelectionMajorant d cutoff hd n = genericSelectionBase d cutoff :=
  GroupSelectionRecurrence.majorant_small d (genericSelectionBase d cutoff)
    (tollCoefficient d) 7 hd n small

theorem genericSelectionMajorant_large (d cutoff : Nat) (hd : 5 ≤ d)
    (n : Nat) (large : GroupSelectionRecurrence.cutoff d < n) :
    genericSelectionMajorant d cutoff hd n =
      genericSelectionMajorant d cutoff hd (GroupSelectionRecurrence.pivotChild d n) +
        genericSelectionMajorant d cutoff hd (GroupSelectionRecurrence.sideChild d n) +
        tollCoefficient d * n + 7 :=
  GroupSelectionRecurrence.majorant_large d (genericSelectionBase d cutoff)
    (tollCoefficient d) 7 hd n large

theorem genericSelectionBase_le_majorant (d cutoff : Nat) (hd : 5 ≤ d) (n : Nat) :
    genericSelectionBase d cutoff ≤ genericSelectionMajorant d cutoff hd n :=
  GroupSelectionRecurrence.base_le_majorant d (genericSelectionBase d cutoff)
    (tollCoefficient d) 7 hd n

theorem genericSelectionMajorant_monotone (d cutoff : Nat) (hd : 5 ≤ d) :
    Monotone (genericSelectionMajorant d cutoff hd) :=
  GroupSelectionRecurrence.majorant_monotone d (genericSelectionBase d cutoff)
    (tollCoefficient d) 7 hd

/-- Either cutoff can determine the finite prefix. The bound uses actual
execution and does not take a supremum over arbitrary payload values. -/
theorem selectRunWith_cost_le_groupBase_of_prefix (d cutoff : Nat)
    (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (k : Nat) (xs : List α)
    (prefix : xs.length ≤ cutoff ∨ xs.length ≤ GroupSelectionRecurrence.cutoff d) :
    (selectRunWith d cutoff hd hc k xs).2 ≤ genericSelectionBase d cutoff :=
  (selectRunWith_cost_le_envelope d cutoff hd hc k xs).trans
    (prefix_max_bound d cutoff (GroupSelectionRecurrence.cutoff d) xs.length prefix)

/-- The entry-and-length cost of every invalid rank fits the same scalar. -/
theorem invalid_cost_le_groupMajorant (d cutoff : Nat) (hd : 5 ≤ d) (n : Nat) :
    n + 2 ≤ genericSelectionMajorant d cutoff hd n := by
  by_cases small : n ≤ GroupSelectionRecurrence.cutoff d
  · rw [genericSelectionMajorant_small d cutoff hd n small]
    exact (invalid_budget_le d n).trans
      (prefix_max_bound d cutoff (GroupSelectionRecurrence.cutoff d) n (Or.inr small))
  · rw [genericSelectionMajorant_large d cutoff hd n (Nat.lt_of_not_ge small)]
    have coefficient : 1 ≤ tollCoefficient d := by unfold tollCoefficient; omega
    have charged : n ≤ tollCoefficient d * n := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right n coefficient
    omega

/-- Actual valid executions are bounded by the contracting group scalar.
The finite prefix is proved uniformly before this induction; no desired
runtime, growth or payload-finiteness hypothesis is assumed. -/
theorem selectRunWith_cost_le_groupMajorant_of_lt (d cutoff : Nat)
    (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (hgroup : 5 ≤ d) (k : Nat) (xs : List α)
    (hk : k < xs.length) :
    (selectRunWith d cutoff hd hc k xs).2 ≤ genericSelectionMajorant d cutoff hgroup xs.length := by
  suffices h : ∀ n (ys : List α), ys.length = n →
      ∀ j, j < ys.length →
        (selectRunWith d cutoff hd hc j ys).2 ≤ genericSelectionMajorant d cutoff hgroup n by
    exact h xs.length xs rfl k hk
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ys hyn j hj
    by_cases prefix : ys.length ≤ cutoff ∨ ys.length ≤ GroupSelectionRecurrence.cutoff d
    · have bounded := selectRunWith_cost_le_groupBase_of_prefix d cutoff hd hc j ys prefix
      exact bounded.trans (genericSelectionBase_le_majorant d cutoff hgroup n)
    · have large : cutoff < ys.length := by omega
      have large_n : GroupSelectionRecurrence.cutoff d < n := by omega
      let ms := (chunkMediansRun d ys).1
      let i := ((ys.length ⌈/⌉ d) - 1) / 2
      have proper : 0 < ms.length ∧ ms.length < ys.length :=
        chunkMediansRun_proper_size d ys hd (by omega)
      have hmshort : ms.length < n := by omega
      have hm : ms.length = GroupSelectionRecurrence.pivotChild d n := by
        dsimp only [ms]
        rw [chunkMediansRun_length_eq_groupPivotChild d ys (by omega), hyn]
      have hi : i < ms.length := by
        have hmlen : ms.length = ys.length ⌈/⌉ d := chunkMediansRun_length d ys
        dsimp only [i]
        omega
      obtain ⟨p, hp⟩ := selectRunWith_exists d cutoff hd hc i ms hi
      have hpm : medianOfMedians d ys = some p :=
        (selectRunWith_median_value d cutoff hd hc ys).symm.trans hp
      have strict := partition_strict_sizes p ys (medianOfMedians_mem d ys p hpm)
      have sides := selectRunWith_pivot_size_bounds d cutoff hd hc ys p hp
      have pivot_cost := ih ms.length hmshort ms rfl i hi
      have pivot_bound : (selectRunWith d cutoff hd hc i ms).2 ≤
          genericSelectionMajorant d cutoff hgroup (GroupSelectionRecurrence.pivotChild d n) := by
        simpa only [hm] using pivot_cost
      have toll : 1 + (SymmetricCosts.lengthRun ys).2 + (chunkMediansRun d ys).2 +
          (Partition.partitionRun p ys).2 + (SymmetricCosts.lengthRun (partition3 p ys).1).2 +
          (SymmetricCosts.lengthRun (partition3 p ys).2.1).2 ≤ tollCoefficient d * n + 7 := by
        simpa only [hyn] using selectRunWith_local_cost_bound d ys p
      rw [selectRunWith_cost_step d cutoff hd hc j ys hj large p hp,
        genericSelectionMajorant_large d cutoff hgroup n large_n]
      change 1 + (SymmetricCosts.lengthRun ys).2 + (chunkMediansRun d ys).2 +
        (selectRunWith d cutoff hd hc i ms).2 + (Partition.partitionRun p ys).2 +
        (SymmetricCosts.lengthRun (partition3 p ys).1).2 +
        (if j < (partition3 p ys).1.length then
          (selectRunWith d cutoff hd hc j (partition3 p ys).1).2
        else (SymmetricCosts.lengthRun (partition3 p ys).2.1).2 +
          if j < (partition3 p ys).1.length + (partition3 p ys).2.1.length then 0
          else (selectRunWith d cutoff hd hc
            (j - (partition3 p ys).1.length - (partition3 p ys).2.1.length)
            (partition3 p ys).2.2).2) ≤
        genericSelectionMajorant d cutoff hgroup (GroupSelectionRecurrence.pivotChild d n) +
          genericSelectionMajorant d cutoff hgroup (GroupSelectionRecurrence.sideChild d n) +
          tollCoefficient d * n + 7
      by_cases hl : j < (partition3 p ys).1.length
      · rw [ite_eq_left hl]
        have child := ih (partition3 p ys).1.length (by omega)
          (partition3 p ys).1 rfl j hl
        have child_bound : (selectRunWith d cutoff hd hc j (partition3 p ys).1).2 ≤
            genericSelectionMajorant d cutoff hgroup (GroupSelectionRecurrence.sideChild d n) := by
          simpa only [hyn] using child.trans
            (genericSelectionMajorant_monotone d cutoff hgroup sides.1)
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
              (selectRunWith d cutoff hd hc
                (j - (partition3 p ys).1.length - (partition3 p ys).2.1.length)
                (partition3 p ys).2.2).2 ≤
                genericSelectionMajorant d cutoff hgroup (GroupSelectionRecurrence.sideChild d n) := by
            simpa only [hyn] using child.trans
              (genericSelectionMajorant_monotone d cutoff hgroup sides.2)
          omega

/-- The same bound covers all ranks, including the actual invalid extension. -/
theorem selectRunWith_cost_le_groupMajorant (d cutoff : Nat)
    (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (hgroup : 5 ≤ d) (k : Nat) (xs : List α) :
    (selectRunWith d cutoff hd hc k xs).2 ≤ genericSelectionMajorant d cutoff hgroup xs.length := by
  by_cases hk : k < xs.length
  · exact selectRunWith_cost_le_groupMajorant_of_lt d cutoff hd hc hgroup k xs hk
  · rw [selectRunWith_of_invalid d cutoff hd hc k xs (Nat.le_of_not_gt hk)]
    exact invalid_cost_le_groupMajorant d cutoff hgroup xs.length

/-- The constants depend on the fixed group and cutoff, before any payload
type, list or rank is supplied. The all-size statement includes empty inputs. -/
theorem selectRunWith_exists_uniform_affine_bound (d cutoff : Nat)
    (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (hgroup : 5 ≤ d) :
    ∃ A B : Nat, ∀ (β : Type u) [LinearOrder β] (xs : List β) (k : Nat),
      (selectRunWith d cutoff hd hc k xs).2 ≤ A * xs.length + B := by
  obtain ⟨A, B, bound⟩ := GroupSelectionRecurrence.majorant_affine_bound d
    (genericSelectionBase d cutoff) (tollCoefficient d) 7 hgroup
  refine ⟨A, B, ?_⟩
  intro β inst ys j
  exact (selectRunWith_cost_le_groupMajorant d cutoff hd hc hgroup j ys).trans (bound ys.length)

/-- A single multiplicative constant works at every positive input size.
The empty input retains its separate cost two and the all-size affine bound. -/
theorem selectRunWith_exists_uniform_linear_bound (d cutoff : Nat)
    (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (hgroup : 5 ≤ d) :
    ∃ C : Nat, ∀ (β : Type u) [LinearOrder β] (xs : List β) (k : Nat),
      0 < xs.length → (selectRunWith d cutoff hd hc k xs).2 ≤ C * xs.length := by
  obtain ⟨A, B, bound⟩ := selectRunWith_exists_uniform_affine_bound d cutoff hd hc hgroup
  refine ⟨A + B, ?_⟩
  intro β inst ys j hy
  have h := bound β ys j
  have hb : B ≤ B * ys.length := by nlinarith
  nlinarith

/-- Actual size-indexed families have ordinary linear growth; the family
hypothesis supplies input sizes, not a desired runtime bound. -/
theorem selectRunWith_family_isBigO (d cutoff : Nat)
    (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (hgroup : 5 ≤ d)
    (inputs : Nat → List α) (ranks : Nat → Nat)
    (lengths : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => ((selectRunWith d cutoff hd hc (ranks n) (inputs n)).2 : ℝ))
      (fun n => (n : ℝ)) := by
  obtain ⟨C, bound⟩ := selectRunWith_exists_uniform_linear_bound d cutoff hd hc hgroup
  apply Resources.isBigO_of_nat_bound
    (fun n => (selectRunWith d cutoff hd hc (ranks n) (inputs n)).2) (fun n => n) C 1
  intro n hn
  have positive : 0 < (inputs n).length := by rw [lengths n]; omega
  have h := bound α (inputs n) (ranks n) positive
  simpa only [lengths n] using h

end
end Resources.Selection
