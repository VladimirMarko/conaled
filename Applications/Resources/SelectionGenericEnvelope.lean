import Applications.Resources.SelectionBounds
import Applications.Resources.SelectionEnvelope

/-! Actual generic selection counts have a uniform finite-size envelope.

The existing worker is unchanged. Groups at least two and cutoffs at least
one ensure both reached recursive lists are strictly smaller. The source's
actual local operations fit the scalar envelope's tariff. This establishes
a bound independent of payload values and ranks before any finite prefix is
used in the separate contracting-majorant argument for groups at least five.

The envelope itself is deliberately coarse; no linear bound is asserted here.
Mathematical source: FDSA Exercise3.8, with the Chapter3 source-call tariff.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Selection
open Applications.Selection
open Resources.SelectionAuxiliary Resources.SelectionMedians Resources.SelectionEnvelope
universe u
variable {α : Type u} [LinearOrder α]

/-- The actual generic recursive pivot has the mathematical median value. -/
theorem selectRunWith_median_value (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (xs : List α) :
    (selectRunWith d cutoff hd hc (((xs.length ⌈/⌉ d) - 1) / 2)
      (chunkMediansRun d xs).1).1 = medianOfMedians d xs := by
  rw [selectRunWith_value, chunkMediansRun_value, medianOfMedians,
    lowerMedianWith_value _ head_pivot_valid, length_chunkMedians]

/-- The generic worker's first recursive list is nonempty and smaller above
singleton size. This statement requires neither pivot balance nor a cost law. -/
theorem chunkMediansRun_proper_size (d : Nat) (xs : List α)
    (hd : 2 ≤ d) (hx : 1 < xs.length) :
    0 < (chunkMediansRun d xs).1.length ∧
      (chunkMediansRun d xs).1.length < xs.length := by
  constructor
  · apply List.length_pos_iff.mpr
    intro h
    rcases (chunkMediansRun_eq_nil_iff d xs).mp h with h | h
    · omega
    · subst xs
      simp only [List.length_nil] at hx
      omega
  · rw [chunkMediansRun_length]
    have h : xs.length ⌈/⌉ d ≤ xs.length - 1 := by
      apply (ceilDiv_le_iff_le_mul (by omega : 0 < d)).mpr
      calc
        xs.length ≤ 2 * (xs.length - 1) := by omega
        _ ≤ d * (xs.length - 1) := Nat.mul_le_mul_right _ hd
    omega

/-- Every local call is charged. The generic coefficient includes the actual
chop/map cost and both bucket lengths, though the left branch omits the latter
equal-length traversal. This auxiliary inequality also holds at d=0. -/
theorem selectRunWith_local_cost_bound (d : Nat) (xs : List α) (p : α) :
    1 + (SymmetricCosts.lengthRun xs).2 + (chunkMediansRun d xs).2 +
      (Partition.partitionRun p xs).2 + (SymmetricCosts.lengthRun (partition3 p xs).1).2 +
      (SymmetricCosts.lengthRun (partition3 p xs).2.1).2 ≤
        tollCoefficient d * xs.length + 7 := by
  have hc := chunkMediansRun_bound d xs
  have hceil : xs.length ⌈/⌉ d ≤ xs.length := by
    simpa only [Applications.Sequences.Chunks.length_chop] using
      Applications.Sequences.Chunks.length_chop_le d xs
  have hmul := Nat.mul_le_mul_left (d ^ 2 + 4 * d + 3) hceil
  have hprep : (chunkMediansRun d xs).2 ≤ (d ^ 2 + 4 * d + 8) * xs.length + 2 := by
    calc
      (chunkMediansRun d xs).2 ≤
          5 * xs.length + (d ^ 2 + 4 * d + 3) * xs.length + 2 := by omega
      _ = (d ^ 2 + 4 * d + 8) * xs.length + 2 := by ring
  have parts := partition_lengths p xs
  have hl : (partition3 p xs).1.length ≤ xs.length := by omega
  have he : (partition3 p xs).2.1.length ≤ xs.length := by omega
  simp only [SymmetricCosts.lengthRun_exact, Partition.partitionRun_cost]
  unfold tollCoefficient
  nlinarith

/-- All valid executions fit a size-only budget, for every terminating group
and cutoff. Equal-branch transfer uses zero second-child cost, not an empty
selection call. No bound on the payload domain is assumed. -/
theorem selectRunWith_cost_le_envelope_of_lt (d cutoff : Nat)
    (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (k : Nat) (xs : List α) (hk : k < xs.length) :
    (selectRunWith d cutoff hd hc k xs).2 ≤ envelope d xs.length := by
  suffices h : ∀ n (ys : List α), ys.length = n →
      ∀ j, j < ys.length → (selectRunWith d cutoff hd hc j ys).2 ≤ envelope d n by
    exact h xs.length xs rfl k hk
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ys hyn j hj
    by_cases hs : ys.length ≤ cutoff
    · rw [selectRunWith_small d cutoff hd hc j ys hj hs]
      change 1 + (SymmetricCosts.lengthRun ys).2 + (slowSelectRun j ys).2 ≤ envelope d n
      calc
        1 + (SymmetricCosts.lengthRun ys).2 + (slowSelectRun j ys).2 ≤ smallBudget n := by
          simpa only [smallBudget, pow_two, hyn] using slowSelectRun_entry_bound j ys hj
        _ ≤ envelope d n := small_budget_le d n
    · have large : cutoff < ys.length := Nat.lt_of_not_ge hs
      let ms := (chunkMediansRun d ys).1
      let i := ((ys.length ⌈/⌉ d) - 1) / 2
      have proper : 0 < ms.length ∧ ms.length < ys.length :=
        chunkMediansRun_proper_size d ys hd (by omega)
      have hmshort : ms.length < n := by omega
      have hi : i < ms.length := by
        have hmlen : ms.length = ys.length ⌈/⌉ d := chunkMediansRun_length d ys
        dsimp only [i]
        omega
      obtain ⟨p, hp⟩ := selectRunWith_exists d cutoff hd hc i ms hi
      have hpm : medianOfMedians d ys = some p :=
        (selectRunWith_median_value d cutoff hd hc ys).symm.trans hp
      have strict := partition_strict_sizes p ys (medianOfMedians_mem d ys p hpm)
      have pivot_cost := ih ms.length hmshort ms rfl i hi
      let localCost := 1 + (SymmetricCosts.lengthRun ys).2 + (chunkMediansRun d ys).2 +
        (Partition.partitionRun p ys).2 + (SymmetricCosts.lengthRun (partition3 p ys).1).2 +
        (SymmetricCosts.lengthRun (partition3 p ys).2.1).2
      have local_bound : localCost ≤ tollCoefficient d * n + 7 := by
        dsimp only [localCost]
        simpa only [hyn] using selectRunWith_local_cost_bound d ys p
      rw [selectRunWith_cost_step d cutoff hd hc j ys hj large p hp]
      change 1 + (SymmetricCosts.lengthRun ys).2 + (chunkMediansRun d ys).2 +
        (selectRunWith d cutoff hd hc i ms).2 + (Partition.partitionRun p ys).2 +
        (SymmetricCosts.lengthRun (partition3 p ys).1).2 +
        (if j < (partition3 p ys).1.length then
          (selectRunWith d cutoff hd hc j (partition3 p ys).1).2
        else (SymmetricCosts.lengthRun (partition3 p ys).2.1).2 +
          if j < (partition3 p ys).1.length + (partition3 p ys).2.1.length then 0
          else (selectRunWith d cutoff hd hc
            (j - (partition3 p ys).1.length - (partition3 p ys).2.1.length)
            (partition3 p ys).2.2).2) ≤ envelope d n
      by_cases hl : j < (partition3 p ys).1.length
      · rw [ite_eq_left hl]
        have child := ih (partition3 p ys).1.length (by omega)
          (partition3 p ys).1 rfl j hl
        apply two_child_budget_le d n ms.length (partition3 p ys).1.length
          (selectRunWith d cutoff hd hc i ms).2
          (selectRunWith d cutoff hd hc j (partition3 p ys).1).2 localCost _
          hmshort (by omega) pivot_cost child local_bound
        dsimp only [localCost]
        omega
      · rw [ite_eq_right hl]
        by_cases he : j < (partition3 p ys).1.length + (partition3 p ys).2.1.length
        · rw [ite_eq_left he]
          apply two_child_budget_le d n ms.length 0
            (selectRunWith d cutoff hd hc i ms).2 0 localCost _
            hmshort (by omega) pivot_cost (Nat.zero_le _) local_bound
          dsimp only [localCost]
          omega
        · rw [ite_eq_right he]
          have parts := partition_lengths p ys
          have hj' : j - (partition3 p ys).1.length - (partition3 p ys).2.1.length <
              (partition3 p ys).2.2.length := by omega
          have child := ih (partition3 p ys).2.2.length (by omega)
            (partition3 p ys).2.2 rfl
            (j - (partition3 p ys).1.length - (partition3 p ys).2.1.length) hj'
          apply two_child_budget_le d n ms.length (partition3 p ys).2.2.length
            (selectRunWith d cutoff hd hc i ms).2
            (selectRunWith d cutoff hd hc
              (j - (partition3 p ys).1.length - (partition3 p ys).2.1.length)
              (partition3 p ys).2.2).2 localCost _
            hmshort (by omega) pivot_cost child local_bound
          dsimp only [localCost]
          omega

/-- The actual n+2 invalid extension fits the same uniform envelope. -/
theorem selectRunWith_cost_le_envelope (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) :
    (selectRunWith d cutoff hd hc k xs).2 ≤ envelope d xs.length := by
  by_cases hk : k < xs.length
  · exact selectRunWith_cost_le_envelope_of_lt d cutoff hd hc k xs hk
  · rw [selectRunWith_of_invalid d cutoff hd hc k xs (Nat.le_of_not_gt hk)]
    exact invalid_budget_le d xs.length

/-- The finite-size budget is fixed before any payload type, values or rank
are supplied. It does not take a maximum over an infinite input domain. -/
theorem selectRunWith_uniform_prefix_bound (d cutoff : Nat)
    (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (N : Nat) :
    ∀ (β : Type u) [LinearOrder β] (xs : List β) (k : Nat), xs.length ≤ N →
      (selectRunWith d cutoff hd hc k xs).2 ≤ envelope d N := by
  intro β inst ys j hn
  exact (selectRunWith_cost_le_envelope d cutoff hd hc j ys).trans (envelope_mono d hn)

end Resources.Selection
