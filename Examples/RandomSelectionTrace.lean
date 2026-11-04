import Applications.Resources.RandomSelectionTrace
import Examples.RandomSelectionEndpoints

/-! Exact trace atoms calculated before the trace factorization proofs.

The unsorted interior-rank path switches from a minimum to a maximum and has
sizes 3,2,1, value 2, scan volume 6, source cost 33 and probability 1/6. The signed
five-element case has value 5, scan volume 15, source cost 67 and probability
1/120. Both complete-outcome atoms are derived through actual recursive-step
factorization; their trace atoms use the supported-trace uniqueness bridge.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomSelectionTrace
open Resources.RandomSelection Applications.Selection
open scoped ENNReal
universe u
variable {α : Type u}

noncomputable section

private theorem inverse_nat_product (m n : Nat) :
    ((m : ℝ≥0∞)⁻¹) * ((n : ℝ≥0∞)⁻¹) = (((m * n : Nat) : ℝ≥0∞)⁻¹) := by
  rw [Nat.cast_mul]
  exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top n))
    (Or.inl (ENNReal.natCast_ne_top m))).symm

section Ordered
variable [LinearOrder α]

theorem singleton_trace_atom (x : α) : traceLaw 0 [x] [(1, 0)] = 1 := by
  have hr : (some x, ([(1, 0)], 9)) ∈ (run 0 [x]).support := by
    rw [PMF.mem_support_iff, run_singleton_atom]
    exact one_ne_zero
  exact (traceLaw_atom 0 [x] _ hr).trans (run_singleton_atom x)

theorem middle_child_atom :
    run 0 ([3, 2] : List Int) (some 2, ([(2, 0), (1, 0)], 19)) =
      (2 : ℝ≥0∞)⁻¹ := by
  have hs := Examples.RandomSelectionEndpoints.middle_rank_switch.2.2
  simpa [hs, prepend, run_singleton_atom] using
    run_child_atom 0 (3 : Int) [2] 0 0 [2] (congrArg Prod.fst hs)
      (some 2, ([(1, 0)], 9))

theorem middle_path_atom :
    run 1 ([3, 1, 2] : List Int) (some 2, ([(3, 1), (2, 0), (1, 0)], 33)) =
      (6 : ℝ≥0∞)⁻¹ := by
  have hs := Examples.RandomSelectionEndpoints.unsorted_minimum_step
  calc
    _ = (3 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
      simpa [hs, prepend, middle_child_atom] using
        run_child_atom 1 (3 : Int) [1, 2] 1 0 [3, 2] (congrArg Prod.fst hs)
          (some 2, ([(2, 0), (1, 0)], 19))
    _ = (6 : ℝ≥0∞)⁻¹ := inverse_nat_product 3 2

theorem middle_path_trace :
    traceLaw 1 ([3, 1, 2] : List Int) [(3, 1), (2, 0), (1, 0)] =
      (6 : ℝ≥0∞)⁻¹ := by
  have hr : (some 2, ([(3, 1), (2, 0), (1, 0)], 33)) ∈
      (run 1 ([3, 1, 2] : List Int)).support := by
    rw [PMF.mem_support_iff, middle_path_atom]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top 6)
  exact (traceLaw_atom 1 ([3, 1, 2] : List Int) _ hr).trans middle_path_atom

/-- The public support-image law carries the positive complete-outcome witness
to the actual trace distribution at an unsorted interior-rank request. -/
theorem middle_path_supported :
    [(3, 1), (2, 0), (1, 0)] ∈ (traceLaw 1 ([3, 1, 2] : List Int)).support := by
  apply (traceLaw_support 1 ([3, 1, 2] : List Int) _).mpr
  refine ⟨(some 2, ([(3, 1), (2, 0), (1, 0)], 33)), ?_, rfl⟩
  rw [PMF.mem_support_iff, middle_path_atom]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top 6)

/-- The exact trace still identifies the actual value and source cost. -/
theorem middle_path_observations (r : Outcome Int)
    (hr : r ∈ (run 1 [3, 1, 2]).support)
    (ht : r.2.1 = [(3, 1), (2, 0), (1, 0)]) :
    r.1 = some 2 ∧ scanVolume r.2.1 = 6 ∧ r.2.2 = 33 := by
  have hs : (some 2, ([(3, 1), (2, 0), (1, 0)], 33)) ∈
      (run 1 ([3, 1, 2] : List Int)).support := by
    rw [PMF.mem_support_iff, middle_path_atom]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top 6)
  have he := run_trace_injective 1 [3, 1, 2] r _ hr hs ht
  rw [he]
  decide

theorem negative_path_atom :
    run 3 ([3, -2, 8, 0, 5] : List Int)
      (some 5, ([(5, 1), (4, 2), (3, 0), (2, 0), (1, 0)], 67)) =
      (120 : ℝ≥0∞)⁻¹ := by
  have h2 : run 0 ([8, 5] : List Int) (some 5, ([(2, 0), (1, 0)], 19)) =
      (2 : ℝ≥0∞)⁻¹ := by
    have hs : stepRun 0 ([8, 5] : List Int) 0 = (Sum.inl (0, [5]), 10) := by
      norm_num [stepRun_eq, partition3_eq_filters]
    simpa [hs, prepend, run_singleton_atom] using
      run_child_atom 0 (8 : Int) [5] 0 0 [5] (congrArg Prod.fst hs)
        (some 5, ([(1, 0)], 9))
  have h3 : run 1 ([3, 8, 5] : List Int)
      (some 5, ([(3, 0), (2, 0), (1, 0)], 32)) = (6 : ℝ≥0∞)⁻¹ := by
    have hs : stepRun 1 ([3, 8, 5] : List Int) 0 = (Sum.inl (0, [8, 5]), 13) := by
      norm_num [stepRun_eq, partition3_eq_filters]
    calc
      _ = (3 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
        simpa [hs, prepend, h2] using
          run_child_atom 1 (3 : Int) [8, 5] 0 0 [8, 5] (congrArg Prod.fst hs)
            (some 5, ([(2, 0), (1, 0)], 19))
      _ = (6 : ℝ≥0∞)⁻¹ := inverse_nat_product 3 2
  have h4 : run 2 ([3, 8, 0, 5] : List Int)
      (some 5, ([(4, 2), (3, 0), (2, 0), (1, 0)], 49)) = (24 : ℝ≥0∞)⁻¹ := by
    have hs : stepRun 2 ([3, 8, 0, 5] : List Int) 2 =
        (Sum.inl (1, [3, 8, 5]), 17) := by
      norm_num [stepRun_eq, partition3_eq_filters]
    calc
      _ = (4 : ℝ≥0∞)⁻¹ * (6 : ℝ≥0∞)⁻¹ := by
        simpa [hs, prepend, h3] using
          run_child_atom 2 (3 : Int) [8, 0, 5] 2 1 [3, 8, 5] (congrArg Prod.fst hs)
            (some 5, ([(3, 0), (2, 0), (1, 0)], 32))
      _ = (24 : ℝ≥0∞)⁻¹ := inverse_nat_product 4 6
  have hs := Examples.RandomSelectionEndpoints.negative_minimum_step
  calc
    _ = (5 : ℝ≥0∞)⁻¹ * (24 : ℝ≥0∞)⁻¹ := by
      simpa [hs, prepend, h4] using
        run_child_atom 3 (3 : Int) [-2, 8, 0, 5] 1 2 [3, 8, 0, 5]
          (congrArg Prod.fst hs) (some 5, ([(4, 2), (3, 0), (2, 0), (1, 0)], 49))
    _ = (120 : ℝ≥0∞)⁻¹ := inverse_nat_product 5 24

theorem negative_path_trace :
    traceLaw 3 ([3, -2, 8, 0, 5] : List Int)
      [(5, 1), (4, 2), (3, 0), (2, 0), (1, 0)] = (120 : ℝ≥0∞)⁻¹ := by
  have hr : (some 5, ([(5, 1), (4, 2), (3, 0), (2, 0), (1, 0)], 67)) ∈
      (run 3 ([3, -2, 8, 0, 5] : List Int)).support := by
    rw [PMF.mem_support_iff, negative_path_atom]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top 120)
  exact (traceLaw_atom 3 ([3, -2, 8, 0, 5] : List Int) _ hr).trans negative_path_atom

theorem duplicate_trace_atom :
    traceLaw 1 ([4, 4, 4] : List Nat) [(3, 0)] = (3 : ℝ≥0∞)⁻¹ := by
  have ha : run 1 ([4, 4, 4] : List Nat) (some 4, ([(3, 0)], 15)) =
      (3 : ℝ≥0∞)⁻¹ := run_replicate_valid_atom 2 1 4 (by decide) 0
  have hr : (some 4, ([(3, 0)], 15)) ∈ (run 1 ([4, 4, 4] : List Nat)).support := by
    rw [PMF.mem_support_iff, ha]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top 3)
  exact (traceLaw_atom 1 ([4, 4, 4] : List Nat) _ hr).trans ha

theorem empty_trace_atom (k : Nat) : traceLaw k ([] : List α) [] = 1 := by
  rw [traceLaw_nil]
  exact PMF.pure_apply_self []

theorem invalid_singleton_trace_atom :
    traceLaw 1 ([7] : List Nat) [(1, 0)] = 1 := by
  have ha : run 1 ([7] : List Nat) (none, ([(1, 0)], 11)) = 1 := by
    simpa using run_replicate_invalid_atom 0 1 (7 : Nat) (by decide) 0
  have hr : (none, ([(1, 0)], 11)) ∈ (run 1 ([7] : List Nat)).support := by
    rw [PMF.mem_support_iff, ha]
    exact one_ne_zero
  exact (traceLaw_atom 1 ([7] : List Nat) _ hr).trans ha

/-- Fixed initial state is essential: the same trace occurs at valid and
invalid singleton ranks, with different values and measured source costs. -/
theorem different_initial_rank_boundary (x : α) :
    run 0 [x] = PMF.pure (some x, ([(1, 0)], 9)) ∧
      run 1 [x] = PMF.pure (none, ([(1, 0)], 11)) ∧
      (some x, ([(1, 0)], 9)) ≠ (none, ([(1, 0)], 11)) := by
  have hs := Examples.RandomSelectionEqual.singleton_boundary x
  exact ⟨hs.1, hs.2, by simp⟩

/-- Support is essential even at a fixed initial state: replacing the actual
empty source cost two by three preserves the trace but gives a zero atom. -/
theorem unsupported_empty_trace_boundary (k : Nat) :
    run k ([] : List Nat) (none, ([], 3)) = 0 ∧
      traceLaw k ([] : List Nat) [] = 1 ∧
      (none, ([], 3)) ∉ (run k ([] : List Nat)).support := by
  have ha : run k ([] : List Nat) (none, ([], 3)) = 0 := by
    rw [run_nil]
    exact PMF.pure_apply_of_ne _ _ (by decide)
  exact ⟨ha, empty_trace_atom k, (PMF.apply_eq_zero_iff _ _).mp ha⟩

theorem arbitrary_supported_trace (k : Nat) (xs : List α) (r s : Outcome α)
    (hr : r ∈ (run k xs).support) (hs : s ∈ (run k xs).support)
    (ht : r.2.1 = s.2.1) : r = s ∧ traceLaw k xs r.2.1 = run k xs r :=
  ⟨run_trace_injective k xs r s hr hs ht, traceLaw_atom k xs r hr⟩

end Ordered
end
end Examples.RandomSelectionTrace
