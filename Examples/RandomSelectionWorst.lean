import Applications.Resources.RandomSelectionWorst
import Examples.RandomSelectionTrace

/-! Independently calculated endpoint-path and source-cost cases.

The unsorted interior rank switches from minima to maxima; signed values give
a longer path. The range-four interior case has W10 but actual source cost48.
The universal client compares the witness with every supported execution.
Empty, invalid, all-equal and mixed-duplicate cases separate structural paths
from the distinct-input factorial and triangular theorems.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomSelectionWorst
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

theorem singleton_endpoint (x : α) :
    EndpointTrace 0 [x] [(1, 0)] ∧ ¬ EndpointTrace 0 [x] [] ∧
      traceLaw 0 [x] [(1, 0)] = 1 ∧ scanVolume [(1, 0)] = 1 :=
  ⟨endpointTrace_singleton x, endpointTrace_nil 0 [x],
    Examples.RandomSelectionTrace.singleton_trace_atom x, rfl⟩

theorem middle_endpoint_trace :
    EndpointTrace 1 ([3, 1, 2] : List Int) [(3, 1), (2, 0), (1, 0)] := by
  have hc : EndpointTrace 0 ([3, 2] : List Int) [(2, 0), (1, 0)] :=
    endpointTrace_child 0 [3, 2] 0 0 [2] [(1, 0)]
      Examples.RandomSelectionEndpoints.middle_rank_switch.2.1
      (congrArg Prod.fst Examples.RandomSelectionEndpoints.middle_rank_switch.2.2)
      (endpointTrace_singleton 2)
  exact endpointTrace_child 1 [3, 1, 2] 1 0 [3, 2] [(2, 0), (1, 0)]
    Examples.RandomSelectionEndpoints.middle_rank_switch.1
    (congrArg Prod.fst Examples.RandomSelectionEndpoints.unsorted_minimum_step) hc

theorem middle_endpoint_probability :
    EndpointTrace 1 ([3, 1, 2] : List Int) [(3, 1), (2, 0), (1, 0)] ∧
      run 1 ([3, 1, 2] : List Int)
        (some 2, ([(3, 1), (2, 0), (1, 0)], 33)) = (6 : ℝ≥0∞)⁻¹ ∧
      traceLaw 1 ([3, 1, 2] : List Int) [(3, 1), (2, 0), (1, 0)] =
        (6 : ℝ≥0∞)⁻¹ ∧ scanVolume [(3, 1), (2, 0), (1, 0)] = 6 :=
  ⟨middle_endpoint_trace, Examples.RandomSelectionTrace.middle_path_atom,
    Examples.RandomSelectionTrace.middle_path_trace, rfl⟩

theorem signed_endpoint_trace :
    EndpointTrace 3 ([3, -2, 8, 0, 5] : List Int)
      [(5, 1), (4, 2), (3, 0), (2, 0), (1, 0)] := by
  have h2 : EndpointTrace 0 ([8, 5] : List Int) [(2, 0), (1, 0)] := by
    apply endpointTrace_child 0 [8, 5] 0 0 [5] [(1, 0)]
    · norm_num [EndpointPivot]
    · norm_num [stepRun_eq, partition3_eq_filters]
    · exact endpointTrace_singleton 5
  have h3 : EndpointTrace 1 ([3, 8, 5] : List Int) [(3, 0), (2, 0), (1, 0)] := by
    apply endpointTrace_child 1 [3, 8, 5] 0 0 [8, 5] [(2, 0), (1, 0)]
    · norm_num [EndpointPivot]
    · norm_num [stepRun_eq, partition3_eq_filters]
    · exact h2
  have h4 : EndpointTrace 2 ([3, 8, 0, 5] : List Int)
      [(4, 2), (3, 0), (2, 0), (1, 0)] := by
    apply endpointTrace_child 2 [3, 8, 0, 5] 2 1 [3, 8, 5]
      [(3, 0), (2, 0), (1, 0)]
    · norm_num [EndpointPivot]
    · norm_num [stepRun_eq, partition3_eq_filters]
    · exact h3
  apply endpointTrace_child 3 [3, -2, 8, 0, 5] 1 2 [3, 8, 0, 5]
    [(4, 2), (3, 0), (2, 0), (1, 0)]
  · norm_num [EndpointPivot]
  · exact congrArg Prod.fst Examples.RandomSelectionEndpoints.negative_minimum_step
  · exact h4

theorem signed_endpoint_probability :
    EndpointTrace 3 ([3, -2, 8, 0, 5] : List Int)
      [(5, 1), (4, 2), (3, 0), (2, 0), (1, 0)] ∧
      run 3 ([3, -2, 8, 0, 5] : List Int)
        (some 5, ([(5, 1), (4, 2), (3, 0), (2, 0), (1, 0)], 67)) =
          (120 : ℝ≥0∞)⁻¹ ∧
      traceLaw 3 ([3, -2, 8, 0, 5] : List Int)
        [(5, 1), (4, 2), (3, 0), (2, 0), (1, 0)] = (120 : ℝ≥0∞)⁻¹ ∧
      scanVolume [(5, 1), (4, 2), (3, 0), (2, 0), (1, 0)] = 15 :=
  ⟨signed_endpoint_trace, Examples.RandomSelectionTrace.negative_path_atom,
    Examples.RandomSelectionTrace.negative_path_trace, rfl⟩

/-- The endpoint witness attains the universal scan upper bound among actual
supported outcomes, for every distinct list and every valid worker rank. -/
theorem distinct_scan_maximum (k : Nat) (xs : List α)
    (hxs : xs.Nodup) (hk : k < xs.length) :
    ∃ r : Outcome α,
      EndpointTrace k xs r.2.1 ∧ r ∈ (run k xs).support ∧
      traceLaw k xs r.2.1 = ((xs.length.factorial : ℝ≥0∞)⁻¹) ∧
      scanVolume r.2.1 = xs.length * (xs.length + 1) / 2 ∧
      ∀ s ∈ (run k xs).support, scanVolume s.2.1 ≤ scanVolume r.2.1 := by
  obtain ⟨r, ht, hr, _, hm, _, _, hw, _, _, _⟩ :=
    exists_endpoint_worst k xs hxs hk
  refine ⟨r, ht, hr, hm, hw, ?_⟩
  intro s hs
  rw [hw]
  exact run_scanVolume_le k xs s hs

theorem unsorted_endpoint_ranks :
    (∃ r : Outcome Int, r ∈ (run 0 [3, 1, 2]).support ∧
      traceLaw 0 ([3, 1, 2] : List Int) r.2.1 = (6 : ℝ≥0∞)⁻¹ ∧
      scanVolume r.2.1 = 6) ∧
    (∃ r : Outcome Int, r ∈ (run 2 [3, 1, 2]).support ∧
      traceLaw 2 ([3, 1, 2] : List Int) r.2.1 = (6 : ℝ≥0∞)⁻¹ ∧
      scanVolume r.2.1 = 6) := by
  constructor
  · obtain ⟨r, _, hr, _, hm, _, _, hw, _, _, _⟩ :=
      exists_endpoint_worst 0 ([3, 1, 2] : List Int) (by decide) (by decide)
    exact ⟨r, hr, by simpa [Nat.factorial] using hm, by simpa using hw⟩
  · obtain ⟨r, _, hr, _, hm, _, _, hw, _, _, _⟩ :=
      exists_endpoint_worst 2 ([3, 1, 2] : List Int) (by decide) (by decide)
    exact ⟨r, hr, by simpa [Nat.factorial] using hm, by simpa using hw⟩

theorem range_four_exact :
    EndpointTrace 2 (List.range 4) [(4, 0), (3, 0), (2, 1), (1, 0)] ∧
      run 2 (List.range 4)
        (some 2, ([(4, 0), (3, 0), (2, 1), (1, 0)], 48)) = (24 : ℝ≥0∞)⁻¹ ∧
      traceLaw 2 (List.range 4) [(4, 0), (3, 0), (2, 1), (1, 0)] =
        (24 : ℝ≥0∞)⁻¹ ∧ scanVolume [(4, 0), (3, 0), (2, 1), (1, 0)] = 10 := by
  have hs2 : stepRun 0 ([2, 3] : List Nat) 1 = (Sum.inl (0, [2]), 11) := by
    norm_num [stepRun_eq, partition3_eq_filters]
  have hs3 : stepRun 1 ([1, 2, 3] : List Nat) 0 = (Sum.inl (0, [2, 3]), 13) := by
    norm_num [stepRun_eq, partition3_eq_filters]
  have hs4 : stepRun 2 ([0, 1, 2, 3] : List Nat) 0 = (Sum.inl (1, [1, 2, 3]), 15) := by
    norm_num [stepRun_eq, partition3_eq_filters]
  have ht2 : EndpointTrace 0 ([2, 3] : List Nat) [(2, 1), (1, 0)] :=
    endpointTrace_child 0 [2, 3] 1 0 [2] [(1, 0)]
      (by norm_num [EndpointPivot]) (congrArg Prod.fst hs2) (endpointTrace_singleton 2)
  have ht3 : EndpointTrace 1 ([1, 2, 3] : List Nat) [(3, 0), (2, 1), (1, 0)] :=
    endpointTrace_child 1 [1, 2, 3] 0 0 [2, 3] [(2, 1), (1, 0)]
      (by norm_num [EndpointPivot]) (congrArg Prod.fst hs3) ht2
  have ht4 : EndpointTrace 2 ([0, 1, 2, 3] : List Nat)
      [(4, 0), (3, 0), (2, 1), (1, 0)] :=
    endpointTrace_child 2 [0, 1, 2, 3] 0 1 [1, 2, 3] [(3, 0), (2, 1), (1, 0)]
      (by norm_num [EndpointPivot]) (congrArg Prod.fst hs4) ht3
  have ha2 : run 0 ([2, 3] : List Nat)
      (some 2, ([(2, 1), (1, 0)], 20)) = (2 : ℝ≥0∞)⁻¹ := by
    simpa [hs2, prepend, run_singleton_atom] using
      run_child_atom 0 (2 : Nat) [3] 1 0 [2] (congrArg Prod.fst hs2)
        (some 2, ([(1, 0)], 9))
  have ha3 : run 1 ([1, 2, 3] : List Nat)
      (some 2, ([(3, 0), (2, 1), (1, 0)], 33)) = (6 : ℝ≥0∞)⁻¹ := by
    calc
      _ = (3 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
        simpa [hs3, prepend, ha2] using
          run_child_atom 1 (1 : Nat) [2, 3] 0 0 [2, 3] (congrArg Prod.fst hs3)
            (some 2, ([(2, 1), (1, 0)], 20))
      _ = (6 : ℝ≥0∞)⁻¹ := inverse_nat_product 3 2
  have ha4 : run 2 ([0, 1, 2, 3] : List Nat)
      (some 2, ([(4, 0), (3, 0), (2, 1), (1, 0)], 48)) = (24 : ℝ≥0∞)⁻¹ := by
    calc
      _ = (4 : ℝ≥0∞)⁻¹ * (6 : ℝ≥0∞)⁻¹ := by
        simpa [hs4, prepend, ha3] using
          run_child_atom 2 (0 : Nat) [1, 2, 3] 0 1 [1, 2, 3] (congrArg Prod.fst hs4)
            (some 2, ([(3, 0), (2, 1), (1, 0)], 33))
      _ = (24 : ℝ≥0∞)⁻¹ := inverse_nat_product 4 6
  have hr : (some 2, ([(4, 0), (3, 0), (2, 1), (1, 0)], 48)) ∈
      (run 2 ([0, 1, 2, 3] : List Nat)).support := by
    rw [PMF.mem_support_iff, ha4]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top 24)
  exact ⟨ht4, ha4, (traceLaw_atom 2 [0, 1, 2, 3] _ hr).trans ha4, rfl⟩

theorem range_four_bounds :
    ∃ r : Outcome Nat, EndpointTrace 2 (List.range 4) r.2.1 ∧
      r ∈ (run 2 (List.range 4)).support ∧
      traceLaw 2 (List.range 4) r.2.1 = (24 : ℝ≥0∞)⁻¹ ∧
      scanVolume r.2.1 = 10 ∧ 16 ≤ 2 * r.2.2 ∧ r.2.2 ≤ 176 := by
  obtain ⟨r, ht, hr, _, hm, _, hw, _, _, hl, hu⟩ :=
    range_endpoint_worst 4 2 (by decide) (by decide)
  exact ⟨r, ht, hr, by simpa [Nat.factorial] using hm, hw, hl, hu⟩

/-- Every chosen large range retains all valid ranks, and the positive trace
event carries an actual outcome with the stated unbounded quadratic source cost. -/
theorem large_family_every_rank (B : Nat) :
    ∃ n : Nat, B < n ∧ ∀ k : Nat, k < n →
      ∃ trace : Trace, trace ∈ (traceLaw k (List.range n)).support ∧
        traceLaw k (List.range n) trace = ((n.factorial : ℝ≥0∞)⁻¹) ∧
        ∃ r ∈ (run k (List.range n)).support, r.2.1 = trace ∧
          B < r.2.2 ∧ n * n ≤ 2 * r.2.2 ∧ r.2.2 ≤ 11 * (n * n) := by
  obtain ⟨n, hn, hall⟩ := unbounded_endpoint_source_family B
  refine ⟨n, hn, ?_⟩
  intro k hk
  obtain ⟨r, _, hr, hm, _, hb, hl, hu⟩ := hall k hk
  exact ⟨r.2.1, (traceLaw_support k (List.range n) r.2.1).mpr ⟨r, hr, rfl⟩,
    hm, r, hr, rfl, hb, hl, hu⟩

theorem empty_endpoint_boundary (k : Nat) (trace : Trace) :
    ¬ EndpointTrace k ([] : List α) trace ∧ traceLaw k ([] : List α) [] = 1 :=
  ⟨endpointTrace_empty_input k trace, Examples.RandomSelectionTrace.empty_trace_atom k⟩

theorem invalid_endpoint_boundary (k : Nat) (xs : List α) (trace : Trace)
    (hbad : xs.length ≤ k) : ¬ EndpointTrace k xs trace := by
  intro ht
  have hv := endpointTrace_valid k xs trace ht
  omega

theorem invalid_singleton_endpoint_boundary :
    ¬ EndpointTrace 1 ([7] : List Nat) [(1, 0)] ∧
      traceLaw 1 ([7] : List Nat) [(1, 0)] = 1 :=
  ⟨invalid_endpoint_boundary 1 [7] [(1, 0)] (by decide),
    Examples.RandomSelectionTrace.invalid_singleton_trace_atom⟩

theorem equal_block_endpoint_boundary :
    ¬ EndpointTrace 1 ([4, 4, 4] : List Nat) [(3, 0)] ∧
      traceLaw 1 ([4, 4, 4] : List Nat) [(3, 0)] = (3 : ℝ≥0∞)⁻¹ ∧
      scanVolume [(3, 0)] = 3 := by
  refine ⟨?_, Examples.RandomSelectionTrace.duplicate_trace_atom, rfl⟩
  intro ht
  obtain ⟨hi, _, _, ht⟩ := ht
  have hs : (stepRun 1 ([4, 4, 4] : List Nat) ⟨0, hi⟩).1 = Sum.inr 4 :=
    congrArg Prod.fst Examples.RandomSelectionEndpoints.duplicate_countercase.2
  rw [hs] at ht
  have hlen := ht.1
  norm_num at hlen

/-- Mixed duplicates can satisfy the structural path, so distinctness must
remain explicit in the triangular/factorial theorem. This path has W4, T23,
and probability1/3, while the distinct size-three values are W6 and1/6. -/
theorem mixed_duplicate_endpoint_boundary :
    EndpointTrace 2 ([1, 1, 2] : List Nat) [(3, 0), (1, 0)] ∧
      ¬ ([1, 1, 2] : List Nat).Nodup ∧
      run 2 ([1, 1, 2] : List Nat) (some 2, ([(3, 0), (1, 0)], 23)) =
        (3 : ℝ≥0∞)⁻¹ ∧
      traceLaw 2 ([1, 1, 2] : List Nat) [(3, 0), (1, 0)] = (3 : ℝ≥0∞)⁻¹ ∧
      scanVolume [(3, 0), (1, 0)] = 4 ∧ scanVolume [(3, 0), (1, 0)] ≠ 6 := by
  have hs : stepRun 2 ([1, 1, 2] : List Nat) 0 = (Sum.inl (0, [2]), 14) := by
    norm_num [stepRun_eq, partition3_eq_filters]
  have ht : EndpointTrace 2 ([1, 1, 2] : List Nat) [(3, 0), (1, 0)] :=
    endpointTrace_child 2 [1, 1, 2] 0 0 [2] [(1, 0)]
      (by norm_num [EndpointPivot]) (congrArg Prod.fst hs) (endpointTrace_singleton 2)
  have ha : run 2 ([1, 1, 2] : List Nat) (some 2, ([(3, 0), (1, 0)], 23)) =
      (3 : ℝ≥0∞)⁻¹ := by
    simpa [hs, prepend, run_singleton_atom] using
      run_child_atom 2 (1 : Nat) [1, 2] 0 0 [2] (congrArg Prod.fst hs)
        (some 2, ([(1, 0)], 9))
  have hr : (some 2, ([(3, 0), (1, 0)], 23)) ∈
      (run 2 ([1, 1, 2] : List Nat)).support := by
    rw [PMF.mem_support_iff, ha]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top 3)
  exact ⟨ht, by decide, ha, (traceLaw_atom 2 [1, 1, 2] _ hr).trans ha, rfl, by decide⟩

end Ordered
end
end Examples.RandomSelectionWorst
