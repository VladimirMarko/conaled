import Applications.Resources.RandomSelectionEqual
import Examples.RandomSelectionTail

/-! Independently calculated duplicate and boundary cases. The general law
keeps every occurrence draw: three equal entries have source costs 15,16,17
at a valid rank, and 17,18,19 at an invalid worker rank. Their scan volume is
always three. These are actual source observations, not assigned complexities.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomSelectionEqual
open Resources.RandomSelection
open scoped ENNReal
universe u
variable {α : Type u} [LinearOrder α]

noncomputable section

theorem empty_boundary (k : Nat) (x : α) :
    run k (List.replicate 0 x) = PMF.pure (none, ([], 2)) ∧
      scanLaw k (List.replicate 0 x) = PMF.pure 0 ∧
      scanMean k (List.replicate 0 x) = 0 := by
  refine ⟨run_nil k, scanLaw_replicate 0 k x, ?_⟩
  simpa only [Nat.cast_zero] using scanMean_replicate 0 k x

theorem singleton_boundary (x : α) :
    run 0 (List.replicate 1 x) = PMF.pure (some x, ([(1, 0)], 9)) ∧
      run 1 (List.replicate 1 x) = PMF.pure (none, ([(1, 0)], 11)) := by
  constructor
  · simpa [Resources.RandomQuickSort.uniformIndex_zero, PMF.pure_map] using
      run_replicate_valid 0 0 x (by decide)
  · simpa [Resources.RandomQuickSort.uniformIndex_zero, PMF.pure_map] using
      run_replicate_invalid 0 1 x (by decide)

theorem pair_both_valid_ranks (k : Nat) (hk : k < 2) (x : α) :
    run k [x, x] = PMF.map
      (fun i : Fin 2 => (some x, ([(2, i.val)], 12 + i.val)))
      (Resources.RandomQuickSort.uniformIndex 1) := by
  have h := run_replicate_valid 1 k x hk
  have hc : ∀ i : Nat, 3 * (1 + 1) + i + 6 = 12 + i := by
    intro i
    omega
  simpa only [List.replicate_succ, List.replicate_zero, hc] using h

theorem three_equal_first_atom :
    run 2 ([-3, -3, -3] : List Int) (some (-3), ([(3, 0)], 15)) =
      (3 : ℝ≥0∞)⁻¹ :=
  run_replicate_valid_atom 2 2 (-3 : Int) (by decide) 0

theorem three_equal_last_atom :
    run 2 ([-3, -3, -3] : List Int) (some (-3), ([(3, 2)], 17)) =
      (3 : ℝ≥0∞)⁻¹ :=
  run_replicate_valid_atom 2 2 (-3 : Int) (by decide) 2

theorem three_equal_invalid_atom :
    run 3 ([-3, -3, -3] : List Int) (none, ([(3, 2)], 19)) =
      (3 : ℝ≥0∞)⁻¹ :=
  run_replicate_invalid_atom 2 3 (-3 : Int) (by decide) 2

theorem five_equal_scan (k : Nat) :
    scanLaw k ([4, 4, 4, 4, 4] : List Nat) = PMF.pure 5 ∧
      scanExpectation k ([4, 4, 4, 4, 4] : List Nat) = 5 ∧
      scanMean k ([4, 4, 4, 4, 4] : List Nat) = 5 :=
  ⟨scanLaw_replicate 5 k 4, scanExpectation_replicate 5 k 4, scanMean_replicate 5 k 4⟩

theorem five_equal_source_law :
    sourceLaw 2 ([4, 4, 4, 4, 4] : List Nat) =
      PMF.map (fun i : Fin 5 => 21 + i.val)
        (Resources.RandomQuickSort.uniformIndex 4) := by
  have hc : ∀ i : Nat, 3 * (4 + 1) + i + 6 = 21 + i := by
    intro i
    omega
  simpa only [List.replicate_succ, List.replicate_zero, hc] using
    sourceLaw_replicate_valid 4 2 (4 : Nat) (by decide)

theorem general_equal_execution (time k : Nat) (xs : List α) (x : α)
    (hall : ∀ a ∈ xs, a = x) (hk : k < xs.length) (result : Outcome α)
    (hr : result ∈ (run k xs).support) :
    result.1 = some x ∧ result.2.1.length = 1 ∧ scanVolume result.2.1 = xs.length ∧
      result.2.2 ≤ 4 * xs.length + 5 ∧ activeSize (time + 1) result.2.1 = 0 ∧
      residualWork (time + 1) result.2.1 = 0 := by
  obtain ⟨hv, hc, hw, _, ht⟩ := run_all_equal_summary k xs x hall hk result hr
  exact ⟨hv, hc, hw, ht, run_all_equal_absorbed time k xs x hall hk result hr⟩

theorem equal_family_below_quadratic (n k : Nat) (hn : 2 ≤ n)
    (result : Outcome Nat) (hr : result ∈ (run k (List.replicate n 4)).support) :
    scanVolume result.2.1 = n ∧ scanVolume result.2.1 < n * (n + 1) / 2 :=
  ⟨run_replicate_scan n k 4 result hr, run_replicate_scan_lt_quadratic n k 4 hn result hr⟩

theorem public_zero_still_fails (n : Nat) (x : α) :
    select 0 (List.replicate n x) = PMF.pure (none, ([], 0)) := by
  simp [select]

end
end Examples.RandomSelectionEqual
