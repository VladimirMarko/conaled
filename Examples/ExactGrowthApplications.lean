import SquareKit.ExactGrowthBounds
import Examples.ExactGrowth
import Examples.DiscreteEstimates
import Examples.PermutationSearch

/-!
# Exact positional-search populations and weighted prefix scans

The search counter counts positional occurrences for an arbitrary stored prefix.
Its exact logarithm uses the accepted partial arithmetic interpretation. Repeated
entries need no distinctness or decidable-equality premise. These are population
magnitude statements, not execution-time or decision-tree bounds.

The existing real-valued scanner supplies every positive weighted logarithmic
prefix. Each output is connected to the finite value and rational section of the
corresponding arithmetic term, including the initial and empty zero cases.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExactGrowthApplications

open SquareKit.NonnegativeArithmetic
open scoped NNReal

universe u
variable {α : Type u}

noncomputable section

/-- The actual depth-complete positional counter is positive even on empty input. -/
theorem permutation_count_pos (remaining chosen : List α) :
    0 < FiniteSearch.count PermutationSearch.next remaining.length (chosen, remaining) := by
  rw [PermutationSearch.count_factorial]
  exact Nat.factorial_pos _

/-- The finite payload is the actual real logarithm of the actual counter. -/
theorem permutation_count_logarithm_value (remaining chosen : List α) :
    value (logarithm
      (FiniteSearch.count PermutationSearch.next remaining.length (chosen, remaining))) =
      ((Real.toNNReal (Real.logb 2
        (FiniteSearch.count PermutationSearch.next remaining.length
          (chosen, remaining) : ℝ))) : Value) := by
  rw [value_logarithm, logarithmValue,
    ite_eq_right (Nat.ne_of_gt (permutation_count_pos remaining chosen))]

/-- Every rational query observes that same exact logarithm; negative queries
remain included when below it. -/
theorem permutation_count_logarithm_section (remaining chosen : List α) (q : ℚ) :
    q ∈ sectionOf (logarithm
      (FiniteSearch.count PermutationSearch.next remaining.length (chosen, remaining))) ↔
      (q : ℝ) ≤ Real.logb 2
        (FiniteSearch.count PermutationSearch.next remaining.length (chosen, remaining) : ℝ) := by
  let population := FiniteSearch.count PermutationSearch.next remaining.length (chosen, remaining)
  have hp : 0 < population := permutation_count_pos remaining chosen
  have hlog : 0 ≤ Real.logb 2 (population : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 1 ≤ population by omega))
  have hrel : Rel (logApprox population)
      (Real.toNNReal (Real.logb 2 (population : ℝ)) : Value) := by
    simpa only [logarithmValue, ite_eq_right (Nat.ne_of_gt hp)] using rel_logarithm population
  simpa only [sectionOf, raw_logarithm, Real.coe_toNNReal _ hlog] using hrel.2 q

/-- The actual population's exact section retains the finite power criterion. -/
theorem permutation_count_logarithm_fraction (remaining chosen : List α)
    (p q : ℕ) (hq : 0 < q) :
    (p : ℚ) / (q : ℚ) ∈ sectionOf (logarithm
      (FiniteSearch.count PermutationSearch.next remaining.length (chosen, remaining))) ↔
      2 ^ p ≤ (FiniteSearch.count PermutationSearch.next remaining.length
        (chosen, remaining)) ^ q := by
  exact logarithm_section_fraction_iff _ p q
    (by have h := permutation_count_pos remaining chosen; omega) hq

/-- Eight equal values still supply 40320 positional occurrences, without
constructing the output list. -/
theorem permutation_repeated_eight_count (x : α) (chosen : List α) :
    FiniteSearch.count PermutationSearch.next 8 (chosen, List.replicate 8 x) = 40320 := by
  calc
    _ = Nat.factorial 8 := by
      simpa only [List.length_replicate] using
        PermutationSearch.count_factorial (List.replicate 8 x) chosen
    _ = 40320 := by decide

/-- The exact power thresholds accept fifteen and reject sixteen. -/
theorem permutation_repeated_eight_sections (x : α) (chosen : List α) :
    (15 : ℚ) ∈ sectionOf (logarithm
      (FiniteSearch.count PermutationSearch.next 8 (chosen, List.replicate 8 x))) ∧
      (16 : ℚ) ∉ sectionOf (logarithm
        (FiniteSearch.count PermutationSearch.next 8 (chosen, List.replicate 8 x))) := by
  rw [permutation_repeated_eight_count x chosen]
  constructor
  · simpa only [Nat.cast_ofNat, Nat.cast_one, div_one] using
      (logarithm_section_fraction_iff 40320 15 1 (by decide) (by decide)).mpr (by decide)
  · intro h
    have hbad := (logarithm_section_fraction_iff 40320 16 1 (by decide) (by decide)).mp
      (by simpa only [Nat.cast_ofNat, Nat.cast_one, div_one] using h)
    exact (by decide : ¬ ((2 : ℕ) ^ 16 ≤ 40320 ^ 1)) hbad

/-- Strict integer power comparisons distinguish the exact logarithm from its
floor fifteen. No numerical real evaluation is used. -/
theorem permutation_repeated_eight_log_bounds (x : α) (chosen : List α) :
    15 < Real.logb 2
      (FiniteSearch.count PermutationSearch.next 8 (chosen, List.replicate 8 x) : ℝ) ∧
      Real.logb 2
        (FiniteSearch.count PermutationSearch.next 8 (chosen, List.replicate 8 x) : ℝ) < 16 := by
  rw [permutation_repeated_eight_count x chosen]
  have hb : (1 : ℝ) < 2 := by norm_num
  have hlo := Real.logb_lt_logb hb
    (by norm_num : (0 : ℝ) < (2 : ℝ) ^ (15 : ℕ))
    (by norm_num : (2 : ℝ) ^ (15 : ℕ) < 40320)
  have hhi := Real.logb_lt_logb hb (by norm_num : (0 : ℝ) < 40320)
    (by norm_num : (40320 : ℝ) < (2 : ℝ) ^ (16 : ℕ))
  constructor
  · simpa only [Real.logb_pow, Real.logb_self_eq_one hb, Nat.cast_ofNat, mul_one] using hlo
  · simpa only [Real.logb_pow, Real.logb_self_eq_one hb, Nat.cast_ofNat, mul_one] using hhi

theorem permutation_repeated_eight_log_ne_floor (x : α) (chosen : List α) :
    Real.logb 2
      (FiniteSearch.count PermutationSearch.next 8 (chosen, List.replicate 8 x) : ℝ) ≠ 15 :=
  ne_of_gt (permutation_repeated_eight_log_bounds x chosen).1

/-- The current prefix itself is the one depth-zero occurrence. -/
theorem permutation_empty_count (chosen : List α) :
    FiniteSearch.count PermutationSearch.next 0 (chosen, []) = 1 :=
  PermutationSearch.count_factorial ([] : List α) chosen

theorem permutation_empty_log_value (chosen : List α) :
    value (logarithm (FiniteSearch.count PermutationSearch.next 0 (chosen, []))) =
      ((0 : ℝ≥0) : Value) := by
  rw [permutation_empty_count chosen]
  norm_num [value_logarithm, logarithmValue]

/-- Valid exact zero admits all and only nonpositive rational queries. -/
theorem permutation_empty_log_section (chosen : List α) (q : ℚ) :
    q ∈ sectionOf (logarithm
      (FiniteSearch.count PermutationSearch.next 0 (chosen, []))) ↔ q ≤ 0 := by
  rw [permutation_empty_count chosen]
  simpa only [pow_zero, Nat.cast_zero] using
    section_of_exact_bounds (bounded_log_power 0) q

/-- Extra depth on an empty remainder counts zero, so its log remains invalid. -/
theorem permutation_empty_extra_log_invalid (chosen : List α) (extra : ℕ) :
    value (logarithm
      (FiniteSearch.count PermutationSearch.next (extra + 1) (chosen, []))) = ⊥ := by
  have hc := PermutationSearch.exhausted_count ([] : List α) chosen extra
  simp only [List.length_nil, zero_add] at hc
  rw [hc]
  simp [value_logarithm, logarithmValue]

theorem permutation_empty_extra_log_section (chosen : List α) (extra : ℕ) :
    sectionOf (logarithm
      (FiniteSearch.count PermutationSearch.next (extra + 1) (chosen, []))) = ∅ :=
  (value_eq_bot_iff_sectionOf_empty _).mp (permutation_empty_extra_log_invalid chosen extra)

end
end Examples.ExactGrowthApplications

/-! Exact finite population comparisons and actual weighted prefix scans. -/

namespace Examples.ExactGrowthApplications

open SquareKit.NonnegativeArithmetic
open Applications.Parallel Examples.ExactGrowth
open scoped NNReal BigOperators

universe u
variable {α : Type u}

noncomputable section

/-- The actual population inherits both finite exact-log coefficients. -/
theorem permutation_count_exact_log_coefficients (remaining chosen : List α)
    (hn : 4 ≤ remaining.length) :
    Real.logb 2
        (FiniteSearch.count PermutationSearch.next remaining.length (chosen, remaining) : ℝ) ≤
      4 * ((remaining.length : ℝ) * Real.logb 2 remaining.length) ∧
      (remaining.length : ℝ) * Real.logb 2 remaining.length ≤
        12 * Real.logb 2
          (FiniteSearch.count PermutationSearch.next remaining.length (chosen, remaining) : ℝ) := by
  simpa only [PermutationSearch.count_factorial] using
    SquareKit.ExactGrowthBounds.factorial_logb_coefficients remaining.length hn

/-- The same finite comparisons hold in the actual expression's closed-section
order, through the family finite-value bridge. -/
theorem permutation_count_log_section_bounds (remaining chosen : List α)
    (hn : 4 ≤ remaining.length) :
    (sectionOf (logarithm
        (FiniteSearch.count PermutationSearch.next remaining.length (chosen, remaining))) ⊆
      sectionOf (scale 4 (nLog remaining.length))) ∧
      (sectionOf (nLog remaining.length) ⊆ sectionOf (scale 12 (logarithm
        (FiniteSearch.count PermutationSearch.next remaining.length (chosen, remaining))))) := by
  simpa only [PermutationSearch.count_factorial] using
    factorial_log_section_bounds remaining.length hn

/-- Every output of any certified scanner is the positive weighted exact sum
for that prefix; the premise describes only the actual flattened input. -/
theorem inclusive_weighted_prefixes {s : Shape}
    (p : Scanner s (Multiplicative ℝ)) (x : s.Data (Multiplicative ℝ)) (n : ℕ)
    (hx : s.flatten x = (List.range n).map
      (fun j => Multiplicative.ofAdd (((j + 1 : ℕ) : ℝ) * Real.logb 2 (j + 1)))) :
    (p.inclusive x).map Multiplicative.toAdd =
      (List.range (n + 1)).map
        (fun k => ∑ i ∈ Finset.Ico (1 : ℕ) (k + 1), (i : ℝ) * Real.logb 2 i) := by
  calc
    _ = (List.range (n + 1)).map
        (fun k => ∑ j ∈ Finset.range k, ((j + 1 : ℕ) : ℝ) * Real.logb 2 (j + 1)) :=
      DiscreteEstimates.inclusive_finite_prefix_sums p x
        (fun j => ((j + 1 : ℕ) : ℝ) * Real.logb 2 (j + 1)) n hx
    _ = _ := by
      apply List.map_congr_left
      intro k _hk
      exact weighted_log_range_eq_Ico k

/-- The final total is the same positive weighted sum, not a separately run sum. -/
theorem inclusive_weighted_total {s : Shape}
    (p : Scanner s (Multiplicative ℝ)) (x : s.Data (Multiplicative ℝ)) (n : ℕ)
    (hx : s.flatten x = (List.range n).map
      (fun j => Multiplicative.ofAdd (((j + 1 : ℕ) : ℝ) * Real.logb 2 (j + 1)))) :
    Multiplicative.toAdd (p.run x).2 =
      ∑ k ∈ Finset.Ico (1 : ℕ) (n + 1), (k : ℝ) * Real.logb 2 k := by
  exact (DiscreteEstimates.inclusive_finite_total p x
    (fun j => ((j + 1 : ℕ) : ℝ) * Real.logb 2 (j + 1)) n hx).trans
      (weighted_log_range_eq_Ico n)

/-- Each actual indexed output is the finite value of the corresponding native
weighted term, with the same closed-section meaning for every rational query. -/
theorem inclusive_weighted_prefix_value {s : Shape}
    (p : Scanner s (Multiplicative ℝ)) (x : s.Data (Multiplicative ℝ)) (n : ℕ)
    (hx : s.flatten x = (List.range n).map
      (fun j => Multiplicative.ofAdd (((j + 1 : ℕ) : ℝ) * Real.logb 2 (j + 1))))
    (k : ℕ) (hk : k ≤ n) :
    ∃ v : ℝ≥0, value (weightedLogExpr k) = (v : Value) ∧
      ((p.inclusive x).map Multiplicative.toAdd)[k]? = some (v : ℝ) ∧
      ∀ q : ℚ, q ∈ sectionOf (weightedLogExpr k) ↔ (q : ℝ) ≤ (v : ℝ) := by
  obtain ⟨v, hv, hreal⟩ := value_weightedLogExpr k
  refine ⟨v, hv, ?_, ?_⟩
  · rw [inclusive_weighted_prefixes p x n hx]
    simp only [List.getElem?_map, List.getElem?_range (Nat.lt_succ_iff.mpr hk),
      Option.map_some]
    rw [hreal]
  · intro q
    rw [section_weightedLogExpr, hreal]

/-- The actual total also has the same finite native payload. -/
theorem inclusive_weighted_total_value {s : Shape}
    (p : Scanner s (Multiplicative ℝ)) (x : s.Data (Multiplicative ℝ)) (n : ℕ)
    (hx : s.flatten x = (List.range n).map
      (fun j => Multiplicative.ofAdd (((j + 1 : ℕ) : ℝ) * Real.logb 2 (j + 1)))) :
    ∃ v : ℝ≥0, value (weightedLogExpr n) = (v : Value) ∧
      Multiplicative.toAdd (p.run x).2 = (v : ℝ) := by
  obtain ⟨v, hv, hreal⟩ := value_weightedLogExpr n
  refine ⟨v, hv, ?_⟩
  rw [inclusive_weighted_total p x n hx, hreal]

/-- Four positive-index weights represented for the actual composition of two
pair scanners. The first zero is one times log one, not strict zero times log zero. -/
def weightedFourInput : (ScanPlan.comp .pair .pair).shape.Data (Multiplicative ℝ) :=
  ((Multiplicative.ofAdd (0 : ℝ), Multiplicative.ofAdd (2 : ℝ)),
    (Multiplicative.ofAdd (3 * Real.logb 2 3), Multiplicative.ofAdd (8 : ℝ)))

theorem weightedFourInput_flatten :
    (ScanPlan.comp .pair .pair).shape.flatten weightedFourInput =
      (List.range 4).map
        (fun j => Multiplicative.ofAdd (((j + 1 : ℕ) : ℝ) * Real.logb 2 (j + 1))) := by
  have htwo : Real.logb 2 (2 : ℝ) = 1 :=
    Real.logb_self_eq_one (by norm_num)
  have hfour : Real.logb 2 (4 : ℝ) = 2 := by
    have h := Real.logb_pow 2 2 2
    norm_num [htwo] at h
    exact h
  -- Match the actual wrapped input, including its real successor inside logb.
  change
    [Multiplicative.ofAdd (0 : ℝ), Multiplicative.ofAdd (2 : ℝ),
      Multiplicative.ofAdd (3 * Real.logb 2 3), Multiplicative.ofAdd (8 : ℝ)] =
    [Multiplicative.ofAdd (((0 + 1 : ℕ) : ℝ) * Real.logb 2 (((0 : ℕ) : ℝ) + 1)),
      Multiplicative.ofAdd (((1 + 1 : ℕ) : ℝ) * Real.logb 2 (((1 : ℕ) : ℝ) + 1)),
      Multiplicative.ofAdd (((2 + 1 : ℕ) : ℝ) * Real.logb 2 (((2 : ℕ) : ℝ) + 1)),
      Multiplicative.ofAdd (((3 + 1 : ℕ) : ℝ) * Real.logb 2 (((3 : ℕ) : ℝ) + 1))]
  norm_num [htwo, hfour]

/-- Actual composed execution retains all five independently expected prefixes. -/
theorem weighted_four_prefixes :
    ((ScanPlan.comp .pair .pair).scanner.inclusive weightedFourInput).map
      Multiplicative.toAdd =
        [0, 0, 2, 2 + 3 * Real.logb 2 3, 10 + 3 * Real.logb 2 3] := by
  rw [Scanner.inclusive_correct]
  change ([0, 2, 3 * Real.logb 2 3, 8] : List ℝ).scanl (· + ·) 0 = _
  have hlast : 2 + 3 * Real.logb 2 3 + 8 = 10 + 3 * Real.logb 2 3 := by ring
  simp only [List.scanl_cons, List.scanl_nil, zero_add, hlast]

/-- The general finite-prefix theorem identifies this native scan result with
the actual positive sum used in the weighted term's semantic theorem. -/
theorem weighted_four_sum :
    (∑ k ∈ Finset.Ico (1 : ℕ) (4 + 1), (k : ℝ) * Real.logb 2 k) =
      10 + 3 * Real.logb 2 3 := by
  have hs := inclusive_weighted_prefixes
    (ScanPlan.comp .pair .pair).scanner weightedFourInput 4 weightedFourInput_flatten
  have h := congrArg (fun xs : List ℝ => xs[4]?) (hs.symm.trans weighted_four_prefixes)
  change some (∑ k ∈ Finset.Ico (1 : ℕ) (4 + 1), (k : ℝ) * Real.logb 2 k) =
    some (10 + 3 * Real.logb 2 3) at h
  exact Option.some.inj h

/-- The finite value is supplied by the family theorem, not assumed from the
scanner output description. -/
theorem weighted_four_value :
    ∃ v : ℝ≥0, value (weightedLogExpr 4) = (v : Value) ∧
      (v : ℝ) = 10 + 3 * Real.logb 2 3 := by
  obtain ⟨v, hv, hreal⟩ := value_weightedLogExpr 4
  exact ⟨v, hv, hreal.trans weighted_four_sum⟩

/-- The actual raw lower member thirteen and upper bound twenty-six are
different observations from the exact real total. -/
theorem weighted_four_raw_bounds : Bounded (weightedLogExpr 4) 13 26 := by
  have hsum : (∑ k ∈ Finset.Ico (1 : ℕ) (4 + 1), k * Nat.log2 k : ℕ) = 13 := by decide
  have h := weighted_expression_bounds 4
  norm_num [hsum] at h
  exact h

theorem weighted_four_raw_thirteen : (13 : ℚ) ∈ raw (weightedLogExpr 4) :=
  weighted_four_raw_bounds.1

/-- Integer comparisons 16 < 27 < 32 give the strict exact bracket; no floating-point evaluation
or floor-log substitution enters this proof. -/
theorem weighted_four_sum_bounds :
    14 < (∑ k ∈ Finset.Ico (1 : ℕ) (4 + 1), (k : ℝ) * Real.logb 2 k) ∧
      (∑ k ∈ Finset.Ico (1 : ℕ) (4 + 1), (k : ℝ) * Real.logb 2 k) < 15 := by
  rw [weighted_four_sum]
  have hb : (1 : ℝ) < 2 := by norm_num
  have hlo := Real.logb_lt_logb hb
    (by norm_num : (0 : ℝ) < (2 : ℝ) ^ (4 : ℕ))
    (by norm_num : (2 : ℝ) ^ (4 : ℕ) < (3 : ℝ) ^ (3 : ℕ))
  have hhi := Real.logb_lt_logb hb
    (by norm_num : (0 : ℝ) < (3 : ℝ) ^ (3 : ℕ))
    (by norm_num : (3 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (5 : ℕ))
  have hlow : (4 : ℝ) < 3 * Real.logb 2 3 := by
    simpa only [Real.logb_pow, Real.logb_self_eq_one hb, Nat.cast_ofNat, mul_one] using hlo
  have hhigh : 3 * Real.logb 2 3 < (5 : ℝ) := by
    simpa only [Real.logb_pow, Real.logb_self_eq_one hb, Nat.cast_ofNat, mul_one] using hhi
  constructor <;> linarith

/-- The actual scanner's total has the same strict bracket. -/
theorem weighted_four_total_bounds :
    14 < Multiplicative.toAdd
        ((ScanPlan.comp .pair .pair).scanner.run weightedFourInput).2 ∧
      Multiplicative.toAdd
        ((ScanPlan.comp .pair .pair).scanner.run weightedFourInput).2 < 15 := by
  rw [inclusive_weighted_total _ _ 4 weightedFourInput_flatten]
  exact weighted_four_sum_bounds

/-- The term connected to that exact total accepts 14 and rejects 15. -/
theorem weighted_four_sections :
    (14 : ℚ) ∈ sectionOf (weightedLogExpr 4) ∧
      (15 : ℚ) ∉ sectionOf (weightedLogExpr 4) := by
  constructor
  · apply (section_weightedLogExpr 4 14).mpr
    simpa only [Rat.cast_ofNat] using weighted_four_sum_bounds.1.le
  · intro h
    have hle := (section_weightedLogExpr 4 15).mp h
    norm_num only [Rat.cast_ofNat] at hle
    linarith [weighted_four_sum_bounds.2]

theorem weighted_four_total_ne_discrete :
    Multiplicative.toAdd
      ((ScanPlan.comp .pair .pair).scanner.run weightedFourInput).2 ≠ 13 := by
  have h := weighted_four_total_bounds.1
  linarith

/-- The empty actual plan still returns its initial exact zero. -/
theorem weighted_empty_prefixes :
    ((ScanPlan.empty.scanner : Scanner .empty (Multiplicative ℝ)).inclusive PUnit.unit).map
      Multiplicative.toAdd = [0] := by
  calc
    _ = (List.range (0 + 1)).map
        (fun k => ∑ i ∈ Finset.Ico (1 : ℕ) (k + 1), (i : ℝ) * Real.logb 2 i) :=
      inclusive_weighted_prefixes _ _ 0 (by rfl)
    _ = [0] := by
      change [∑ i ∈ Finset.Ico (1 : ℕ) (0 + 1), (i : ℝ) * Real.logb 2 i] = [0]
      norm_num

theorem weighted_empty_value_sections :
    value (weightedLogExpr 0) = ((0 : ℝ≥0) : Value) ∧
      ∀ q : ℚ, q ∈ sectionOf (weightedLogExpr 0) ↔ q ≤ 0 := by
  rw [weightedLogExpr_zero]
  constructor
  · simpa only [value_rational, Nat.cast_zero] using rationalValue_natCast 0
  · intro q
    exact rational_section_iff 0 q (by norm_num)

end
end Examples.ExactGrowthApplications
