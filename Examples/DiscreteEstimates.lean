import Mathlib.Analysis.Asymptotics.Theta
import Examples.PermutationSearch
import SquareKit.HarmonicBounds
import SquareKit.LogarithmicSums
import Applications.Parallel.InclusiveScan
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import SquareKit.DiscreteScales
import Applications.Resources.Growth
import Applications.Resources.RandomAccess.Families
import Mathlib.Tactic.NormNum

/-!
# Discrete estimates through existing algorithms

Natural comparisons retain explicit source thresholds. The random-access
clients measure the existing branch and loop charges and refine the actual
value projections; represented length, not request index, controls the bounds.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.DiscreteEstimates
open Filter Asymptotics RandomAccess Resources.RandomAccessCosts
open SquareKit.DiscreteScales
universe u
variable {α : Type u}

/-- Explicit finite form of the source coefficient-one comparison. -/
theorem n_log2_le_n_sqrt {n : ℕ} (hn : 16 ≤ n) :
    n * Nat.log2 n ≤ n * Nat.sqrt n :=
  Nat.mul_le_mul_left n (log2_le_sqrt hn)

/-- The source natural growth witness is coefficient one from sixteen. -/
theorem n_log2_isBigO_n_sqrt :
    (fun n : ℕ => ((n * Nat.log2 n : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => ((n * Nat.sqrt n : ℕ) : ℝ)) := by
  apply Resources.isBigO_of_nat_bound _ _ 1 16
  intro n hn
  simpa using n_log2_le_n_sqrt hn

/-- The native lower power bracket gives coefficient one from index one. -/
theorem two_pow_log2_isBigO_linear :
    (fun n : ℕ => ((2 ^ Nat.log2 n : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  apply Resources.isBigO_of_nat_bound _ _ 1 1
  intro n hn
  simpa using Nat.log2_self_le (by omega : n ≠ 0)

/-- All-natural cubic comparison, with forward/reverse witnesses three and one. -/
theorem cubic_lower_terms_isTheta :
    (fun n : ℕ => ((n * n * n + n * n + n * Nat.log2 n : ℕ) : ℝ)) =Θ[atTop]
      (fun n : ℕ => ((n * n * n : ℕ) : ℝ)) := by
  apply Asymptotics.IsBigO.antisymm
  · exact Resources.isBigO_of_nat_bound _ _ 3 0
      (fun n _ => (cubic_lower_terms_bounds n).2)
  · apply Resources.isBigO_of_nat_bound _ _ 1 0
    intro n _
    simpa using (cubic_lower_terms_bounds n).1

/-- Lookup retains optional-list semantics and the square-root work upper bound,
including requests beyond the represented list. -/
theorem fetchRARun_sqrt_spec {ds : RAList α} (h : Inv ds)
    (hn : 16 ≤ (fromRA ds).length) (k : ℕ) :
    (fetchRARun k ds).1 = (fromRA ds)[k]? ∧
      (fetchRARun k ds).2 ≤ 2 * Nat.sqrt (fromRA ds).length + 3 := by
  refine ⟨fetchRARun_refinement h k, ?_⟩
  have hl := log2_le_sqrt hn
  have hc := fetchRARun_log_bound h k
  omega

/-- Update refines the same total list-set operation for every index. -/
theorem updateRARun_sqrt_spec {ds : RAList α} (h : Inv ds)
    (hn : 16 ≤ (fromRA ds).length) (k : ℕ) (x : α) :
    fromRA (updateRARun k x ds).1 = (fromRA ds).set k x ∧
      (updateRARun k x ds).2 ≤ 2 * Nat.sqrt (fromRA ds).length + 3 := by
  refine ⟨updateRARun_refinement h k x, ?_⟩
  have hl := log2_le_sqrt hn
  have hc := updateRARun_log_bound h k x
  omega

/-- Bulk work includes the existing loop visit and preserves sequential updates
to each preceding state, rather than applying all edits to the initial list. -/
theorem bulkRun_sqrt_spec {ds : RAList α} (h : Inv ds)
    (hn : 16 ≤ (fromRA ds).length) (us : List (ℕ × α)) :
    fromRA (bulkRun ds us).1 = us.foldl (fun ys p => ys.set p.1 p.2) (fromRA ds) ∧
      (bulkRun ds us).2 ≤ us.length * (2 * Nat.sqrt (fromRA ds).length + 4) := by
  constructor
  · rw [bulkRun_value, bulk_refinement h]
  · apply (bulkRun_log_bound h us).trans
    apply Nat.mul_le_mul_left us.length
    have hl := log2_le_sqrt hn
    omega

/-- A genuine valid rank-four input: lookup returns seven, charges ten, and
the new length-sixteen square-root bound allows eleven. -/
theorem rank_four_fetch :
    (fetchRARun 0 (sparse 4 (perfectTree (7 : ℕ) 4))).1 = some 7 ∧
      (fetchRARun 0 (sparse 4 (perfectTree (7 : ℕ) 4))).2 = 10 ∧
      (fetchRARun 0 (sparse 4 (perfectTree (7 : ℕ) 4))).2 ≤ 11 := by
  have hv : Inv (sparse 4 (perfectTree (7 : ℕ) 4)) :=
    sparse_valid 0 4 (perfectTree_valid 7 4)
  have hn : 16 ≤ (fromRA (sparse 4 (perfectTree (7 : ℕ) 4))).length := by
    simp [sparse_value, perfectTree_values]
  have h := fetchRARun_sqrt_spec hv hn 0
  refine ⟨?_, sparse_fetch_cost 4 (perfectTree_valid 7 4), ?_⟩
  · simpa [sparse_value, perfectTree_values] using h.1
  · norm_num [sparse_value, perfectTree_values, (show Nat.sqrt 16 = 4 from Nat.sqrt_eq 4)] at h
    exact h.2

/-- The repeated index distinguishes sequential update semantics: nine is the
final first element; the two existing charged updates cost twenty-two. -/
theorem rank_four_bulk :
    fromRA (bulkRun (sparse 4 (perfectTree (7 : ℕ) 4)) [(0,8),(0,9)]).1 =
        9 :: List.replicate 15 7 ∧
      (bulkRun (sparse 4 (perfectTree (7 : ℕ) 4)) [(0,8),(0,9)]).2 = 22 ∧
      (bulkRun (sparse 4 (perfectTree (7 : ℕ) 4)) [(0,8),(0,9)]).2 ≤ 24 := by
  have hv : Inv (sparse 4 (perfectTree (7 : ℕ) 4)) :=
    sparse_valid 0 4 (perfectTree_valid 7 4)
  have hn : 16 ≤ (fromRA (sparse 4 (perfectTree (7 : ℕ) 4))).length := by
    simp [sparse_value, perfectTree_values]
  have h := bulkRun_sqrt_spec hv hn [(0,8),(0,9)]
  refine ⟨?_, bulk_sparse_zero_cost 4 (perfectTree_valid 7 4) [8,9], ?_⟩
  · rw [h.1, sparse_value, perfectTree_values]
    rfl
  · norm_num [sparse_value, perfectTree_values, (show Nat.sqrt 16 = 4 from Nat.sqrt_eq 4)] at h
    exact h.2

/-- A request beyond the list still uses the valid represented length bound. -/
theorem rank_four_fetch_out_of_range :
    (fetchRARun 100 (sparse 4 (perfectTree (7 : ℕ) 4))).1 = none ∧
      (fetchRARun 100 (sparse 4 (perfectTree (7 : ℕ) 4))).2 ≤ 11 := by
  have hv : Inv (sparse 4 (perfectTree (7 : ℕ) 4)) :=
    sparse_valid 0 4 (perfectTree_valid 7 4)
  have hn : 16 ≤ (fromRA (sparse 4 (perfectTree (7 : ℕ) 4))).length := by
    simp [sparse_value, perfectTree_values]
  have h := fetchRARun_sqrt_spec hv hn 100
  norm_num [sparse_value, perfectTree_values, (show Nat.sqrt 16 = 4 from Nat.sqrt_eq 4)] at h
  exact h

end Examples.DiscreteEstimates


/-! D1 client fragments for root's Examples.DiscreteEstimates assembly. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.DiscreteEstimates
open SquareKit.DiscreteScales

/-- C4: the native exact-power logarithm identifies the exponent. -/
theorem source_log2_twenty : Nat.log2 (2 ^ 20) = 20 := Nat.log2_two_pow

/-- C5: the square-root bridge is instantiated at half the exponent. -/
theorem source_sqrt_twenty : Nat.sqrt (2 ^ 20) = 2 ^ 10 := by
  simpa using sqrt_two_pow_even 10

/-- The positive lower-log bracket cannot include zero. -/
theorem log2_lower_zero_failure : ¬ 2 ^ Nat.log2 0 ≤ (0 : ℕ) := by
  decide

/-- Three is below the retained square/power threshold: nine exceeds eight. -/
theorem square_power_three_failure : ¬ (3 : ℕ) * 3 ≤ 2 ^ 3 := by
  decide

/-- Four connects the threshold case to the universal finite power comparison. -/
theorem square_power_four : (4 : ℕ) * 4 ≤ 2 ^ 4 :=
  square_le_two_pow (by decide)

/-- The proposed log/root bound fails at eight: three exceeds two. -/
theorem log2_sqrt_eight_failure : ¬ Nat.log2 8 ≤ Nat.sqrt 8 := by
  rw [show Nat.sqrt 8 = 2 from (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm]
  decide

/-- Sixteen is the stated log/root threshold; both scales equal four. -/
theorem log2_sqrt_sixteen : Nat.log2 16 ≤ Nat.sqrt 16 :=
  log2_le_sqrt (by decide)

/-- The finite comparison also applies to odd represented lengths. -/
theorem log2_sqrt_seventeen : Nat.log2 17 ≤ Nat.sqrt 17 :=
  log2_le_sqrt (by decide)

/-- The exact-power square-root bridge includes the zeroth exponent. -/
theorem sqrt_even_power_zero : Nat.sqrt (2 ^ (2 * 0)) = 1 := by
  exact sqrt_two_pow_even 0

/-- The all-natural cubic estimate keeps its zero case through the public result. -/
theorem cubic_lower_terms_zero :
    (0 : ℕ) ≤ 0 * 0 * 0 + 0 * 0 + 0 * Nat.log2 0 ∧
      0 * 0 * 0 + 0 * 0 + 0 * Nat.log2 0 ≤ 0 := by
  exact cubic_lower_terms_bounds 0

end Examples.DiscreteEstimates

/-! D2 band cases for root's Examples.DiscreteEstimates assembly. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.DiscreteEstimates
open SquareKit.DiscreteScales

/-- The native floor logarithm itself satisfies the positive-index band hypothesis. -/
theorem floor_logBand_mem : ∀ n : ℕ, 1 ≤ n →
    (Nat.log2 n : ℚ) ∈ Set.Icc (Nat.log2 n : ℚ) ((Nat.log2 n : ℚ) + 1) := by
  intro n _
  exact ⟨le_rfl, le_add_of_nonneg_right (by norm_num)⟩

/-- The native floor root itself satisfies the positive-index band hypothesis. -/
theorem floor_rootBand_mem : ∀ n : ℕ, 1 ≤ n →
    (Nat.sqrt n : ℚ) ∈ Set.Icc (Nat.sqrt n : ℚ) ((Nat.sqrt n : ℚ) + 1) := by
  intro n _
  exact ⟨le_rfl, le_add_of_nonneg_right (by norm_num)⟩

/-- A half-unit log offset, with its zero value independently chosen. -/
def halfOffsetLog (zeroValue : ℚ) (n : ℕ) : ℚ :=
  if n = 0 then zeroValue else (Nat.log2 n : ℚ) + 1 / 2

/-- A half-unit root offset, with its zero value independently chosen. -/
def halfOffsetRoot (zeroValue : ℚ) (n : ℕ) : ℚ :=
  if n = 0 then zeroValue else (Nat.sqrt n : ℚ) + 1 / 2

/-- Every zero value, including a negative one, is compatible with the log band. -/
theorem halfOffsetLog_mem (zeroValue : ℚ) : ∀ n : ℕ, 1 ≤ n →
    halfOffsetLog zeroValue n ∈ Set.Icc (Nat.log2 n : ℚ) ((Nat.log2 n : ℚ) + 1) := by
  intro n hn
  simp only [halfOffsetLog, ite_eq_right (show n ≠ 0 by omega), Set.mem_Icc]
  constructor <;> linarith

/-- Every zero value, including a negative one, is compatible with the root band. -/
theorem halfOffsetRoot_mem (zeroValue : ℚ) : ∀ n : ℕ, 1 ≤ n →
    halfOffsetRoot zeroValue n ∈ Set.Icc (Nat.sqrt n : ℚ) ((Nat.sqrt n : ℚ) + 1) := by
  intro n hn
  simp only [halfOffsetRoot, ite_eq_right (show n ≠ 0 by omega), Set.mem_Icc]
  constructor <;> linarith

/-- The two bands really can have negative values at zero. -/
theorem negative_band_zero :
    halfOffsetLog (-7) 0 = -7 ∧ halfOffsetRoot (-3) 0 = -3 := by
  simp [halfOffsetLog, halfOffsetRoot]

/-- Both positive-index bounds consume the public arbitrary-band estimates. -/
theorem halfOffset_bounds (logZero rootZero : ℚ) {n : ℕ} (hn : 2 ≤ n) :
    ((Nat.log2 n : ℚ) ≤ halfOffsetLog logZero n ∧
      halfOffsetLog logZero n ≤ 2 * (Nat.log2 n : ℚ)) ∧
    ((Nat.sqrt n : ℚ) ≤ halfOffsetRoot rootZero n ∧
      halfOffsetRoot rootZero n ≤ 2 * (Nat.sqrt n : ℚ)) :=
  ⟨logBand_bounds (halfOffsetLog_mem logZero) hn,
    rootBand_bounds (halfOffsetRoot_mem rootZero) (by omega)⟩

/-- The finite coefficient-two comparison uses the same two offset bands. -/
theorem halfOffset_interpolation (logZero rootZero : ℚ) {n : ℕ} (hn : 16 ≤ n) :
    (n : ℚ) * halfOffsetLog logZero n ≤ 2 * ((n : ℚ) * halfOffsetRoot rootZero n) :=
  mul_logBand_le_two_mul_rootBand
    (halfOffsetLog_mem logZero) (halfOffsetRoot_mem rootZero) hn

/-- Arbitrary zero values do not obstruct the universal strict counterfamily. -/
theorem halfOffset_counterfamily (logZero rootZero C : ℚ) (hC : 0 < C) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      C * (halfOffsetRoot rootZero n * halfOffsetLog logZero n) <
        (n : ℚ) + halfOffsetRoot rootZero n :=
  band_counterexample (halfOffsetLog_mem logZero) (halfOffsetRoot_mem rootZero) C hC N

/-- An admissible whole log band with value one at one breaks the twice-floor bound. -/
theorem logBand_one_failure :
    ∃ l : ℕ → ℚ,
      (∀ n, 1 ≤ n → l n ∈ Set.Icc (Nat.log2 n : ℚ) ((Nat.log2 n : ℚ) + 1)) ∧
      l 1 = 1 ∧ ¬ l 1 ≤ 2 * (Nat.log2 1 : ℚ) := by
  refine ⟨fun n => (Nat.log2 n : ℚ) + 1, ?_, ?_⟩
  · intro n _
    exact ⟨le_add_of_nonneg_right (by norm_num), le_rfl⟩
  · norm_num [Nat.log2_def]

end Examples.DiscreteEstimates

/-!
# DISCRETE M3 fragment for root assembly

These declarations compose the existing inclusive scanner with native finite
additive prefix sums. The supplied shape and scanner remain arbitrary, and the
only input adequacy premise describes the flattened input.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.DiscreteEstimates

open Applications.Parallel
open scoped BigOperators

universe u

/-- Decode every inclusive state of the supplied scanner as its independent finite prefix sum. -/
theorem inclusive_finite_prefix_sums {A : Type u} [AddCommMonoid A] {s : Shape}
    (p : Scanner s (Multiplicative A)) (x : s.Data (Multiplicative A))
    (f : Nat → A) (n : Nat)
    (hx : s.flatten x = (List.range n).map (fun j => Multiplicative.ofAdd (f j))) :
    (p.inclusive x).map Multiplicative.toAdd =
      (List.range (n + 1)).map (fun k => ∑ j ∈ Finset.range k, f j) := by
  rw [Scanner.inclusive_correct, hx, SquareKit.ListFusion.scanl_prefix_values]
  simp only [List.length_map, List.length_range, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
  dsimp only [Function.comp_apply]
  rw [← List.map_take, List.take_range, Nat.min_eq_left hkn,
    ← List.prod_eq_foldl, toAdd_list_sum, List.map_map]
  change ((List.range k).map f).sum = ∑ j ∈ Finset.range k, f j
  simpa only [List.toFinset_range] using
    (List.sum_toFinset f (List.nodup_range (n := k))).symm

/-- The final component of the actual run is the last inclusive finite prefix. -/
theorem inclusive_finite_total {A : Type u} [AddCommMonoid A] {s : Shape}
    (p : Scanner s (Multiplicative A)) (x : s.Data (Multiplicative A))
    (f : Nat → A) (n : Nat)
    (hx : s.flatten x = (List.range n).map (fun j => Multiplicative.ofAdd (f j))) :
    Multiplicative.toAdd (p.run x).2 = ∑ j ∈ Finset.range n, f j := by
  have h := congrArg List.getLast? (inclusive_finite_prefix_sums p x f n hx)
  simpa [Scanner.inclusive, List.range_succ] using h

/-- Rational successor reciprocals recover all native harmonic prefixes. -/
theorem inclusive_harmonic_prefixes {s : Shape}
    (p : Scanner s (Multiplicative ℚ)) (x : s.Data (Multiplicative ℚ)) (n : Nat)
    (hx : s.flatten x = (List.range n).map
      (fun j => Multiplicative.ofAdd (((j + 1 : Nat) : ℚ)⁻¹))) :
    (p.inclusive x).map Multiplicative.toAdd = (List.range (n + 1)).map harmonic := by
  exact inclusive_finite_prefix_sums p x (fun j => (((j + 1 : Nat) : ℚ)⁻¹)) n hx

/-- The total produced by that same run is the native harmonic number. -/
theorem inclusive_harmonic_total {s : Shape}
    (p : Scanner s (Multiplicative ℚ)) (x : s.Data (Multiplicative ℚ)) (n : Nat)
    (hx : s.flatten x = (List.range n).map
      (fun j => Multiplicative.ofAdd (((j + 1 : Nat) : ℚ)⁻¹))) :
    Multiplicative.toAdd (p.run x).2 = harmonic n := by
  exact inclusive_finite_total p x (fun j => (((j + 1 : Nat) : ℚ)⁻¹)) n hx

/-- The finite dyadic estimate applies to the actual scanner's returned total. -/
theorem harmonic_scan_dyadic_bounds {s : Shape}
    (p : Scanner s (Multiplicative ℚ)) (x : s.Data (Multiplicative ℚ)) (k : Nat)
    (hx : s.flatten x = (List.range (2 ^ k)).map
      (fun j => Multiplicative.ofAdd (((j + 1 : Nat) : ℚ)⁻¹))) :
    1 + (k : ℚ) / 2 ≤ Multiplicative.toAdd (p.run x).2 ∧
      Multiplicative.toAdd (p.run x).2 ≤ 1 + (k : ℚ) := by
  rw [inclusive_harmonic_total p x (2 ^ k) hx]
  exact SquareKit.HarmonicBounds.harmonic_dyadic_bounds k

/-- Four reciprocals, represented for the existing composition of two pair scans. -/
def harmonicFourInput : (ScanPlan.comp .pair .pair).shape.Data (Multiplicative ℚ) :=
  ((Multiplicative.ofAdd (1 : ℚ), Multiplicative.ofAdd (1 / 2 : ℚ)),
    (Multiplicative.ofAdd (1 / 3 : ℚ), Multiplicative.ofAdd (1 / 4 : ℚ)))

/-- The concrete composed input is exactly the tagged successor-reciprocal sequence. -/
theorem harmonicFourInput_flatten :
    (ScanPlan.comp .pair .pair).shape.flatten harmonicFourInput =
      (List.range 4).map
        (fun j => Multiplicative.ofAdd (((j + 1 : Nat) : ℚ)⁻¹)) := by
  change ([1, 1 / 2, 1 / 3, 1 / 4] : List ℚ) =
    [(((0 + 1 : Nat) : ℚ)⁻¹), (((1 + 1 : Nat) : ℚ)⁻¹),
      (((2 + 1 : Nat) : ℚ)⁻¹), (((3 + 1 : Nat) : ℚ)⁻¹)]
  norm_num

/-- The two pair scans and outer total scan preserve every rational prefix. -/
theorem harmonic_four_prefixes :
    ((ScanPlan.comp .pair .pair).scanner.inclusive harmonicFourInput).map
      Multiplicative.toAdd = [0, 1, 3 / 2, 11 / 6, 25 / 12] := by
  calc
    _ = (List.range (4 + 1)).map harmonic :=
      inclusive_harmonic_prefixes _ _ 4 harmonicFourInput_flatten
    _ = [0, 1, 3 / 2, 11 / 6, 25 / 12] := by
      have h1 : harmonic 1 = (1 : ℚ) := by
        rw [harmonic_succ 0, harmonic_zero]
        norm_num
      have h2 : harmonic 2 = (3 / 2 : ℚ) := by
        rw [harmonic_succ 1, h1]
        norm_num
      have h3 : harmonic 3 = (11 / 6 : ℚ) := by
        rw [harmonic_succ 2, h2]
        norm_num
      have h4 : harmonic 4 = (25 / 12 : ℚ) := by
        rw [harmonic_succ 3, h3]
        norm_num
      change [harmonic 0, harmonic 1, harmonic 2, harmonic 3, harmonic 4] =
        [0, 1, 3 / 2, 11 / 6, 25 / 12]
      rw [harmonic_zero, h1, h2, h3, h4]

/-- The second noninitial scanner prefix retains the first harmonic source case. -/
theorem harmonic_two : harmonic 2 = (3 / 2 : ℚ) := by
  have hs := inclusive_harmonic_prefixes
    (ScanPlan.comp .pair .pair).scanner harmonicFourInput 4 harmonicFourInput_flatten
  have h := congrArg (fun xs : List ℚ => xs[2]?) (hs.symm.trans harmonic_four_prefixes)
  change some (harmonic 2) = some (3 / 2 : ℚ) at h
  exact Option.some.inj h

/-- The final scanner prefix retains the second harmonic source case. -/
theorem harmonic_four : harmonic 4 = (25 / 12 : ℚ) := by
  have hs := inclusive_harmonic_prefixes
    (ScanPlan.comp .pair .pair).scanner harmonicFourInput 4 harmonicFourInput_flatten
  have h := congrArg (fun xs : List ℚ => xs[4]?) (hs.symm.trans harmonic_four_prefixes)
  change some (harmonic 4) = some (25 / 12 : ℚ) at h
  exact Option.some.inj h

/-- The empty plan still returns the initial harmonic state. -/
theorem harmonic_empty_prefixes :
    ((ScanPlan.empty.scanner : Scanner .empty (Multiplicative ℚ)).inclusive PUnit.unit).map
      Multiplicative.toAdd = [0] := by
  calc
    _ = (List.range (0 + 1)).map harmonic :=
      inclusive_harmonic_prefixes _ _ 0 (by rfl)
    _ = [0] := rfl

/-- The third harmonic source case uses the general positive doubling theorem. -/
theorem reciprocal_block_eight_bounds :
    (1 / 2 : ℚ) ≤ (∑ j ∈ Finset.range 8, (((8 + j + 1 : Nat) : ℚ)⁻¹)) ∧
      (∑ j ∈ Finset.range 8, (((8 + j + 1 : Nat) : ℚ)⁻¹)) ≤ 1 :=
  SquareKit.HarmonicBounds.doubling_block_bounds 8 (by decide)

/-- The zero dyadic index is the nonempty harmonic value at one. -/
theorem harmonic_dyadic_zero :
    (1 : ℚ) ≤ harmonic 1 ∧ harmonic 1 ≤ 1 := by
  simpa only [Nat.pow_zero, Nat.cast_zero, zero_div, add_zero] using
    SquareKit.HarmonicBounds.harmonic_dyadic_bounds 0

/-- At a zero block start and zero block length, the positive doubling lower bound is false. -/
theorem doubling_zero_lower_false :
    ¬((1 / 2 : ℚ) ≤ ∑ j ∈ Finset.range 0, (((0 + j + 1 : Nat) : ℚ)⁻¹)) := by
  norm_num

/-- A zero upper comparison denominator cannot replace its positive-parameter premise. -/
theorem block_upper_zero_parameter_false :
    ¬((∑ j ∈ Finset.range 1, (((0 + j + 1 : Nat) : ℚ)⁻¹)) ≤ (1 : ℚ) / 0) := by
  norm_num

/-- The logarithmic finite estimate applies to the actual harmonic scanner total. -/
theorem harmonic_scan_log2_bounds {s : Shape}
    (p : Scanner s (Multiplicative ℚ)) (x : s.Data (Multiplicative ℚ))
    (n : Nat) (hn : 1 ≤ n)
    (hx : s.flatten x = (List.range n).map
      (fun j => Multiplicative.ofAdd (((j + 1 : Nat) : ℚ)⁻¹))) :
    (n.log2 : ℚ) / 2 ≤ Multiplicative.toAdd (p.run x).2 ∧
      Multiplicative.toAdd (p.run x).2 ≤ (n.log2 : ℚ) + 2 := by
  rw [inclusive_harmonic_total p x n hx]
  exact SquareKit.HarmonicBounds.harmonic_log2_bounds n hn

/-- The concrete composed scan satisfies the finite dyadic estimate at its actual endpoint. -/
theorem harmonic_four_run_bounds :
    (2 : ℚ) ≤ Multiplicative.toAdd
      ((ScanPlan.comp .pair .pair).scanner.run harmonicFourInput).2 ∧
      Multiplicative.toAdd ((ScanPlan.comp .pair .pair).scanner.run harmonicFourInput).2 ≤ 3 := by
  have h := harmonic_scan_dyadic_bounds
    (ScanPlan.comp .pair .pair).scanner harmonicFourInput 2 harmonicFourInput_flatten
  norm_num at h
  exact h

/-- The harmonic coefficient bound needs its threshold two. -/
theorem harmonic_log2_upper_one_false :
    ¬(harmonic 1 ≤ 3 * (Nat.log2 1 : ℚ)) := by
  have hlog : Nat.log2 1 = 0 := by decide
  rw [hlog]
  norm_num [harmonic]

/-- Weighted successor inputs give the native positive-interval sum at every prefix. -/
theorem inclusive_weighted_prefixes {s : Shape}
    (p : Scanner s (Multiplicative Nat)) (x : s.Data (Multiplicative Nat)) (n : Nat)
    (hx : s.flatten x = (List.range n).map
      (fun j => Multiplicative.ofAdd ((j + 1) * Nat.log2 (j + 1)))) :
    (p.inclusive x).map Multiplicative.toAdd = (List.range (n + 1)).map
      (fun k => ∑ i ∈ Finset.Ico 1 (k + 1), i * Nat.log2 i) := by
  rw [inclusive_finite_prefix_sums p x (fun j => (j + 1) * Nat.log2 (j + 1)) n hx]
  apply List.map_congr_left
  intro k _
  symm
  simpa [Nat.add_comm] using
    (Finset.sum_Ico_eq_sum_range (fun i : Nat => i * Nat.log2 i) 1 (k + 1))

/-- The actual returned natural total is the positive weighted sum. -/
theorem inclusive_weighted_total {s : Shape}
    (p : Scanner s (Multiplicative Nat)) (x : s.Data (Multiplicative Nat)) (n : Nat)
    (hx : s.flatten x = (List.range n).map
      (fun j => Multiplicative.ofAdd ((j + 1) * Nat.log2 (j + 1)))) :
    Multiplicative.toAdd (p.run x).2 = ∑ i ∈ Finset.Ico 1 (n + 1), i * Nat.log2 i := by
  have h := congrArg List.getLast? (inclusive_weighted_prefixes p x n hx)
  simpa [Scanner.inclusive, List.range_succ] using h

/-- Four weighted inputs use the same existing composition of pair scans. -/
def weightedFourInput : (ScanPlan.comp .pair .pair).shape.Data (Multiplicative Nat) :=
  ((Multiplicative.ofAdd 0, Multiplicative.ofAdd 2),
    (Multiplicative.ofAdd 3, Multiplicative.ofAdd 8))

/-- Both initial zero states are retained by the weighted inclusive scan. -/
theorem weighted_four_prefixes :
    ((ScanPlan.comp .pair .pair).scanner.inclusive weightedFourInput).map
      Multiplicative.toAdd = [0, 0, 2, 5, 13] := by
  calc
    _ = (List.range (4 + 1)).map
        (fun k => ∑ i ∈ Finset.Ico 1 (k + 1), i * Nat.log2 i) :=
      inclusive_weighted_prefixes _ _ 4 (by rfl)
    _ = [0, 0, 2, 5, 13] := by decide

/-- The native weighted source case is obtained through the actual scan endpoint. -/
theorem weighted_four :
    (∑ i ∈ Finset.Ico 1 (4 + 1), i * Nat.log2 i) = 13 := by
  have hs := inclusive_weighted_prefixes
    (ScanPlan.comp .pair .pair).scanner weightedFourInput 4 (by rfl)
  have h := congrArg (fun xs : List Nat => xs[4]?) (hs.symm.trans weighted_four_prefixes)
  change some (∑ i ∈ Finset.Ico 1 (4 + 1), i * Nat.log2 i) = some 13 at h
  exact Option.some.inj h

/-- The empty weighted plan returns the single initial zero. -/
theorem weighted_empty_prefixes :
    ((ScanPlan.empty.scanner : Scanner .empty (Multiplicative Nat)).inclusive PUnit.unit).map
      Multiplicative.toAdd = [0] := by
  calc
    _ = (List.range (0 + 1)).map
        (fun k => ∑ i ∈ Finset.Ico 1 (k + 1), i * Nat.log2 i) :=
      inclusive_weighted_prefixes _ _ 0 (by rfl)
    _ = [0] := rfl

end Examples.DiscreteEstimates

namespace Examples.DiscreteEstimates

/-- The finite weighted bounds apply to the total returned by the supplied scanner. -/
theorem weighted_scan_bounds {s : Applications.Parallel.Shape}
    (p : Applications.Parallel.Scanner s (Multiplicative Nat))
    (x : s.Data (Multiplicative Nat)) (n : Nat) (hn : 4 ≤ n)
    (hx : s.flatten x = (List.range n).map
      (fun j => Multiplicative.ofAdd ((j + 1) * Nat.log2 (j + 1)))) :
    n * n * Nat.log2 n ≤ 18 * Multiplicative.toAdd (p.run x).2 ∧
      Multiplicative.toAdd (p.run x).2 ≤ n * n * Nat.log2 n := by
  rw [inclusive_weighted_total p x n hx]
  exact SquareKit.LogarithmicSums.weighted_log_bounds n hn

end Examples.DiscreteEstimates

/-!
# Native norm growth clients of the finite discrete scale estimates

All bands constrain only positive indices. Eventual sign proofs are established
at the actual use sites of the accepted rational coefficient bridge.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.DiscreteEstimates
open Filter Asymptotics SquareKit.DiscreteScales

/-- Every admissible log band has the native norm order of the floor logarithm. -/
theorem logBand_isTheta {l : ℕ → ℚ}
    (hl : ∀ n, 1 ≤ n → l n ∈ Set.Icc (Nat.log2 n : ℚ) ((Nat.log2 n : ℚ) + 1)) :
    l =Θ[atTop] (fun n : ℕ => (Nat.log2 n : ℚ)) := by
  have hband : ∀ᶠ n : ℕ in atTop, 0 ≤ l n := by
    refine eventually_atTop.mpr ⟨1, ?_⟩
    intro n hn
    exact (Nat.cast_nonneg (Nat.log2 n)).trans (hl n hn).1
  have hfloor : ∀ᶠ n : ℕ in atTop, 0 ≤ (Nat.log2 n : ℚ) :=
    Eventually.of_forall fun n => Nat.cast_nonneg (Nat.log2 n)
  apply Asymptotics.IsBigO.antisymm
  · apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hband hfloor).mpr
    refine ⟨2, by norm_num, eventually_atTop.mpr ⟨2, ?_⟩⟩
    intro n hn
    exact (logBand_bounds hl hn).2
  · apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hfloor hband).mpr
    refine ⟨1, by norm_num, eventually_atTop.mpr ⟨2, ?_⟩⟩
    intro n hn
    simpa only [one_mul] using (logBand_bounds hl hn).1

/-- Every admissible root band has the native norm order of the floor root. -/
theorem rootBand_isTheta {s : ℕ → ℚ}
    (hs : ∀ n, 1 ≤ n → s n ∈ Set.Icc (Nat.sqrt n : ℚ) ((Nat.sqrt n : ℚ) + 1)) :
    s =Θ[atTop] (fun n : ℕ => (Nat.sqrt n : ℚ)) := by
  have hband : ∀ᶠ n : ℕ in atTop, 0 ≤ s n := by
    refine eventually_atTop.mpr ⟨1, ?_⟩
    intro n hn
    exact (Nat.cast_nonneg (Nat.sqrt n)).trans (hs n hn).1
  have hfloor : ∀ᶠ n : ℕ in atTop, 0 ≤ (Nat.sqrt n : ℚ) :=
    Eventually.of_forall fun n => Nat.cast_nonneg (Nat.sqrt n)
  apply Asymptotics.IsBigO.antisymm
  · apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hband hfloor).mpr
    refine ⟨2, by norm_num, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    exact (rootBand_bounds hs hn).2
  · apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hfloor hband).mpr
    refine ⟨1, by norm_num, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    simpa only [one_mul] using (rootBand_bounds hs hn).1

/-- The finite coefficient-two band comparison gives native norm Big O. -/
theorem mul_logBand_isBigO_mul_rootBand {l s : ℕ → ℚ}
    (hl : ∀ n, 1 ≤ n → l n ∈ Set.Icc (Nat.log2 n : ℚ) ((Nat.log2 n : ℚ) + 1))
    (hs : ∀ n, 1 ≤ n → s n ∈ Set.Icc (Nat.sqrt n : ℚ) ((Nat.sqrt n : ℚ) + 1)) :
    (fun n : ℕ => (n : ℚ) * l n) =O[atTop] (fun n : ℕ => (n : ℚ) * s n) := by
  have hleft : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℚ) * l n := by
    refine eventually_atTop.mpr ⟨1, ?_⟩
    intro n hn
    exact mul_nonneg (Nat.cast_nonneg n)
      ((Nat.cast_nonneg (Nat.log2 n)).trans (hl n hn).1)
  have hright : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℚ) * s n := by
    refine eventually_atTop.mpr ⟨1, ?_⟩
    intro n hn
    exact mul_nonneg (Nat.cast_nonneg n)
      ((Nat.cast_nonneg (Nat.sqrt n)).trans (hs n hn).1)
  apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hleft hright).mpr
  refine ⟨2, by norm_num, eventually_atTop.mpr ⟨16, ?_⟩⟩
  intro n hn
  exact mul_logBand_le_two_mul_rootBand hl hs hn

/-- No native norm Big-O coefficient bounds the linear-plus-root function by root times log. -/
theorem linear_add_sqrt_not_isBigO_sqrt_log2 :
    ¬ ((fun n : ℕ => (n : ℚ) + (Nat.sqrt n : ℚ)) =O[atTop]
      (fun n : ℕ => (Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ))) := by
  have hleft : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℚ) + (Nat.sqrt n : ℚ) :=
    Eventually.of_forall fun n => add_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg (Nat.sqrt n))
  have hright : ∀ᶠ n : ℕ in atTop, 0 ≤ (Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ) :=
    Eventually.of_forall fun n =>
      mul_nonneg (Nat.cast_nonneg (Nat.sqrt n)) (Nat.cast_nonneg (Nat.log2 n))
  intro h
  obtain ⟨C, hC, hbound⟩ :=
    (Resources.isBigO_rat_iff_eventually_le_mul _ _ hleft hright).mp h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  obtain ⟨n, hn, hstrict⟩ := sqrt_log2_counterexample C hC N
  exact (not_lt_of_ge (hN n hn)) hstrict

/-- The native norm failure persists for arbitrary bands, with no sign condition at zero. -/
theorem linear_add_rootBand_not_isBigO_rootBand_mul_logBand {l s : ℕ → ℚ}
    (hl : ∀ n, 1 ≤ n → l n ∈ Set.Icc (Nat.log2 n : ℚ) ((Nat.log2 n : ℚ) + 1))
    (hs : ∀ n, 1 ≤ n → s n ∈ Set.Icc (Nat.sqrt n : ℚ) ((Nat.sqrt n : ℚ) + 1)) :
    ¬ ((fun n : ℕ => (n : ℚ) + s n) =O[atTop] (fun n : ℕ => s n * l n)) := by
  have hleft : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℚ) + s n := by
    refine eventually_atTop.mpr ⟨1, ?_⟩
    intro n hn
    exact add_nonneg (Nat.cast_nonneg n)
      ((Nat.cast_nonneg (Nat.sqrt n)).trans (hs n hn).1)
  have hright : ∀ᶠ n : ℕ in atTop, 0 ≤ s n * l n := by
    refine eventually_atTop.mpr ⟨1, ?_⟩
    intro n hn
    exact mul_nonneg
      ((Nat.cast_nonneg (Nat.sqrt n)).trans (hs n hn).1)
      ((Nat.cast_nonneg (Nat.log2 n)).trans (hl n hn).1)
  intro h
  obtain ⟨C, hC, hbound⟩ :=
    (Resources.isBigO_rat_iff_eventually_le_mul _ _ hleft hright).mp h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  obtain ⟨n, hn, hstrict⟩ := band_counterexample hl hs C hC N
  exact (not_lt_of_ge (hN n hn)) hstrict

/-- C6 consumes the complete universally quantified finite counterfamily through native norm transport. -/
theorem source_floor_not_isBigO :
    ¬ ((fun n : ℕ => (n : ℚ) + (Nat.sqrt n : ℚ)) =O[atTop]
      (fun n : ℕ => (Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ))) :=
  linear_add_sqrt_not_isBigO_sqrt_log2

end Examples.DiscreteEstimates

/-!
# Native rational harmonic asymptotics

Assembly fragment for `Examples.DiscreteEstimates`. Each native norm statement
uses the accepted rational order/norm bridge, with eventual signs established
for the actual functions and explicit finite coefficients from index two.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.DiscreteEstimates

/-- Native rational Theta follows from the finite coefficients three and two. -/
theorem harmonic_isTheta_log2 :
    Asymptotics.IsTheta Filter.atTop harmonic (fun n : Nat => (n.log2 : ℚ)) := by
  have hH : ∀ᶠ n : Nat in Filter.atTop, (0 : ℚ) ≤ harmonic n :=
    Filter.eventually_atTop.mpr
      ⟨2, fun n _ => SquareKit.HarmonicBounds.harmonic_nonneg n⟩
  have hL : ∀ᶠ n : Nat in Filter.atTop, (0 : ℚ) ≤ (n.log2 : ℚ) :=
    Filter.eventually_atTop.mpr ⟨2, fun n _ => Nat.cast_nonneg n.log2⟩
  constructor
  · apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hH hL).mpr
    refine ⟨3, by norm_num, Filter.eventually_atTop.mpr ⟨2, ?_⟩⟩
    intro n hn
    exact (SquareKit.HarmonicBounds.harmonic_log2_coefficients n hn).2
  · apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hL hH).mpr
    refine ⟨2, by norm_num, Filter.eventually_atTop.mpr ⟨2, ?_⟩⟩
    intro n hn
    have h := (SquareKit.HarmonicBounds.harmonic_log2_coefficients n hn).1
    linarith

/-- A rational band is constrained only at positive indices; its value at zero remains free. -/
theorem harmonic_isTheta_logBand {l : Nat → ℚ}
    (hl : ∀ n, 1 ≤ n → l n ∈ Set.Icc (n.log2 : ℚ) ((n.log2 : ℚ) + 1)) :
    Asymptotics.IsTheta Filter.atTop harmonic l := by
  have hH : ∀ᶠ n : Nat in Filter.atTop, (0 : ℚ) ≤ harmonic n :=
    Filter.eventually_atTop.mpr
      ⟨2, fun n _ => SquareKit.HarmonicBounds.harmonic_nonneg n⟩
  have hL : ∀ᶠ n : Nat in Filter.atTop, (0 : ℚ) ≤ l n := by
    apply Filter.eventually_atTop.mpr
    refine ⟨2, fun n hn => ?_⟩
    exact (Nat.cast_nonneg n.log2).trans (hl n (by omega)).1
  constructor
  · apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hH hL).mpr
    refine ⟨3, by norm_num, Filter.eventually_atTop.mpr ⟨2, ?_⟩⟩
    intro n hn
    exact (SquareKit.HarmonicBounds.harmonic_logBand_coefficients hl n hn).2
  · apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hL hH).mpr
    refine ⟨4, by norm_num, Filter.eventually_atTop.mpr ⟨2, ?_⟩⟩
    intro n hn
    have h := (SquareKit.HarmonicBounds.harmonic_logBand_coefficients hl n hn).1
    linarith

/-- The actual nonnegative index products retain the same native rational Theta constants. -/
theorem mul_harmonic_isTheta_mul_log2 :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => (n : ℚ) * harmonic n)
      (fun n : Nat => (n : ℚ) * (n.log2 : ℚ)) := by
  have hH : ∀ᶠ n : Nat in Filter.atTop, (0 : ℚ) ≤ (n : ℚ) * harmonic n :=
    Filter.eventually_atTop.mpr ⟨2, fun n _ =>
      mul_nonneg (Nat.cast_nonneg n) (SquareKit.HarmonicBounds.harmonic_nonneg n)⟩
  have hL : ∀ᶠ n : Nat in Filter.atTop, (0 : ℚ) ≤ (n : ℚ) * (n.log2 : ℚ) :=
    Filter.eventually_atTop.mpr ⟨2, fun n _ =>
      mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n.log2)⟩
  constructor
  · apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hH hL).mpr
    refine ⟨3, by norm_num, Filter.eventually_atTop.mpr ⟨2, ?_⟩⟩
    intro n hn
    exact (SquareKit.HarmonicBounds.mul_harmonic_log2_coefficients n hn).2
  · apply (Resources.isBigO_rat_iff_eventually_le_mul _ _ hL hH).mpr
    refine ⟨2, by norm_num, Filter.eventually_atTop.mpr ⟨2, ?_⟩⟩
    intro n hn
    have h := (SquareKit.HarmonicBounds.mul_harmonic_log2_coefficients n hn).1
    linarith

end Examples.DiscreteEstimates

/-!
# Native growth and actual permutation-count clients

The growth statements use real casts of native natural quantities. The search
observations count positional occurrences through the existing counter, with
an arbitrary stored prefix and without requiring element equality. They do not
assert running time, bit complexity, or the number of distinct output lists.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.DiscreteEstimates

open Finset SquareKit.LogarithmicSums
open scoped BigOperators

universe u
variable {α : Type u}

/-- Forward coefficient two and reverse coefficient six apply from index four. -/
theorem factorial_log2_isTheta :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ => ((Nat.factorial n).log2 : ℝ))
      (fun n : ℕ => ((n * n.log2 : ℕ) : ℝ)) := by
  constructor
  · exact Resources.isBigO_of_nat_bound
      (fun n => (Nat.factorial n).log2) (fun n => n * n.log2) 2 4
      (fun n hn => (factorial_log2_bounds n hn).2)
  · exact Resources.isBigO_of_nat_bound
      (fun n => n * n.log2) (fun n => (Nat.factorial n).log2) 6 4
      (fun n hn => (factorial_log2_bounds n hn).1)

/-- The positive weighted sum has coefficients one and eighteen from four. -/
theorem weighted_log_isTheta :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ => ((∑ k ∈ Ico 1 (n + 1), k * k.log2 : ℕ) : ℝ))
      (fun n : ℕ => ((n * n * n.log2 : ℕ) : ℝ)) := by
  constructor
  · apply Resources.isBigO_of_nat_bound
      (fun n => ∑ k ∈ Ico 1 (n + 1), k * k.log2) (fun n => n * n * n.log2) 1 4
    intro n hn
    simpa only [Nat.one_mul] using (weighted_log_bounds n hn).2
  · exact Resources.isBigO_of_nat_bound
      (fun n => n * n * n.log2) (fun n => ∑ k ∈ Ico 1 (n + 1), k * k.log2) 18 4
      (fun n hn => (weighted_log_bounds n hn).1)

/-- The actual occurrence count has the factorial-log bounds for any stored prefix. -/
theorem permutation_count_log_bounds (remaining chosen : List α)
    (hn : 4 ≤ remaining.length) :
    remaining.length * remaining.length.log2 ≤
        6 * (FiniteSearch.count PermutationSearch.next remaining.length
          (chosen, remaining)).log2 ∧
      (FiniteSearch.count PermutationSearch.next remaining.length
        (chosen, remaining)).log2 ≤ 2 * (remaining.length * remaining.length.log2) := by
  simpa only [PermutationSearch.count_factorial] using
    factorial_log2_bounds remaining.length hn

/-- Eight equal values still yield 40320 occurrences, whose floor logarithm is fifteen. -/
theorem permutation_repeated_eight (x : α) (chosen : List α) :
    FiniteSearch.count PermutationSearch.next 8 (chosen, List.replicate 8 x) = 40320 ∧
      (FiniteSearch.count PermutationSearch.next 8 (chosen, List.replicate 8 x)).log2 = 15 := by
  have hc : FiniteSearch.count PermutationSearch.next 8
      (chosen, List.replicate 8 x) = 40320 := by
    calc
      _ = Nat.factorial 8 := by
        simpa only [List.length_replicate] using
          PermutationSearch.count_factorial (List.replicate 8 x) chosen
      _ = 40320 := by decide
  exact ⟨hc, (congrArg Nat.log2 hc).trans (by decide)⟩

/-- Source C7 is recovered through the actual repeated-input counter. -/
theorem factorial_eight_log2 : (Nat.factorial 8).log2 = 15 := by
  have hc : FiniteSearch.count PermutationSearch.next 8
      (([] : List ℕ), List.replicate 8 7) = Nat.factorial 8 := by
    simpa only [List.length_replicate] using
      PermutationSearch.count_factorial (List.replicate 8 7) []
  calc
    (Nat.factorial 8).log2 =
        (FiniteSearch.count PermutationSearch.next 8
          (([] : List ℕ), List.replicate 8 7)).log2 := (congrArg Nat.log2 hc).symm
    _ = 15 := (permutation_repeated_eight (7 : ℕ) []).2

/-- Empty remaining input leaves the current prefix as the sole depth-zero occurrence. -/
theorem permutation_empty_count (chosen : List α) :
    FiniteSearch.count PermutationSearch.next 0 (chosen, []) = 1 ∧
      (FiniteSearch.count PermutationSearch.next 0 (chosen, [])).log2 = 0 := by
  have hc : FiniteSearch.count PermutationSearch.next 0 (chosen, []) = 1 :=
    PermutationSearch.count_factorial ([] : List α) chosen
  exact ⟨hc, (congrArg Nat.log2 hc).trans (by decide)⟩

/-- A repeated-input specialization also exercises the general finite count bounds. -/
example (x : α) (chosen : List α) :
    24 ≤ 6 * (FiniteSearch.count PermutationSearch.next 8
        (chosen, List.replicate 8 x)).log2 ∧
      (FiniteSearch.count PermutationSearch.next 8
        (chosen, List.replicate 8 x)).log2 ≤ 48 := by
  have h := permutation_count_log_bounds (List.replicate 8 x) chosen
    (by simpa only [List.length_replicate] using (show (4 : ℕ) ≤ 8 from by decide))
  have hl : (8 : ℕ).log2 = 3 := by decide
  simpa only [List.length_replicate, hl] using h

/-- Source C9 is a use of the general coefficient-eighteen bound at sixteen. -/
theorem weighted_sixteen_bound :
    (16 : ℕ) * 16 * (16 : ℕ).log2 ≤
      18 * (∑ k ∈ Ico 1 ((16 : ℕ) + 1), k * k.log2) :=
  (weighted_log_bounds 16 (by decide)).1

/-- Independent exact arithmetic for the positive weighted sum at sixteen. -/
theorem weighted_sixteen_value :
    (∑ k ∈ Ico 1 ((16 : ℕ) + 1), k * k.log2) = 389 := by
  decide

end Examples.DiscreteEstimates

/-!
Assembly fragment: append after r1-d1-d2/D2Cases.lean and NativeClients.lean
inside the assembled Examples.DiscreteEstimates module. This fragment imports
no module and is not a separate compilation target. Its dependencies are the
already drafted halfOffset definitions/membership proofs and native clients.
-/
namespace Examples.DiscreteEstimates
open Filter Asymptotics

/-- The log band really has a negative initial value, yet its native norm order is unchanged. -/
theorem negative_logBand_isTheta :
    halfOffsetLog (-7) =Θ[atTop] (fun n : ℕ => (Nat.log2 n : ℚ)) :=
  logBand_isTheta (halfOffsetLog_mem (-7))

/-- The independently chosen negative root prefix is admitted by the same native contract. -/
theorem negative_rootBand_isTheta :
    halfOffsetRoot (-3) =Θ[atTop] (fun n : ℕ => (Nat.sqrt n : ℚ)) :=
  rootBand_isTheta (halfOffsetRoot_mem (-3))

/-- The two negative-prefix functions specialize the actual product norm comparison. -/
theorem negative_bands_mul_isBigO :
    (fun n : ℕ => (n : ℚ) * halfOffsetLog (-7) n) =O[atTop]
      (fun n : ℕ => (n : ℚ) * halfOffsetRoot (-3) n) :=
  mul_logBand_isBigO_mul_rootBand (halfOffsetLog_mem (-7)) (halfOffsetRoot_mem (-3))

/-- Negative initial values also coexist with the fully quantified native norm failure. -/
theorem negative_bands_not_isBigO :
    ¬ ((fun n : ℕ => (n : ℚ) + halfOffsetRoot (-3) n) =O[atTop]
      (fun n : ℕ => halfOffsetRoot (-3) n * halfOffsetLog (-7) n)) :=
  linear_add_rootBand_not_isBigO_rootBand_mul_logBand
    (halfOffsetLog_mem (-7)) (halfOffsetRoot_mem (-3))

end Examples.DiscreteEstimates
