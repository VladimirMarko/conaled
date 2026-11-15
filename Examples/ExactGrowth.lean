import SquareKit.NonnegativeArithmetic
import SquareKit.ExactGrowthBounds
import Applications.Resources.Growth
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.NNReal.Basic

/-!
# Growth of partial exact arithmetic terms

All source comparisons use the existing partial value order. A bounded exact
coefficient is chosen once, before the eventual index. Standard norm growth is
connected only on a common event where both term families have actual finite values.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExactGrowth
open SquareKit.NonnegativeArithmetic Filter
open scoped NNReal
universe u

noncomputable section

/-- Section inclusion and strict natural scaling express the same native source
growth statement for arbitrary families, including invalid values. -/
theorem section_growth_iff_value_growth (f g : ℕ → ClosedTerm) :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (f n) ⊆ sectionOf (scale C (g n))) ↔
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      value (f n) ≤ WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (g n))) := by
  simp only [sectionOf_subset_iff, value_scale]

theorem value_growth_iff_threshold (f g : ℕ → ClosedTerm) :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      value (f n) ≤ WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (g n))) ↔
    (∃ C N : ℕ, 0 < C ∧ ∀ n, N ≤ n →
      value (f n) ≤ WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (g n))) := by
  constructor
  · rintro ⟨C, hC, h⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    exact ⟨C, N, hC, hN⟩
  · rintro ⟨C, N, hC, h⟩
    exact ⟨C, hC, eventually_atTop.mpr ⟨N, h⟩⟩

/-- The source two-sided comparison remains two independently chosen positive
natural coefficients, with no validity assumption and no custom Theta definition. -/
theorem section_theta_iff_value_theta (f g : ℕ → ClosedTerm) :
    ((∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
        sectionOf (f n) ⊆ sectionOf (scale C (g n))) ∧
      (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
        sectionOf (g n) ⊆ sectionOf (scale C (f n)))) ↔
    ((∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
        value (f n) ≤ WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (g n))) ∧
      (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
        value (g n) ≤ WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (f n)))) :=
  and_congr (section_growth_iff_value_growth f g) (section_growth_iff_value_growth g f)

/-- The source's concrete integer-ceiling coefficient dominates every strict
product, including an invalid right operand. No positivity premise on lo is needed. -/
theorem bounded_multiplier_dominated {c : ClosedTerm} {lo hi : ℚ}
    (hc : Bounded c lo hi) (e : ClosedTerm) :
    sectionOf (mul c e) ⊆ sectionOf (scale ((⌈hi⌉ : ℤ).natAbs + 1) e) := by
  apply le_of_approximants
  intro x hx
  rw [raw_mul] at hx
  rcases hx with ⟨a, ha, b, hb, rfl⟩
  have hahi : a ≤ hi := hc.2 ha
  have hceil : hi ≤ ((⌈hi⌉ : ℤ) : ℚ) := Int.le_ceil hi
  have habs : ((⌈hi⌉ : ℤ) : ℚ) ≤ (((⌈hi⌉ : ℤ).natAbs : ℕ) : ℚ) := by
    simpa only [Int.cast_natCast] using
      ((Int.cast_le (R := ℚ)).mpr (Int.le_natAbs (a := (⌈hi⌉ : ℤ))))
  have hnext : (((⌈hi⌉ : ℤ).natAbs : ℕ) : ℚ) ≤
      (((⌈hi⌉ : ℤ).natAbs + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.le_succ ((⌈hi⌉ : ℤ).natAbs)
  have haC := hahi.trans (hceil.trans (habs.trans hnext))
  refine ⟨((((⌈hi⌉ : ℤ).natAbs + 1 : ℕ) : ℚ) * b), ?_, ?_⟩
  · rw [raw_scale]
    exact Set.mem_image2_of_mem ⟨Nat.cast_nonneg _, le_rfl⟩ hb
  · exact mul_le_mul_of_nonneg_right haC (raw_nonneg e hb)

theorem bounded_multiplier_value_dominated {c : ClosedTerm} {lo hi : ℚ}
    (hc : Bounded c lo hi) (e : ClosedTerm) :
    strictMul (value c) (value e) ≤
      WithBot.map (fun x : ℝ≥0 => (((⌈hi⌉ : ℤ).natAbs + 1 : ℕ) : ℝ≥0) * x) (value e) := by
  have h := (sectionOf_subset_iff _ _).mp (bounded_multiplier_dominated hc e)
  simpa only [value_mul, value_scale] using h

/-- One bounded positive exact coefficient is fixed before the eventual index.
The equivalence holds for arbitrary term families, without eventual validity. -/
theorem growth_iff_exact_coefficient (f g : ℕ → ClosedTerm) :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      value (f n) ≤ WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (g n))) ↔
    (∃ c : ClosedTerm, ∃ lo hi : ℚ, Bounded c lo hi ∧ 0 < lo ∧
      ∃ N : ℕ, ∀ n, N ≤ n → value (f n) ≤ strictMul (value c) (value (g n))) := by
  constructor
  · rintro ⟨C, hC, h⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    refine ⟨rational (C : ℚ), (C : ℚ), (C : ℚ),
      bounded_rational _ (Nat.cast_nonneg C), Nat.cast_pos.mpr hC, N, ?_⟩
    intro n hn
    have hscale := hN n hn
    simpa only [value_rational, rationalValue_natCast, strictMul, WithBot.map₂_coe_left]
      using hscale
  · rintro ⟨c, lo, hi, hc, _hlo, N, hN⟩
    refine ⟨(⌈hi⌉ : ℤ).natAbs + 1, Nat.succ_pos _, eventually_atTop.mpr ⟨N, ?_⟩⟩
    intro n hn
    exact (hN n hn).trans (bounded_multiplier_value_dominated hc (g n))

/-- Actual finite values on a common eventual event connect the partial source
order to standard norm Big O. Finite exceptions do not change either side. -/
theorem value_growth_iff_isBigO {ι : Type u} {l : Filter ι}
    (f g : ι → ClosedTerm) (F G : ι → ℝ≥0)
    (hf : ∀ᶠ n in l, value (f n) = (F n : Value))
    (hg : ∀ᶠ n in l, value (g n) = (G n : Value)) :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in l,
      value (f n) ≤ WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (g n))) ↔
    (fun n => (F n : ℝ)) =O[l] (fun n => (G n : ℝ)) := by
  rw [Resources.isBigO_nnrealCast_iff]
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [h, hf, hg] with n hn hfn hgn
    simpa only [hfn, hgn, WithBot.map_coe, WithBot.coe_le_coe] using hn
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [h, hf, hg] with n hn hfn hgn
    simpa only [hfn, hgn, WithBot.map_coe, WithBot.coe_le_coe] using hn

theorem value_theta_iff_isTheta {ι : Type u} {l : Filter ι}
    (f g : ι → ClosedTerm) (F G : ι → ℝ≥0)
    (hf : ∀ᶠ n in l, value (f n) = (F n : Value))
    (hg : ∀ᶠ n in l, value (g n) = (G n : Value)) :
    ((∃ C : ℕ, 0 < C ∧ ∀ᶠ n in l,
        value (f n) ≤ WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (g n))) ∧
      (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in l,
        value (g n) ≤ WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (f n)))) ↔
    (fun n => (F n : ℝ)) =Θ[l] (fun n => (G n : ℝ)) :=
  and_congr (value_growth_iff_isBigO f g F G hf hg)
    (value_growth_iff_isBigO g f G F hg hf)

/-- Valid zero is not below an invalid scaled operand, for any coefficient. -/
theorem valid_zero_not_le_invalid (C : ℕ) :
    ¬ value (rational 0) ≤
      WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (logarithm 0)) := by
  simp [value_rational, rationalValue, value_logarithm, logarithmValue]

theorem valid_zero_not_growth_invalid :
    ¬ (∃ C : ℕ, 0 < C ∧ ∀ᶠ _n : ℕ in atTop,
      value (rational 0) ≤
        WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (logarithm 0))) := by
  rintro ⟨C, _hC, h⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  exact valid_zero_not_le_invalid C (hN N le_rfl)

/-- Replacing invalidity by zero loses the source order even for constant families. -/
theorem default_zero_counterexample :
    ((fun _ : ℕ => (0 : ℝ)) =O[atTop] (fun _ : ℕ => (0 : ℝ))) ∧
      ¬ (∃ C : ℕ, 0 < C ∧ ∀ᶠ _n : ℕ in atTop,
        value (rational 0) ≤
          WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (logarithm 0))) := by
  refine ⟨?_, valid_zero_not_growth_invalid⟩
  exact (Resources.isBigO_nnrealCast_iff (fun _ : ℕ => (0 : ℝ≥0))
    (fun _ : ℕ => (0 : ℝ≥0))).mpr ⟨1, by decide, Filter.Eventually.of_forall (by simp)⟩

/-- An irrational positive coefficient has actual raw, attained bounds. -/
theorem sqrt_two_coefficient_bounds : Bounded (squareRoot 2) (7 / 5) (10 / 7) := by
  constructor
  · exact ⟨7, 5, by decide, rfl, by decide⟩
  · intro a ha
    exact rootApprox_upper 2 10 7 (by decide) (by decide) ha

theorem sqrt_two_positive_coefficient :
    ∃ lo hi : ℚ, Bounded (squareRoot 2) lo hi ∧ 0 < lo :=
  ⟨7 / 5, 10 / 7, sqrt_two_coefficient_bounds, by norm_num⟩

end
end Examples.ExactGrowth
/-! Qualified zero-default observations and concrete irrational coefficients. -/

namespace Examples.ExactGrowth
open SquareKit.NonnegativeArithmetic Filter
open scoped NNReal
universe u

noncomputable section

theorem eventually_value_eq_default {ι : Type u} {l : Filter ι}
    (f : ι → ClosedTerm) (hf : ∀ᶠ n in l, value (f n) ≠ ⊥) :
    ∀ᶠ n in l, value (f n) = ((WithBot.unbotD (0 : ℝ≥0) (value (f n)) : ℝ≥0) : Value) := by
  filter_upwards [hf] with n hn
  cases h : value (f n) with
  | none => exact False.elim (hn h)
  | some v => rfl

/-- Zero defaults may be used outside the common validity event; equality with
the actual finite value on that event is proved explicitly. -/
theorem growth_iff_default_isBigO {ι : Type u} {l : Filter ι}
    (f g : ι → ClosedTerm)
    (hf : ∀ᶠ n in l, value (f n) ≠ ⊥) (hg : ∀ᶠ n in l, value (g n) ≠ ⊥) :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in l,
      value (f n) ≤ WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (g n))) ↔
    (fun n => ((WithBot.unbotD 0 (value (f n)) : ℝ≥0) : ℝ)) =O[l]
      (fun n => ((WithBot.unbotD 0 (value (g n)) : ℝ≥0) : ℝ)) :=
  value_growth_iff_isBigO f g _ _ (eventually_value_eq_default f hf)
    (eventually_value_eq_default g hg)

theorem actual_default_zero_counterexample :
    ((fun _ : ℕ => ((WithBot.unbotD 0 (value (rational 0)) : ℝ≥0) : ℝ)) =O[atTop]
      (fun _ : ℕ => ((WithBot.unbotD 0 (value (logarithm 0)) : ℝ≥0) : ℝ))) ∧
    ¬ (∃ C : ℕ, 0 < C ∧ ∀ᶠ _n : ℕ in atTop,
      value (rational 0) ≤
        WithBot.map (fun x : ℝ≥0 => (C : ℝ≥0) * x) (value (logarithm 0))) := by
  refine ⟨?_, valid_zero_not_growth_invalid⟩
  simpa [value_rational, rationalValue, value_logarithm, logarithmValue]
    using default_zero_counterexample.1

theorem unit_growth_with_irrational_coefficient :
    Bounded (squareRoot 2) (7 / 5) (10 / 7) ∧ (0 : ℚ) < 7 / 5 ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        value (rational 1) ≤ strictMul (value (squareRoot 2)) (value (rational 1)) := by
  refine ⟨sqrt_two_coefficient_bounds, by norm_num, 0, ?_⟩
  intro n _hn
  have hone : value (rational 1) = ((1 : ℝ≥0) : Value) := by
    simpa only [value_rational, Nat.cast_one] using rationalValue_natCast 1
  simp only [hone, value_squareRoot, squareRootValue, strictMul, WithBot.map₂_coe_coe,
    mul_one, WithBot.coe_le_coe]
  exact NNReal.le_sqrt_iff_sq_le.mpr (by norm_num)

/-- Exact attained bounds fix the actual partial value at a natural endpoint. -/
theorem value_of_exact_nat_bounds {e : ClosedTerm} {k : ℕ}
    (he : Bounded e (k : ℚ) (k : ℚ)) : value e = ((k : ℝ≥0) : Value) := by
  obtain ⟨x, hx, hlo, hhi⟩ := rel_bounds_real (raw_related e) he
  have heq : (x : ℝ) = (((k : ℚ) : ℝ)) := le_antisymm hhi hlo
  have hxk : x = (k : ℝ≥0) := NNReal.coe_injective (by
    simpa only [NNReal.coe_natCast, Rat.cast_natCast] using heq)
  simpa only [hxk] using hx

theorem finite64_left_value :
    value (add (rational 64) (squareRoot 64)) = ((72 : ℝ≥0) : Value) := by
  have hroot : Bounded (squareRoot 64) 8 8 := by
    simpa using bounded_root_square 8
  have h := bounded_add (bounded_rational 64 (by norm_num)) hroot
  have he : Bounded (add (rational 64) (squareRoot 64)) (72 : ℚ) 72 := by
    norm_num at h
    exact h
  exact value_of_exact_nat_bounds (k := 72) he

theorem finite64_right_bounds :
    Bounded (mul (squareRoot 2) (mul (squareRoot 64) (logarithm 64)))
      (336 / 5) (480 / 7) := by
  have hroot : Bounded (squareRoot 64) 8 8 := by
    simpa using bounded_root_square 8
  have hlog : Bounded (logarithm 64) 6 6 := by
    simpa using bounded_log_power 6
  have h := bounded_mul sqrt_two_coefficient_bounds (bounded_mul hroot hlog)
  norm_num at h
  exact h

/-- A finite discriminating witness. This does not assert the deferred universal
growth counterfamily for arbitrary coefficients and thresholds. -/
theorem finite64_irrational_coefficient_fails :
    ∃ x : ℝ≥0,
      value (mul (squareRoot 2) (mul (squareRoot 64) (logarithm 64))) = (x : Value) ∧
      (x : ℝ) ≤ 480 / 7 ∧ (480 / 7 : ℝ) < 72 ∧
      ¬ value (add (rational 64) (squareRoot 64)) ≤
        value (mul (squareRoot 2) (mul (squareRoot 64) (logarithm 64))) := by
  obtain ⟨x, hx, _hlo, hhi⟩ :=
    rel_bounds_real (raw_related _) finite64_right_bounds
  have hupper : (x : ℝ) ≤ 480 / 7 := by norm_num at hhi; exact hhi
  refine ⟨x, hx, hupper, by norm_num, ?_⟩
  intro h
  rw [finite64_left_value, hx] at h
  have hreal := NNReal.coe_le_coe.mpr (WithBot.coe_le_coe.mp h)
  norm_num at hreal
  linarith

end
end Examples.ExactGrowth

/-! The seven native syntax families and the positive-fold value bridge. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExactGrowth
open SquareKit.NonnegativeArithmetic Filter
open scoped NNReal BigOperators

noncomputable section

def nLog (n : ℕ) : ClosedTerm := scale n (logarithm n)
def nRoot (n : ℕ) : ClosedTerm := scale n (squareRoot n)
def nPlusRoot (n : ℕ) : ClosedTerm := add (rational n) (squareRoot n)
def rootLog (n : ℕ) : ClosedTerm := mul (squareRoot n) (logarithm n)
def nSquareLog (n : ℕ) : ClosedTerm := scale (n * n) (logarithm n)
def cubicLowerTerms (n : ℕ) : ClosedTerm :=
  add (add (rational (n * n * n)) (rational (n * n))) (nLog n)
def weightedLogExpr (n : ℕ) : ClosedTerm :=
  (List.range n).foldl
    (fun acc j => add acc (scale (j + 1) (logarithm (j + 1)))) (rational 0)

theorem weightedLogExpr_zero : weightedLogExpr 0 = rational 0 := rfl

/-- Appending the next positive index preserves the source association. -/
theorem weightedLogExpr_succ (n : ℕ) :
    weightedLogExpr (n + 1) =
      add (weightedLogExpr n) (scale (n + 1) (logarithm (n + 1))) := by
  simp only [weightedLogExpr, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem value_nLog (n : ℕ) (hn : 1 ≤ n) :
    value (nLog n) =
      (((n : ℝ≥0) * Real.toNNReal (Real.logb 2 (n : ℝ)) : ℝ≥0) : Value) := by
  have hn0 : n ≠ 0 := by omega
  simp only [nLog, value_scale, value_logarithm, logarithmValue,
    ite_eq_right hn0, WithBot.map_coe]

theorem value_nRoot (n : ℕ) :
    value (nRoot n) = (((n : ℝ≥0) * NNReal.sqrt (n : ℝ≥0) : ℝ≥0) : Value) := by
  simp only [nRoot, value_scale, value_squareRoot, squareRootValue, WithBot.map_coe]

theorem value_nPlusRoot (n : ℕ) :
    value (nPlusRoot n) = (((n : ℝ≥0) + NNReal.sqrt (n : ℝ≥0) : ℝ≥0) : Value) := by
  simp only [nPlusRoot, value_add, value_rational, rationalValue_natCast,
    value_squareRoot, squareRootValue, strictAdd, WithBot.map₂_coe_coe]

theorem value_rootLog (n : ℕ) (hn : 1 ≤ n) :
    value (rootLog n) =
      ((NNReal.sqrt (n : ℝ≥0) * Real.toNNReal (Real.logb 2 (n : ℝ)) : ℝ≥0) : Value) := by
  have hn0 : n ≠ 0 := by omega
  simp only [rootLog, value_mul, value_squareRoot, squareRootValue,
    value_logarithm, logarithmValue, ite_eq_right hn0, strictMul,
    WithBot.map₂_coe_coe]

theorem value_nSquareLog (n : ℕ) (hn : 1 ≤ n) :
    value (nSquareLog n) =
      ((((n * n : ℕ) : ℝ≥0) * Real.toNNReal (Real.logb 2 (n : ℝ)) : ℝ≥0) : Value) := by
  have hn0 : n ≠ 0 := by omega
  simp only [nSquareLog, value_scale, value_logarithm, logarithmValue,
    ite_eq_right hn0, WithBot.map_coe]

theorem value_nLog_eq_bot_iff (n : ℕ) : value (nLog n) = ⊥ ↔ n = 0 := by
  rw [nLog, value_scale_eq_bot_iff, value_logarithm]
  by_cases hn : n = 0 <;> simp [logarithmValue, hn]

theorem value_nSquareLog_eq_bot_iff (n : ℕ) : value (nSquareLog n) = ⊥ ↔ n = 0 := by
  rw [nSquareLog, value_scale_eq_bot_iff, value_logarithm]
  by_cases hn : n = 0 <;> simp [logarithmValue, hn]

theorem value_rootLog_eq_bot_iff (n : ℕ) : value (rootLog n) = ⊥ ↔ n = 0 := by
  simp only [rootLog, value_mul, strictMul_eq_bot_iff, value_squareRoot,
    squareRootValue, WithBot.coe_ne_bot, false_or, value_logarithm]
  by_cases hn : n = 0 <;> simp [logarithmValue, hn]

theorem value_cubicLowerTerms_eq_bot_iff (n : ℕ) :
    value (cubicLowerTerms n) = ⊥ ↔ n = 0 := by
  have hs : (0 : ℚ) ≤ (n : ℚ) * (n : ℚ) := by positivity
  have hc : (0 : ℚ) ≤ (n : ℚ) * (n : ℚ) * (n : ℚ) := by positivity
  simp only [cubicLowerTerms, value_add, strictAdd_eq_bot_iff, value_rational,
    rationalValue, ite_eq_left hs, ite_eq_left hc,
    WithBot.coe_ne_bot, false_or, value_nLog_eq_bot_iff]

theorem value_nRoot_ne_bot (n : ℕ) : value (nRoot n) ≠ ⊥ := by
  rw [value_nRoot]
  exact WithBot.coe_ne_bot

theorem value_nPlusRoot_ne_bot (n : ℕ) : value (nPlusRoot n) ≠ ⊥ := by
  rw [value_nPlusRoot]
  exact WithBot.coe_ne_bot

/-- All rational queries are characterized by the actual finite payload. -/
theorem sectionOf_iff_of_finite_value (e : ClosedTerm) (v : ℝ≥0)
    (he : value e = (v : Value)) (q : ℚ) :
    q ∈ sectionOf e ↔ (q : ℝ) ≤ (v : ℝ) := by
  rw [mem_sectionOf_iff, he]
  constructor
  · rintro ⟨x, hx, hq⟩
    have hvx : v = x := WithBot.coe_injective hx
    simpa only [hvx] using hq
  · intro hq
    exact ⟨v, rfl, hq⟩

/-- The mathematical payload sum uses the same positive indices as the syntax fold. -/
theorem value_weightedLogExpr_sum (n : ℕ) :
    value (weightedLogExpr n) =
      ((∑ k ∈ Finset.Ico 1 (n + 1),
        (k : ℝ≥0) * Real.toNNReal (Real.logb 2 (k : ℝ)) : ℝ≥0) : Value) := by
  induction n with
  | zero => simp [weightedLogExpr_zero, rationalValue]
  | succ n ih =>
    have hn0 : n + 1 ≠ 0 := by omega
    rw [weightedLogExpr_succ, value_add, ih, value_scale, value_logarithm,
      logarithmValue, ite_eq_right hn0, WithBot.map_coe, strictAdd,
      WithBot.map₂_coe_coe,
      Finset.sum_Ico_succ_top (a := 1) (b := n + 1) (by omega)]

/-- The real-valued range input used by the scanner equals the positive Ico sum. -/
theorem weighted_log_range_eq_Ico (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) * Real.logb 2 (j + 1)) =
      ∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 k := by
  symm
  simpa [Nat.add_comm] using
    (Finset.sum_Ico_eq_sum_range (fun k : ℕ => (k : ℝ) * Real.logb 2 k) 1 (n + 1))

/-- Actual finite payload and exact real value, including the empty fold. -/
theorem value_weightedLogExpr (n : ℕ) :
    ∃ v : ℝ≥0, value (weightedLogExpr n) = (v : Value) ∧
      (v : ℝ) = ∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 k := by
  refine ⟨∑ k ∈ Finset.Ico 1 (n + 1),
    (k : ℝ≥0) * Real.toNNReal (Real.logb 2 (k : ℝ)), value_weightedLogExpr_sum n, ?_⟩
  rw [NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hlog : 0 ≤ Real.logb 2 (k : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hk1)
  simp only [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ hlog]

theorem section_weightedLogExpr (n : ℕ) (q : ℚ) :
    q ∈ sectionOf (weightedLogExpr n) ↔
      (q : ℝ) ≤ ∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 k := by
  obtain ⟨v, hv, hreal⟩ := value_weightedLogExpr n
  rw [sectionOf_iff_of_finite_value _ v hv q, hreal]

theorem value_weightedLogExpr_ne_bot (n : ℕ) : value (weightedLogExpr n) ≠ ⊥ := by
  obtain ⟨v, hv, _⟩ := value_weightedLogExpr n
  rw [hv]
  exact WithBot.coe_ne_bot

/-! The zero cases distinguish partial syntax from a totalized real formula. -/

theorem initial_family_domains :
    value (nLog 0) = ⊥ ∧ value (rootLog 0) = ⊥ ∧
      value (nSquareLog 0) = ⊥ ∧ value (cubicLowerTerms 0) = ⊥ ∧
      value (nRoot 0) = ((0 : ℝ≥0) : Value) ∧
      value (nPlusRoot 0) = ((0 : ℝ≥0) : Value) ∧
      value (weightedLogExpr 0) = ((0 : ℝ≥0) : Value) := by
  refine ⟨(value_nLog_eq_bot_iff 0).mpr rfl,
    (value_rootLog_eq_bot_iff 0).mpr rfl,
    (value_nSquareLog_eq_bot_iff 0).mpr rfl,
    (value_cubicLowerTerms_eq_bot_iff 0).mpr rfl, ?_, ?_, ?_⟩
  · simp only [value_nRoot, Nat.cast_zero, NNReal.sqrt_zero, zero_mul]
  · simp only [value_nPlusRoot, Nat.cast_zero, NNReal.sqrt_zero, zero_add]
  · rw [weightedLogExpr_zero, value_rational]
    simpa only [Nat.cast_zero] using rationalValue_natCast 0

theorem weighted_empty_section (q : ℚ) :
    q ∈ sectionOf (weightedLogExpr 0) ↔ q ≤ 0 := by
  rw [weightedLogExpr_zero]
  exact rational_section_iff 0 q (by norm_num)

end
end Examples.ExactGrowth

/-! Actual real meanings, attained weighted bounds and the existing norm bridge. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExactGrowth
open SquareKit.NonnegativeArithmetic Filter
open scoped NNReal BigOperators

noncomputable section

theorem rational_value_real (r : ℚ) (hr : 0 ≤ r) :
    ∃ v : ℝ≥0, value (rational r) = (v : Value) ∧ (v : ℝ) = (r : ℝ) := by
  obtain ⟨v, hv, hlo, hhi⟩ :=
    rel_bounds_real (raw_related (rational r)) (bounded_rational r hr)
  exact ⟨v, hv, le_antisymm hhi hlo⟩

theorem rational_nat_value_real (n : ℕ) :
    ∃ v : ℝ≥0, value (rational (n : ℚ)) = (v : Value) ∧ (v : ℝ) = (n : ℝ) := by
  obtain ⟨v, hv, hreal⟩ := rational_value_real (n : ℚ) (Nat.cast_nonneg n)
  exact ⟨v, hv, by simpa only [Rat.cast_natCast] using hreal⟩

theorem logarithm_value_real (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : ℝ≥0, value (logarithm n) = (v : Value) ∧
      (v : ℝ) = Real.logb 2 (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn)
  refine ⟨Real.toNNReal (Real.logb 2 (n : ℝ)), ?_, Real.coe_toNNReal _ hlog⟩
  simp only [value_logarithm, logarithmValue, ite_eq_right hn0]

theorem nLog_value_real (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : ℝ≥0, value (nLog n) = (v : Value) ∧
      (v : ℝ) = (n : ℝ) * Real.logb 2 (n : ℝ) := by
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn)
  refine ⟨(n : ℝ≥0) * Real.toNNReal (Real.logb 2 (n : ℝ)), value_nLog n hn, ?_⟩
  simp only [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ hlog]

theorem nRoot_value_real (n : ℕ) :
    ∃ v : ℝ≥0, value (nRoot n) = (v : Value) ∧
      (v : ℝ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
  refine ⟨(n : ℝ≥0) * NNReal.sqrt (n : ℝ≥0), value_nRoot n, ?_⟩
  simp only [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_sqrt]

theorem nPlusRoot_value_real (n : ℕ) :
    ∃ v : ℝ≥0, value (nPlusRoot n) = (v : Value) ∧
      (v : ℝ) = (n : ℝ) + Real.sqrt (n : ℝ) := by
  refine ⟨(n : ℝ≥0) + NNReal.sqrt (n : ℝ≥0), value_nPlusRoot n, ?_⟩
  simp only [NNReal.coe_add, NNReal.coe_natCast, Real.coe_sqrt]

theorem rootLog_value_real (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : ℝ≥0, value (rootLog n) = (v : Value) ∧
      (v : ℝ) = Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ) := by
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn)
  refine ⟨NNReal.sqrt (n : ℝ≥0) * Real.toNNReal (Real.logb 2 (n : ℝ)),
    value_rootLog n hn, ?_⟩
  simp only [NNReal.coe_mul, Real.coe_sqrt, NNReal.coe_natCast,
    Real.coe_toNNReal _ hlog]

theorem nSquareLog_value_real (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : ℝ≥0, value (nSquareLog n) = (v : Value) ∧
      (v : ℝ) = (n : ℝ) ^ 2 * Real.logb 2 (n : ℝ) := by
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn)
  refine ⟨((n * n : ℕ) : ℝ≥0) * Real.toNNReal (Real.logb 2 (n : ℝ)),
    value_nSquareLog n hn, ?_⟩
  simp only [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ hlog,
    Nat.cast_mul, pow_two]

theorem harmonic_value_real (n : ℕ) :
    ∃ v : ℝ≥0, value (rational (harmonic n)) = (v : Value) ∧
      (v : ℝ) = (harmonic n : ℝ) :=
  rational_value_real (harmonic n) (SquareKit.HarmonicBounds.harmonic_nonneg n)

theorem n_harmonic_value_real (n : ℕ) :
    ∃ v : ℝ≥0, value (rational ((n : ℚ) * harmonic n)) = (v : Value) ∧
      (v : ℝ) = (n : ℝ) * (harmonic n : ℝ) := by
  obtain ⟨v, hv, hreal⟩ := rational_value_real ((n : ℚ) * harmonic n)
    (mul_nonneg (Nat.cast_nonneg n) (SquareKit.HarmonicBounds.harmonic_nonneg n))
  exact ⟨v, hv, by simpa only [Rat.cast_mul, Rat.cast_natCast] using hreal⟩

theorem factorial_log_value_real (n : ℕ) :
    ∃ v : ℝ≥0, value (logarithm (Nat.factorial n)) = (v : Value) ∧
      (v : ℝ) = Real.logb 2 (Nat.factorial n : ℝ) :=
  logarithm_value_real (Nat.factorial n) (Nat.factorial_pos n)

theorem exponentiatedLogarithm_value_real (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : ℝ≥0, value (exponentiatedLogarithm n) = (v : Value) ∧
      (v : ℝ) = (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  refine ⟨(n : ℝ≥0), ?_, ?_⟩
  · simp only [value_exponentiatedLogarithm, exponentiatedLogarithmValue,
      ite_eq_right hn0]
  · exact NNReal.coe_natCast n

theorem exponentiatedLogarithm_value_rpow (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : ℝ≥0, value (exponentiatedLogarithm n) = (v : Value) ∧
      (v : ℝ) = (2 : ℝ) ^ Real.logb 2 (n : ℝ) := by
  obtain ⟨v, hv, hreal⟩ := exponentiatedLogarithm_value_real n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp : (2 : ℝ) ^ Real.logb 2 (n : ℝ) = (n : ℝ) :=
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hnR
  exact ⟨v, hv, hreal.trans hp.symm⟩

theorem cubic_rational_value_real (n : ℕ) :
    ∃ v : ℝ≥0, value (rational ((n * n * n : ℕ) : ℚ)) = (v : Value) ∧
      (v : ℝ) = (n : ℝ) ^ 3 := by
  obtain ⟨v, hv, hreal⟩ := rational_nat_value_real (n * n * n)
  refine ⟨v, hv, ?_⟩
  rw [hreal]
  push_cast
  ring

theorem cubicLowerTerms_value_real (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : ℝ≥0, value (cubicLowerTerms n) = (v : Value) ∧
      (v : ℝ) = (n : ℝ) ^ 3 + (n : ℝ) ^ 2 + (n : ℝ) * Real.logb 2 (n : ℝ) := by
  obtain ⟨a, ha, har⟩ := rational_value_real
    ((n : ℚ) * (n : ℚ) * (n : ℚ)) (by positivity)
  obtain ⟨b, hb, hbr⟩ := rational_value_real ((n : ℚ) * (n : ℚ)) (by positivity)
  obtain ⟨v, hv, hvr⟩ := nLog_value_real n hn
  refine ⟨a + b + v, ?_, ?_⟩
  · simp only [cubicLowerTerms, value_add, ha, hb, hv, strictAdd,
      WithBot.map₂_coe_coe]
  · simp only [NNReal.coe_add, har, hbr, hvr]
    push_cast
    ring

/-- The lower endpoint is a member of the actual compiled raw interpretation. -/
theorem weighted_expression_bounds (n : ℕ) :
    Bounded (weightedLogExpr n)
      ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℚ)
      (2 * ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℚ)) := by
  induction n with
  | zero => simpa [weightedLogExpr_zero] using bounded_rational 0 (by norm_num)
  | succ n ih =>
    have hb := bounded_add ih (bounded_scale (n + 1)
      (SquareKit.ExactGrowthBounds.bounded_log_twice_floor (n + 1) (by omega)))
    have hstep : (∑ k ∈ Finset.Ico 1 (n + 1 + 1), k * Nat.log2 k) =
        (∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k) + (n + 1) * Nat.log2 (n + 1) :=
      Finset.sum_Ico_succ_top (a := 1) (b := n + 1) (by omega) _
    have he : ((∑ k ∈ Finset.Ico 1 (n + 1 + 1), k * Nat.log2 k : ℕ) : ℚ) =
        ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℚ) +
          ((n + 1 : ℕ) : ℚ) * (Nat.log2 (n + 1) : ℚ) := by
      rw [hstep]
      simp only [Nat.cast_add, Nat.cast_mul]
    simp only [weightedLogExpr_succ, he]
    convert hb using 1
    ring

/-- Transport an actual finite real comparison through the accepted value/section iff. -/
theorem section_scale_of_real_values (e f : ClosedTerm) (F G : ℝ) (C : ℕ)
    (he : ∃ x : ℝ≥0, value e = (x : Value) ∧ (x : ℝ) = F)
    (hf : ∃ y : ℝ≥0, value f = (y : Value) ∧ (y : ℝ) = G)
    (hFG : F ≤ (C : ℝ) * G) :
    sectionOf e ⊆ sectionOf (scale C f) := by
  obtain ⟨x, hx, hxF⟩ := he
  obtain ⟨y, hy, hyG⟩ := hf
  apply (sectionOf_subset_iff _ _).mpr
  rw [hx, value_scale, hy, WithBot.map_coe]
  apply WithBot.coe_le_coe.mpr
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, hxF, hyG] using hFG

/-- Both eventual finite-value equalities are needed to identify the displayed
real functions. The defaults are explicitly NNReal and used only off that event. -/
theorem section_growth_iff_real_isBigO (f g : ℕ → ClosedTerm) (F G : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, ∃ x : ℝ≥0, value (f n) = (x : Value) ∧ (x : ℝ) = F n)
    (hg : ∀ᶠ n in atTop, ∃ y : ℝ≥0, value (g n) = (y : Value) ∧ (y : ℝ) = G n) :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (f n) ⊆ sectionOf (scale C (g n))) ↔ F =O[atTop] G := by
  let fv : ℕ → ℝ≥0 := fun n => WithBot.unbotD (0 : ℝ≥0) (value (f n))
  let gv : ℕ → ℝ≥0 := fun n => WithBot.unbotD (0 : ℝ≥0) (value (g n))
  have hfv : ∀ᶠ n in atTop, value (f n) = (fv n : Value) := by
    filter_upwards [hf] with n hn
    obtain ⟨x, hx, _⟩ := hn
    simp only [fv, hx, WithBot.unbotD_coe]
  have hgv : ∀ᶠ n in atTop, value (g n) = (gv n : Value) := by
    filter_upwards [hg] with n hn
    obtain ⟨y, hy, _⟩ := hn
    simp only [gv, hy, WithBot.unbotD_coe]
  have hfr : (fun n => (fv n : ℝ)) =ᶠ[atTop] F := by
    filter_upwards [hf] with n hn
    obtain ⟨x, hx, hreal⟩ := hn
    simpa only [fv, hx, WithBot.unbotD_coe] using hreal
  have hgr : (fun n => (gv n : ℝ)) =ᶠ[atTop] G := by
    filter_upwards [hg] with n hn
    obtain ⟨y, hy, hreal⟩ := hn
    simpa only [gv, hy, WithBot.unbotD_coe] using hreal
  exact (section_growth_iff_value_growth f g).trans
    ((value_growth_iff_isBigO f g fv gv hfv hgv).trans (Asymptotics.isBigO_congr hfr hgr))

theorem weighted_zero_raw_bounds : Bounded (weightedLogExpr 0) 0 0 := by
  simpa using weighted_expression_bounds 0

theorem weighted_one_raw_bounds : Bounded (weightedLogExpr 1) 0 0 := by
  have hsum : (∑ k ∈ Finset.Ico 1 (1 + 1), k * Nat.log2 k : ℕ) = 0 := by decide
  simpa only [hsum, Nat.cast_zero, mul_zero] using weighted_expression_bounds 1

end
end Examples.ExactGrowth

/-! Source finite witnesses and eventual exact-section comparisons. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExactGrowth
open SquareKit.NonnegativeArithmetic Filter
open scoped NNReal BigOperators

noncomputable section

theorem n_log_n_root_section_bound (n : ℕ) (hn : 16 ≤ n) :
    sectionOf (nLog n) ⊆ sectionOf (scale 2 (nRoot n)) :=
  section_scale_of_real_values _ _ _ _ 2
    (nLog_value_real n (by omega)) (nRoot_value_real n)
    (SquareKit.ExactGrowthBounds.n_log_le_two_n_sqrt n hn)

theorem harmonic_log_section_bounds (n : ℕ) (hn : 2 ≤ n) :
    (sectionOf (rational (harmonic n)) ⊆ sectionOf (scale 3 (logarithm n))) ∧
      (sectionOf (logarithm n) ⊆ sectionOf (scale 4 (rational (harmonic n)))) := by
  have hb := SquareKit.ExactGrowthBounds.harmonic_logb_coefficients n hn
  exact ⟨section_scale_of_real_values _ _ _ _ 3
      (harmonic_value_real n) (logarithm_value_real n (by omega)) hb.1,
    section_scale_of_real_values _ _ _ _ 4
      (logarithm_value_real n (by omega)) (harmonic_value_real n) hb.2⟩

theorem n_harmonic_n_log_section_bounds (n : ℕ) (hn : 2 ≤ n) :
    (sectionOf (rational ((n : ℚ) * harmonic n)) ⊆ sectionOf (scale 3 (nLog n))) ∧
      (sectionOf (nLog n) ⊆ sectionOf (scale 4 (rational ((n : ℚ) * harmonic n)))) := by
  have hb := SquareKit.ExactGrowthBounds.mul_harmonic_logb_coefficients n hn
  exact ⟨section_scale_of_real_values _ _ _ _ 3
      (n_harmonic_value_real n) (nLog_value_real n (by omega)) hb.1,
    section_scale_of_real_values _ _ _ _ 4
      (nLog_value_real n (by omega)) (n_harmonic_value_real n) hb.2⟩

theorem exponentiated_log_linear_section_bound (n : ℕ) (hn : 1 ≤ n) :
    sectionOf (exponentiatedLogarithm n) ⊆ sectionOf (scale 1 (rational (n : ℚ))) :=
  section_scale_of_real_values _ _ _ _ 1
    (exponentiatedLogarithm_value_real n hn) (rational_nat_value_real n) (by simp)

/-- The finite source constants are four and twelve from four onward. -/
theorem factorial_log_section_bounds (n : ℕ) (hn : 4 ≤ n) :
    (sectionOf (logarithm (Nat.factorial n)) ⊆ sectionOf (scale 4 (nLog n))) ∧
      (sectionOf (nLog n) ⊆ sectionOf (scale 12 (logarithm (Nat.factorial n)))) := by
  have hb := SquareKit.ExactGrowthBounds.factorial_logb_coefficients n hn
  exact ⟨section_scale_of_real_values _ _ _ _ 4
      (factorial_log_value_real n) (nLog_value_real n (by omega)) hb.1,
    section_scale_of_real_values _ _ _ _ 12
      (nLog_value_real n (by omega)) (factorial_log_value_real n) hb.2⟩

theorem weighted_log_section_bounds (n : ℕ) (hn : 4 ≤ n) :
    (sectionOf (weightedLogExpr n) ⊆ sectionOf (scale 2 (nSquareLog n))) ∧
      (sectionOf (nSquareLog n) ⊆ sectionOf (scale 36 (weightedLogExpr n))) := by
  have hb := SquareKit.ExactGrowthBounds.weighted_logb_coefficients n hn
  exact ⟨section_scale_of_real_values _ _ _ _ 2
      (value_weightedLogExpr n) (nSquareLog_value_real n (by omega)) hb.1,
    section_scale_of_real_values _ _ _ _ 36
      (nSquareLog_value_real n (by omega)) (value_weightedLogExpr n) hb.2⟩

theorem cubic_section_bounds (n : ℕ) (hn : 1 ≤ n) :
    (sectionOf (cubicLowerTerms n) ⊆
      sectionOf (scale 6 (rational ((n * n * n : ℕ) : ℚ)))) ∧
      (sectionOf (rational ((n * n * n : ℕ) : ℚ)) ⊆
        sectionOf (scale 1 (cubicLowerTerms n))) := by
  have hb := SquareKit.ExactGrowthBounds.cubic_logb_coefficients n hn
  refine ⟨section_scale_of_real_values _ _ _ _ 6
    (cubicLowerTerms_value_real n hn) (cubic_rational_value_real n) hb.1, ?_⟩
  apply section_scale_of_real_values _ _ _ _ 1
    (cubic_rational_value_real n) (cubicLowerTerms_value_real n hn)
  simpa only [Nat.cast_one, one_mul] using hb.2

theorem exact_n_log_bigO_n_sqrt :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (nLog n) ⊆ sectionOf (scale C (nRoot n)) :=
  ⟨2, by decide, eventually_atTop.mpr ⟨16, n_log_n_root_section_bound⟩⟩

/-- Every proposed natural coefficient fails beyond every proposed threshold.
The witness comes from the symbolic discrete power-square counterfamily. -/
theorem exact_linear_plus_sqrt_not_bigO :
    ¬ (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (nPlusRoot n) ⊆ sectionOf (scale C (rootLog n))) := by
  rintro ⟨C, hC, h⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  obtain ⟨n, hn, hcounter⟩ :=
    SquareKit.ExactGrowthBounds.linear_plus_sqrt_counterexample C hC (max N 1)
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  obtain ⟨x, hx, hxR⟩ := nPlusRoot_value_real n
  obtain ⟨y, hy, hyR⟩ := rootLog_value_real n hn1
  have hvalue := (sectionOf_subset_iff _ _).mp (hN n hnN)
  rw [hx, value_scale, hy, WithBot.map_coe] at hvalue
  have hreal := NNReal.coe_le_coe.mpr (WithBot.coe_le_coe.mp hvalue)
  simp only [NNReal.coe_mul, NNReal.coe_natCast, hxR, hyR] at hreal
  exact (not_le_of_gt hcounter) hreal

/-- The exact coefficient and its finite positive bounds are fixed before N. -/
theorem exact_linear_plus_sqrt_not_bigO_any_finite_coefficient :
    ¬ (∃ c : ClosedTerm, ∃ lo hi : ℚ, Bounded c lo hi ∧ 0 < lo ∧
      ∃ N : ℕ, ∀ n, N ≤ n →
        value (nPlusRoot n) ≤ strictMul (value c) (value (rootLog n))) := by
  intro h
  have hnat := (growth_iff_exact_coefficient nPlusRoot rootLog).mpr h
  exact exact_linear_plus_sqrt_not_bigO
    ((section_growth_iff_value_growth nPlusRoot rootLog).mpr hnat)

/-- The same unrestricted fixed-coefficient refutation stated directly for cuts. -/
theorem exact_linear_plus_sqrt_not_section_coefficient :
    ¬ (∃ c : ClosedTerm, ∃ lo hi : ℚ, Bounded c lo hi ∧ 0 < lo ∧
      ∃ N : ℕ, ∀ n, N ≤ n →
        sectionOf (nPlusRoot n) ⊆ sectionOf (mul c (rootLog n))) := by
  rintro ⟨c, lo, hi, hc, hlo, N, hN⟩
  apply exact_linear_plus_sqrt_not_bigO_any_finite_coefficient
  refine ⟨c, lo, hi, hc, hlo, N, ?_⟩
  intro n hn
  have h := (sectionOf_subset_iff _ _).mp (hN n hn)
  simpa only [value_mul] using h

theorem exact_harmonic_theta_log :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (rational (harmonic n)) ⊆ sectionOf (scale C (logarithm n))) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (logarithm n) ⊆ sectionOf (scale C (rational (harmonic n)))) :=
  ⟨⟨3, by decide, eventually_atTop.mpr ⟨2, fun n hn =>
      (harmonic_log_section_bounds n hn).1⟩⟩,
    ⟨4, by decide, eventually_atTop.mpr ⟨2, fun n hn =>
      (harmonic_log_section_bounds n hn).2⟩⟩⟩

theorem exact_n_harmonic_theta_n_log :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      sectionOf (rational ((n : ℚ) * harmonic n)) ⊆ sectionOf (scale C (nLog n))) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      sectionOf (nLog n) ⊆ sectionOf (scale C (rational ((n : ℚ) * harmonic n)))) :=
  ⟨⟨3, by decide, eventually_atTop.mpr ⟨2, fun n hn =>
      (n_harmonic_n_log_section_bounds n hn).1⟩⟩,
    ⟨4, by decide, eventually_atTop.mpr ⟨2, fun n hn =>
      (n_harmonic_n_log_section_bounds n hn).2⟩⟩⟩

theorem exact_exponentiated_log_bigO_linear :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (exponentiatedLogarithm n) ⊆ sectionOf (scale C (rational (n : ℚ))) :=
  ⟨1, by decide, eventually_atTop.mpr ⟨1, exponentiated_log_linear_section_bound⟩⟩

theorem exact_factorial_log_theta_n_log :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (logarithm (Nat.factorial n)) ⊆ sectionOf (scale C (nLog n))) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (nLog n) ⊆ sectionOf (scale C (logarithm (Nat.factorial n)))) :=
  ⟨⟨4, by decide, eventually_atTop.mpr ⟨4, fun n hn =>
      (factorial_log_section_bounds n hn).1⟩⟩,
    ⟨12, by decide, eventually_atTop.mpr ⟨4, fun n hn =>
      (factorial_log_section_bounds n hn).2⟩⟩⟩

theorem exact_weighted_log_theta_n_square_log :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (weightedLogExpr n) ⊆ sectionOf (scale C (nSquareLog n))) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (nSquareLog n) ⊆ sectionOf (scale C (weightedLogExpr n))) :=
  ⟨⟨2, by decide, eventually_atTop.mpr ⟨4, fun n hn =>
      (weighted_log_section_bounds n hn).1⟩⟩,
    ⟨36, by decide, eventually_atTop.mpr ⟨4, fun n hn =>
      (weighted_log_section_bounds n hn).2⟩⟩⟩

theorem exact_cubic_lower_terms_theta :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (cubicLowerTerms n) ⊆
        sectionOf (scale C (rational ((n * n * n : ℕ) : ℚ)))) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (rational ((n * n * n : ℕ) : ℚ)) ⊆
        sectionOf (scale C (cubicLowerTerms n))) :=
  ⟨⟨6, by decide, eventually_atTop.mpr ⟨1, fun n hn =>
      (cubic_section_bounds n hn).1⟩⟩,
    ⟨1, by decide, eventually_atTop.mpr ⟨1, fun n hn =>
      (cubic_section_bounds n hn).2⟩⟩⟩

/-! Five selected source cases remain explicit consumers of the general claims. -/

theorem source_case_n_log_bigO_n_root :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (nLog n) ⊆ sectionOf (scale C (nRoot n)) :=
  exact_n_log_bigO_n_sqrt

theorem source_case_no_fixed_exact_coefficient :
    ¬ (∃ c : ClosedTerm, ∃ lo hi : ℚ, Bounded c lo hi ∧ 0 < lo ∧
      ∃ N : ℕ, ∀ n, N ≤ n →
        sectionOf (nPlusRoot n) ⊆ sectionOf (mul c (rootLog n))) :=
  exact_linear_plus_sqrt_not_section_coefficient

theorem source_case_harmonic_theta_log :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (rational (harmonic n)) ⊆ sectionOf (scale C (logarithm n))) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (logarithm n) ⊆ sectionOf (scale C (rational (harmonic n)))) :=
  exact_harmonic_theta_log

theorem source_case_factorial_log_theta_n_log :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (logarithm (Nat.factorial n)) ⊆ sectionOf (scale C (nLog n))) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (nLog n) ⊆ sectionOf (scale C (logarithm (Nat.factorial n)))) :=
  exact_factorial_log_theta_n_log

theorem source_case_weighted_log_theta_n_square_log :
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (weightedLogExpr n) ⊆ sectionOf (scale C (nSquareLog n))) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
      sectionOf (nSquareLog n) ⊆ sectionOf (scale C (weightedLogExpr n))) :=
  exact_weighted_log_theta_n_square_log

end
end Examples.ExactGrowth

/-! Standard real norm corollaries of the exact-section claims.

Each transport supplies actual eventual finite values for both operands.
The positive-index events identify partial logarithmic expressions with their
displayed real functions without asserting a valid logarithmic term at zero.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExactGrowth
open SquareKit.NonnegativeArithmetic Filter
open scoped NNReal BigOperators

noncomputable section

theorem section_growth_iff_real_isTheta (f g : ℕ → ClosedTerm) (F G : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, ∃ x : ℝ≥0, value (f n) = (x : Value) ∧ (x : ℝ) = F n)
    (hg : ∀ᶠ n in atTop, ∃ y : ℝ≥0, value (g n) = (y : Value) ∧ (y : ℝ) = G n) :
    ((∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
        sectionOf (f n) ⊆ sectionOf (scale C (g n))) ∧
      (∃ C : ℕ, 0 < C ∧ ∀ᶠ n in atTop,
        sectionOf (g n) ⊆ sectionOf (scale C (f n)))) ↔ F =Θ[atTop] G :=
  and_congr (section_growth_iff_real_isBigO f g F G hf hg)
    (section_growth_iff_real_isBigO g f G F hg hf)

theorem real_n_log_isBigO_n_sqrt :
    (fun n : ℕ => (n : ℝ) * Real.logb 2 (n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * Real.sqrt (n : ℝ)) :=
  (section_growth_iff_real_isBigO nLog nRoot _ _
    (eventually_atTop.mpr ⟨1, nLog_value_real⟩)
    (Eventually.of_forall nRoot_value_real)).mp exact_n_log_bigO_n_sqrt

/-- Norm Big-O allows arbitrary real constants; the accepted cofinality bridge
reduces any such bound to a natural coefficient contradicted by the source claim. -/
theorem real_linear_plus_sqrt_not_isBigO :
    ¬ ((fun n : ℕ => (n : ℝ) + Real.sqrt (n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ))) := by
  intro h
  apply exact_linear_plus_sqrt_not_bigO
  exact (section_growth_iff_real_isBigO nPlusRoot rootLog _ _
    (Eventually.of_forall nPlusRoot_value_real)
    (eventually_atTop.mpr ⟨1, rootLog_value_real⟩)).mpr h

theorem real_harmonic_isTheta_log :
    (fun n : ℕ => (harmonic n : ℝ)) =Θ[atTop]
      (fun n : ℕ => Real.logb 2 (n : ℝ)) :=
  (section_growth_iff_real_isTheta (fun n => rational (harmonic n)) logarithm _ _
    (Eventually.of_forall harmonic_value_real)
    (eventually_atTop.mpr ⟨1, logarithm_value_real⟩)).mp exact_harmonic_theta_log

theorem real_n_harmonic_isTheta_n_log :
    (fun n : ℕ => (n : ℝ) * (harmonic n : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) * Real.logb 2 (n : ℝ)) :=
  (section_growth_iff_real_isTheta (fun n => rational ((n : ℚ) * harmonic n)) nLog _ _
    (Eventually.of_forall n_harmonic_value_real)
    (eventually_atTop.mpr ⟨1, nLog_value_real⟩)).mp exact_n_harmonic_theta_n_log

theorem real_exponentiated_log_isBigO_linear :
    (fun n : ℕ => (2 : ℝ) ^ Real.logb 2 (n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)) :=
  (section_growth_iff_real_isBigO exponentiatedLogarithm (fun n => rational (n : ℚ)) _ _
    (eventually_atTop.mpr ⟨1, exponentiatedLogarithm_value_rpow⟩)
    (Eventually.of_forall rational_nat_value_real)).mp exact_exponentiated_log_bigO_linear

theorem real_factorial_log_isTheta_n_log :
    (fun n : ℕ => Real.logb 2 (Nat.factorial n : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) * Real.logb 2 (n : ℝ)) :=
  (section_growth_iff_real_isTheta (fun n => logarithm (Nat.factorial n)) nLog _ _
    (Eventually.of_forall factorial_log_value_real)
    (eventually_atTop.mpr ⟨1, nLog_value_real⟩)).mp exact_factorial_log_theta_n_log

theorem real_weighted_log_isTheta_n_square_log :
    (fun n : ℕ => ∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 (k : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 * Real.logb 2 (n : ℝ)) :=
  (section_growth_iff_real_isTheta weightedLogExpr nSquareLog _ _
    (Eventually.of_forall value_weightedLogExpr)
    (eventually_atTop.mpr ⟨1, nSquareLog_value_real⟩)).mp
      exact_weighted_log_theta_n_square_log

theorem real_cubic_lower_terms_isTheta_cubic :
    (fun n : ℕ => (n : ℝ) ^ 3 + (n : ℝ) ^ 2 + (n : ℝ) * Real.logb 2 (n : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ 3) :=
  (section_growth_iff_real_isTheta cubicLowerTerms
    (fun n => rational ((n * n * n : ℕ) : ℚ)) _ _
    (eventually_atTop.mpr ⟨1, cubicLowerTerms_value_real⟩)
    (Eventually.of_forall cubic_rational_value_real)).mp exact_cubic_lower_terms_theta

end
end Examples.ExactGrowth
