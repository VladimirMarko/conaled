import Applications.Stack.Machine
import Applications.Intervals.ExactArithmetic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExactArithmeticPipeline
open IntervalAnalysis IntervalAnalysis.Exact

def negativeEndpointBox : Interval := ⟨-1, 2⟩

theorem sqrt_two_in_negativeEndpointBox :
    ContainsReal negativeEndpointBox (Real.sqrt 2) := by
  simp only [ContainsReal, negativeEndpointBox, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat]
  constructor
  · exact (show (-1 : ℝ) ≤ 0 by norm_num).trans (Real.sqrt_nonneg 2)
  · exact Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))

theorem negativeEndpointBox_mul :
    IntervalAnalysis.mul negativeEndpointBox negativeEndpointBox = ⟨-2, 4⟩ := by
  norm_num [IntervalAnalysis.mul, negativeEndpointBox]

theorem negativeEndpointBox_square_encloses_two :
    ContainsReal (IntervalAnalysis.mul negativeEndpointBox negativeEndpointBox) (2 : ℝ) := by
  have h := mul_containsReal sqrt_two_in_negativeEndpointBox sqrt_two_in_negativeEndpointBox
  simpa only [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using h

end Examples.ExactArithmeticPipeline
/-! The existing compiler and stack target share the exact arithmetic terms. -/

namespace Examples.ExactArithmeticPipeline
open FirstOrderCompiler SquareKit.NonnegativeArithmetic
open scoped NNReal

noncomputable section

def stackCode {Γ : Ctx} {a : Ty} (t : Term Prim Γ a) (s : List Ty) :
    StackMachine.Program Prim (context Γ) s a s :=
  (FirstOrderCompiler.compile (StackMachine.target Prim valueMeaning) t).code s

def stackRun {Γ : Ctx} {a : Ty} (t : Term Prim Γ a) (s : List Ty)
    (ρ : Val Value (context Γ)) (z : StackMachine.Stack Value s) :
    Val Value a × StackMachine.Stack Value s :=
  StackMachine.run valueMeaning (stackCode t s) (ρ, z)

/-- Compilation preserves the result and every arbitrary typed stack tail. -/
theorem stackRun_correct {Γ : Ctx} {a : Ty} (t : Term Prim Γ a)
    (s : List Ty) (ρ : Val Value (context Γ)) (z : StackMachine.Stack Value s) :
    stackRun t s ρ z = (valueTerm t ρ, z) :=
  StackMachine.compile_correct valueMeaning t s ρ z

theorem raw_related_stack_output {Γ : Ctx} {a : Ty} (t : Term Prim Γ a)
    (s : List Ty) (ρ : Val Value (context Γ)) (z : StackMachine.Stack Value s)
    {r : (FirstOrderRelations.encoding representation (context Γ)).R}
    (h : (FirstOrderRelations.encoding representation (context Γ)).Rel r ρ) :
    (FirstOrderRelations.encoding representation a).Rel
        (rawTerm t r) (stackRun t s ρ z).1 ∧
      (stackRun t s ρ z).2 = z := by
  rw [stackRun_correct]
  exact ⟨rawTerm_related t h, rfl⟩

theorem interval_contains_stack_output (q : ℕ) (hq : 0 < q)
    {Γ : Ctx} {a : Ty} (t : Term Prim Γ a)
    (s : List Ty) (ρ : Val Value (context Γ)) (z : StackMachine.Stack Value s)
    {box : (FirstOrderRelations.encoding IntervalAnalysis.Exact.representation (context Γ)).R}
    (h : (FirstOrderRelations.encoding IntervalAnalysis.Exact.representation (context Γ)).Rel box ρ) :
    (FirstOrderRelations.encoding IntervalAnalysis.Exact.representation a).Rel
        ((IntervalAnalysis.Exact.compile q hq t).impl box) (stackRun t s ρ z).1 ∧
      (stackRun t s ρ z).2 = z := by
  rw [stackRun_correct]
  exact ⟨IntervalAnalysis.Exact.compile_contains q hq t h, rfl⟩

/-- The native let shares one square-root value across both uses in the body. -/
def sharedRoot : ClosedTerm :=
  .letE (squareRoot 2)
    (add (mul (.var .here) (.var .here)) (.var .here))

def rootSquare : ClosedTerm := mul (squareRoot 2) (squareRoot 2)

def discardedInvalid : ClosedTerm := .letE (logarithm 0) (rational 1)

theorem rootSquare_value :
    value rootSquare = ((2 : ℝ≥0) : Value) := by
  change strictMul ((NNReal.sqrt 2 : ℝ≥0) : Value) ((NNReal.sqrt 2 : ℝ≥0) : Value) = _
  simp only [strictMul, WithBot.map₂_coe_coe, NNReal.mul_self_sqrt]

theorem sharedRoot_value :
    value sharedRoot = ((2 + NNReal.sqrt 2 : ℝ≥0) : Value) := by
  change strictAdd
    (strictMul ((NNReal.sqrt 2 : ℝ≥0) : Value) ((NNReal.sqrt 2 : ℝ≥0) : Value))
    ((NNReal.sqrt 2 : ℝ≥0) : Value) = _
  simp only [strictAdd, strictMul, WithBot.map₂_coe_coe, NNReal.mul_self_sqrt]

theorem sharedRoot_stack (s : List Ty) (z : StackMachine.Stack Value s) :
    stackRun sharedRoot s () z = (((2 + NNReal.sqrt 2 : ℝ≥0) : Value), z) := by
  rw [stackRun_correct]
  exact congrArg (fun v => (v, z)) sharedRoot_value

theorem discardedInvalid_value : value discardedInvalid = ((1 : ℝ≥0) : Value) := by
  change rationalValue 1 = _
  norm_num [rationalValue]

theorem discardedInvalid_raw : raw discardedInvalid = Set.Icc 0 1 := rfl

theorem discardedInvalid_stack (s : List Ty) (z : StackMachine.Stack Value s) :
    stackRun discardedInvalid s () z = (((1 : ℝ≥0) : Value), z) := by
  rw [stackRun_correct]
  exact congrArg (fun v => (v, z)) discardedInvalid_value

theorem zero_mul_invalid : value (mul (rational 0) (logarithm 0)) = ⊥ := by
  simp [value_mul, value_rational, value_logarithm, rationalValue, logarithmValue,
    strictMul]

theorem invalid_mul_zero : value (mul (logarithm 0) (rational 0)) = ⊥ := by
  simp [value_mul, value_rational, value_logarithm, rationalValue, logarithmValue,
    strictMul]

theorem zero_mul_valid : value (mul (rational 0) (squareRoot 2)) = ((0 : ℝ≥0) : Value) := by
  simp [value_mul, value_rational, value_squareRoot, rationalValue, squareRootValue,
    strictMul]

/-- The first four canonical source observations use exact finite witnesses. -/
theorem source_root_two_lower : (7 / 5 : ℚ) ∈ sectionOf (squareRoot 2) := by
  exact (squareRoot_section_fraction_iff 2 7 5 (by decide)).mpr (by decide)

theorem source_root_two_upper : (10 / 7 : ℚ) ∉ sectionOf (squareRoot 2) := by
  intro h
  have htest := (squareRoot_section_fraction_iff 2 10 7 (by decide)).mp h
  omega

theorem source_log_three_lower : (3 / 2 : ℚ) ∈ sectionOf (logarithm 3) := by
  exact (logarithm_section_fraction_iff 3 3 2 (by decide) (by decide)).mpr (by decide)

theorem source_log_three_upper : (2 : ℚ) ∉ sectionOf (logarithm 3) := by
  have h := logarithm_section_fraction_iff 3 2 1 (by decide) (by decide)
  norm_num at h
  exact h

theorem source_expLog_three (x : ℚ) :
    x ∈ sectionOf (exponentiatedLogarithm 3) ↔ x ≤ 3 := by
  exact exponentiatedLogarithm_section_iff 3 (by decide) x

end
end Examples.ExactArithmeticPipeline
/-! Raw, closed-section and strict-validity boundary cases on native terms. -/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExactArithmeticPipeline
open SquareKit.NonnegativeArithmetic
open scoped NNReal

noncomputable section

/-- The lower rational observation is present in the actual compiled raw set. -/
theorem root_two_raw_lower : (7 / 5 : ℚ) ∈ raw (squareRoot 2) := by
  rw [raw_squareRoot]
  refine (mem_rootApprox_iff 2 _).mpr ⟨by norm_num, ?_⟩
  exact (nat_fraction_le_sqrt_iff 2 7 5 (by decide)).mpr (by decide)

theorem root_two_raw_upper : (10 / 7 : ℚ) ∉ raw (squareRoot 2) := by
  intro hraw
  have hsection := raw_subset_sectionOf (squareRoot 2) hraw
  have htest := (squareRoot_section_fraction_iff 2 10 7 (by decide)).mp hsection
  omega

/-- Real multiplication attains two in the closed observation contract, while
the compiled raw product does not attain this endpoint. -/
theorem root_two_square_raw_endpoint_absent :
    (2 : ℚ) ∉ raw (mul (squareRoot 2) (squareRoot 2)) := by
  simpa only [raw_mul, raw_squareRoot] using rootApprox_two_product_not_two

theorem root_two_square_closed_endpoint :
    (2 : ℚ) ∈ sectionOf (mul (squareRoot 2) (squareRoot 2)) := by
  apply (mem_sectionOf_iff (mul (squareRoot 2) (squareRoot 2)) 2).mpr
  exact ⟨2, rootSquare_value, by norm_num⟩

theorem zero_mul_invalid_raw : raw (mul (rational 0) (logarithm 0)) = ∅ :=
  (value_eq_bot_iff _).mp zero_mul_invalid

theorem invalid_mul_zero_raw : raw (mul (logarithm 0) (rational 0)) = ∅ :=
  (value_eq_bot_iff _).mp invalid_mul_zero

theorem zero_mul_invalid_section : sectionOf (mul (rational 0) (logarithm 0)) = ∅ :=
  (value_eq_bot_iff_sectionOf_empty _).mp zero_mul_invalid

theorem invalid_mul_zero_section : sectionOf (mul (logarithm 0) (rational 0)) = ∅ :=
  (value_eq_bot_iff_sectionOf_empty _).mp invalid_mul_zero

/-- Finite zero multiplication has a singleton raw result, unlike either
invalid-zero product above. -/
theorem zero_mul_valid_raw : raw (mul (rational 0) (squareRoot 2)) = {0} := by
  rw [raw_mul, raw_rational, raw_squareRoot]
  ext x
  constructor
  · rintro ⟨a, ha, b, _, rfl⟩
    have ha0 : a = 0 := le_antisymm ha.2 ha.1
    simp only [ha0, zero_mul, Set.mem_singleton_iff]
  · intro hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    have hzero : (0 : ℚ) ∈ rootApprox 2 := (mem_rootApprox_iff 2 0).mpr
      ⟨le_rfl, by simpa only [Rat.cast_zero, Nat.cast_ofNat] using Real.sqrt_nonneg (2 : ℝ)⟩
    exact ⟨0, ⟨le_rfl, le_rfl⟩, 0, hzero, by simp⟩

theorem zero_mul_valid_section (q : ℚ) :
    q ∈ sectionOf (mul (rational 0) (squareRoot 2)) ↔ q ≤ 0 := by
  change q ∈ closedSection (raw (mul (rational 0) (squareRoot 2))) ↔ q ≤ 0
  rw [zero_mul_valid_raw]
  exact mem_closedSection_singleton 0 q

theorem negative_rational_value : value (rational (-1)) = ⊥ := by
  norm_num [value_rational, rationalValue]

theorem negative_rational_raw : raw (rational (-1)) = ∅ :=
  (value_eq_bot_iff _).mp negative_rational_value

theorem negative_rational_section : sectionOf (rational (-1)) = ∅ :=
  (value_eq_bot_iff_sectionOf_empty _).mp negative_rational_value

theorem negative_rational_rejects_negative :
    (-2 : ℚ) ∉ sectionOf (rational (-1)) := by
  rw [negative_rational_section]
  exact Set.notMem_empty _

theorem rational_zero_value : value (rational 0) = ((0 : ℝ≥0) : Value) := by
  change rationalValue 0 = _
  simpa only [Nat.cast_zero] using rationalValue_natCast 0

theorem root_zero_value : value (squareRoot 0) = ((0 : ℝ≥0) : Value) := by
  simp [value_squareRoot, squareRootValue]

theorem log_one_value : value (logarithm 1) = ((0 : ℝ≥0) : Value) := by
  norm_num [value_logarithm, logarithmValue]

theorem rational_zero_section (q : ℚ) : q ∈ sectionOf (rational 0) ↔ q ≤ 0 :=
  rational_section_iff 0 q (le_refl 0)

theorem root_zero_section (q : ℚ) : q ∈ sectionOf (squareRoot 0) ↔ q ≤ 0 := by
  simpa only [Nat.zero_mul, Nat.cast_zero] using
    section_of_exact_bounds (bounded_root_square 0) q

theorem log_one_section (q : ℚ) : q ∈ sectionOf (logarithm 1) ↔ q ≤ 0 := by
  simpa only [pow_zero, Nat.cast_zero] using
    section_of_exact_bounds (bounded_log_power 0) q

/-- The three valid-zero atoms admit every nonpositive rational observation. -/
theorem nonpositive_zero_atom_observations (q : ℚ) (hq : q ≤ 0) :
    q ∈ sectionOf (rational 0) ∧ q ∈ sectionOf (squareRoot 0) ∧
      q ∈ sectionOf (logarithm 1) :=
  ⟨(rational_zero_section q).mpr hq, (root_zero_section q).mpr hq,
    (log_one_section q).mpr hq⟩

theorem expLog_zero_value : value (exponentiatedLogarithm 0) = ⊥ := by
  simp [value_exponentiatedLogarithm, exponentiatedLogarithmValue]

theorem expLog_zero_raw : raw (exponentiatedLogarithm 0) = ∅ :=
  (value_eq_bot_iff _).mp expLog_zero_value

theorem expLog_zero_section : sectionOf (exponentiatedLogarithm 0) = ∅ :=
  (value_eq_bot_iff_sectionOf_empty _).mp expLog_zero_value

/-- The standard totalized real expression gives one at zero; the native source
atom deliberately remains invalid, with no raw or closed observations. -/
theorem expLog_zero_totalized_real : (2 : ℝ) ^ Real.logb 2 (0 : ℝ) = 1 := by
  simp

theorem expLog_three_raw_endpoint_absent :
    (3 : ℚ) ∉ raw (exponentiatedLogarithm 3) := by
  simpa only [raw_exponentiatedLogarithm] using expLogApprox_three_not_mem

theorem expLog_three_closed_endpoint :
    (3 : ℚ) ∈ sectionOf (exponentiatedLogarithm 3) :=
  (exponentiatedLogarithm_section_iff 3 (by decide) 3).mpr le_rfl

theorem expLog_four_raw_endpoint : (4 : ℚ) ∈ raw (exponentiatedLogarithm 4) := by
  simpa only [raw_exponentiatedLogarithm] using expLogApprox_four_mem

end
end Examples.ExactArithmeticPipeline
/-! Concrete outputs of the existing interval compiler, including shared native bindings. -/

namespace Examples.ExactArithmeticPipeline
open FirstOrderCompiler
open SquareKit.NonnegativeArithmetic
open IntervalAnalysis.Exact

theorem rootInterval_ten_two :
    squareRootInterval 10 2 = some ⟨7 / 5, 3 / 2⟩ := by
  have hfloor : Nat.sqrt (2 * 10 * 10) = 14 := by
    symm
    apply Nat.eq_sqrt.mpr
    norm_num
  norm_num [squareRootInterval, hfloor]

theorem logInterval_ten_three :
    logarithmInterval 10 3 = some ⟨3 / 2, 8 / 5⟩ := by
  have hfloor : Nat.log2 (3 ^ 10) = 15 := by decide
  norm_num [logarithmInterval, hfloor]

theorem expLogInterval_ten_three :
    exponentiatedLogarithmInterval 10 3 = some ⟨29 / 10, 3⟩ := by
  norm_num [exponentiatedLogarithmInterval]

theorem interval_root_two :
    ((IntervalAnalysis.Exact.compile 10 (by decide) (squareRoot 2 : ClosedTerm)).impl ()) =
      some ⟨7 / 5, 3 / 2⟩ := by
  change squareRootInterval 10 2 = some ⟨7 / 5, 3 / 2⟩
  exact rootInterval_ten_two

theorem interval_log_three :
    ((IntervalAnalysis.Exact.compile 10 (by decide) (logarithm 3 : ClosedTerm)).impl ()) =
      some ⟨3 / 2, 8 / 5⟩ := by
  change logarithmInterval 10 3 = some ⟨3 / 2, 8 / 5⟩
  exact logInterval_ten_three

theorem interval_expLog_three :
    ((IntervalAnalysis.Exact.compile 10 (by decide)
      (exponentiatedLogarithm 3 : ClosedTerm)).impl ()) = some ⟨29 / 10, 3⟩ := by
  change exponentiatedLogarithmInterval 10 3 = some ⟨29 / 10, 3⟩
  exact expLogInterval_ten_three

theorem interval_root_two_squared :
    ((IntervalAnalysis.Exact.compile 10 (by decide)
      (mul (squareRoot 2) (squareRoot 2) : ClosedTerm)).impl ()) =
      some ⟨49 / 25, 9 / 4⟩ := by
  change Option.map₂ IntervalAnalysis.mul
      (squareRootInterval 10 2) (squareRootInterval 10 2) = some ⟨49 / 25, 9 / 4⟩
  rw [rootInterval_ten_two]
  norm_num [Option.map₂, IntervalAnalysis.mul]

theorem interval_shared_explicit :
    ((IntervalAnalysis.Exact.compile 10 (by decide)
      (.letE (squareRoot 2)
        (add (mul (.var .here) (.var .here)) (.var .here)) : ClosedTerm)).impl ()) =
      some ⟨84 / 25, 15 / 4⟩ := by
  change Option.map₂ IntervalAnalysis.add
      (Option.map₂ IntervalAnalysis.mul (squareRootInterval 10 2) (squareRootInterval 10 2))
      (squareRootInterval 10 2) = some ⟨84 / 25, 15 / 4⟩
  rw [rootInterval_ten_two]
  norm_num [Option.map₂, IntervalAnalysis.mul, IntervalAnalysis.add]

theorem interval_zero_log_zero (q : ℕ) (hq : 0 < q) :
    ((IntervalAnalysis.Exact.compile q hq
      (mul (rational 0) (logarithm 0) : ClosedTerm)).impl ()) = none := by
  change Option.map₂ IntervalAnalysis.mul
      (rationalInterval 0) (logarithmInterval q 0) = none
  simp [rationalInterval, logarithmInterval, Option.map₂]

theorem interval_log_zero_zero (q : ℕ) (hq : 0 < q) :
    ((IntervalAnalysis.Exact.compile q hq
      (mul (logarithm 0) (rational 0) : ClosedTerm)).impl ()) = none := by
  change Option.map₂ IntervalAnalysis.mul
      (logarithmInterval q 0) (rationalInterval 0) = none
  simp [rationalInterval, logarithmInterval, Option.map₂]

theorem interval_zero_root_two (q : ℕ) (hq : 0 < q) :
    ((IntervalAnalysis.Exact.compile q hq
      (mul (rational 0) (squareRoot 2) : ClosedTerm)).impl ()) = some ⟨0, 0⟩ := by
  change Option.map₂ IntervalAnalysis.mul
      (rationalInterval 0) (squareRootInterval q 2) = some ⟨0, 0⟩
  simp [rationalInterval, squareRootInterval, Option.map₂,
    IntervalAnalysis.singleton, IntervalAnalysis.mul]

theorem interval_negative_rational (q : ℕ) (hq : 0 < q) :
    ((IntervalAnalysis.Exact.compile q hq (rational (-1) : ClosedTerm)).impl ()) = none := by
  change rationalInterval (-1) = none
  norm_num [rationalInterval]

theorem interval_log_zero (q : ℕ) (hq : 0 < q) :
    ((IntervalAnalysis.Exact.compile q hq (logarithm 0 : ClosedTerm)).impl ()) = none := by
  change logarithmInterval q 0 = none
  simp [logarithmInterval]

theorem interval_expLog_zero (q : ℕ) (hq : 0 < q) :
    ((IntervalAnalysis.Exact.compile q hq
      (exponentiatedLogarithm 0 : ClosedTerm)).impl ()) = none := by
  change exponentiatedLogarithmInterval q 0 = none
  simp [exponentiatedLogarithmInterval]

theorem interval_rational_zero (q : ℕ) (hq : 0 < q) :
    ((IntervalAnalysis.Exact.compile q hq (rational 0 : ClosedTerm)).impl ()) =
      some ⟨0, 0⟩ := by
  change rationalInterval 0 = some ⟨0, 0⟩
  simp [rationalInterval, IntervalAnalysis.singleton]

theorem interval_root_zero (q : ℕ) (hq : 0 < q) :
    ((IntervalAnalysis.Exact.compile q hq (squareRoot 0 : ClosedTerm)).impl ()) =
      some ⟨0, 1 / (q : ℚ)⟩ := by
  change squareRootInterval q 0 = some ⟨0, 1 / (q : ℚ)⟩
  simp [squareRootInterval]

theorem interval_log_one (q : ℕ) (hq : 0 < q) :
    ((IntervalAnalysis.Exact.compile q hq (logarithm 1 : ClosedTerm)).impl ()) =
      some ⟨0, 1 / (q : ℚ)⟩ := by
  change logarithmInterval q 1 = some ⟨0, 1 / (q : ℚ)⟩
  have hfloor : Nat.log2 1 = 0 := by decide
  simp [logarithmInterval, hfloor]

theorem interval_discarded_invalid_explicit (q : ℕ) (hq : 0 < q) :
    ((IntervalAnalysis.Exact.compile q hq
      (.letE (logarithm 0) (rational 1) : ClosedTerm)).impl ()) = some ⟨1, 1⟩ := by
  change rationalInterval 1 = some ⟨1, 1⟩
  norm_num [rationalInterval, IntervalAnalysis.singleton]

theorem interval_shared_related_explicit :
    IntervalAnalysis.Exact.Rel (some ⟨84 / 25, 15 / 4⟩)
      (value (.letE (squareRoot 2)
        (add (mul (.var .here) (.var .here)) (.var .here)) : ClosedTerm)) := by
  let t : ClosedTerm := .letE (squareRoot 2)
    (add (mul (.var .here) (.var .here)) (.var .here))
  have h : IntervalAnalysis.Exact.Rel
      ((IntervalAnalysis.Exact.compile 10 (by decide) t).impl ()) (value t) :=
    compile_contains 10 (by decide) t (box := ()) (ρ := ()) (by trivial)
  have heq : ((IntervalAnalysis.Exact.compile 10 (by decide) t).impl ()) =
      some ⟨84 / 25, 15 / 4⟩ := interval_shared_explicit
  rw [heq] at h
  exact h

theorem interval_discarded_related_explicit (q : ℕ) (hq : 0 < q) :
    IntervalAnalysis.Exact.Rel (some ⟨1, 1⟩)
      (value (.letE (logarithm 0) (rational 1) : ClosedTerm)) := by
  let t : ClosedTerm := .letE (logarithm 0) (rational 1)
  have h : IntervalAnalysis.Exact.Rel
      ((IntervalAnalysis.Exact.compile q hq t).impl ()) (value t) :=
    compile_contains q hq t (box := ()) (ρ := ()) (by trivial)
  have heq : ((IntervalAnalysis.Exact.compile q hq t).impl ()) =
      some ⟨1, 1⟩ := interval_discarded_invalid_explicit q hq
  rw [heq] at h
  exact h

end Examples.ExactArithmeticPipeline
/-! Exact section observations and actual interval/stack composition. -/

namespace Examples.ExactArithmeticPipeline
open FirstOrderCompiler SquareKit.NonnegativeArithmetic
open scoped NNReal

noncomputable section

theorem sharedRoot_section_iff (q : ℚ) :
    q ∈ sectionOf sharedRoot ↔ (q : ℝ) ≤ 2 + Real.sqrt 2 := by
  have h : Rel (raw sharedRoot) ((2 + NNReal.sqrt 2 : ℝ≥0) : Value) := by
    rw [← sharedRoot_value]
    exact raw_related sharedRoot
  simpa only [sectionOf, NNReal.coe_add, NNReal.coe_ofNat, Real.coe_sqrt] using h.2 q

theorem sharedRoot_value_irrational :
    ∃ x : ℝ≥0, value sharedRoot = (x : Value) ∧ Irrational (x : ℝ) := by
  refine ⟨2 + NNReal.sqrt 2, sharedRoot_value, ?_⟩
  simpa only [NNReal.coe_add, NNReal.coe_ofNat, Real.coe_sqrt, Nat.cast_ofNat]
    using irrational_sqrt_two.natCast_add 2

theorem sharedRoot_interval :
    ((IntervalAnalysis.Exact.compile 10 (by decide) sharedRoot).impl ()) =
      some ⟨84 / 25, 15 / 4⟩ :=
  interval_shared_explicit

theorem sharedRoot_interval_stack (s : List Ty) (z : StackMachine.Stack Value s) :
    IntervalAnalysis.Exact.Rel (some ⟨84 / 25, 15 / 4⟩)
        (stackRun sharedRoot s () z).1 ∧
      (stackRun sharedRoot s () z).2 = z := by
  have h := interval_contains_stack_output 10 (by decide) sharedRoot s () z
    (box := ()) True.intro
  rw [sharedRoot_interval] at h
  exact h

theorem sharedRoot_enclosed :
    IntervalAnalysis.Exact.ContainsReal ⟨84 / 25, 15 / 4⟩ (2 + Real.sqrt 2) := by
  have h := (sharedRoot_interval_stack [] ()).1
  rw [sharedRoot_stack] at h
  simpa only [IntervalAnalysis.Exact.Rel, NNReal.coe_add, NNReal.coe_ofNat,
    Real.coe_sqrt] using h

/-- q=10 gives width1/10; the arbitrary-precision contract requires a strictly
smaller width when the requested epsilon itself is1/10. -/
theorem tenth_width_not_strict :
    (3 / 2 : ℚ) - 7 / 5 = 1 / 10 ∧ ¬ (3 / 2 : ℚ) < 7 / 5 + 1 / 10 := by
  norm_num

end
end Examples.ExactArithmeticPipeline
