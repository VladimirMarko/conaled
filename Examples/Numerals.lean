import Applications.Numerals.Decimal
import Applications.Parallel.Polynomial
import Mathlib.Tactic.NormNum

/-!
# Exact numerals through independent realizations

The source folds retain their digit order and rational domain. An existing
scan-of-powers/dot-product evaluator computes the same integer meaning for every
scan plan, and its output feeds an exact fractional observation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.Numerals
open Numerals.Decimal Applications.Parallel

theorem source_digits : integer [2, 7, 1, 8] = 2718 := by
  rw [integer_spec]
  rfl

theorem seeded_digits : [2, 7, 1, 8].foldl shiftl 42 = 422718 := by
  rw [integer_fold_invariant]
  rfl

theorem source_parts : fractionParts [1, 2, 5] = (125, 1000) := by
  rw [fractionParts_spec]
  rfl

theorem source_printed_integer : integer [1, 4, 8, 4, 9, 3] = 148493 := by
  rw [integer_spec]
  rfl

theorem source_printed_fraction :
    fractionFold [1, 4, 8, 4, 9, 3] = (148493 : ℚ) / 1000000 := by
  rw [fractionFold_spec]
  norm_num [positionalValue, Nat.ofDigits]

theorem source_eighth : fractionRat [1, 2, 5] = (1 : ℚ) / 8 := by
  rw [fractionRat_spec]
  norm_num [positionalValue, Nat.ofDigits]

theorem source_improper : fractionFold [10] = 1 ∧ ¬ Digits [10] := by
  rw [fractionFold_spec]
  norm_num [positionalValue, Nat.ofDigits, Digits]

theorem source_empty :
    integer [] = 0 ∧ fractionFold [] = 0 ∧ fractionParts [] = (0, 1) := by
  norm_num [integer_spec, fractionFold_spec, fractionParts_spec, positionalValue]

theorem source_proper_bounds :
    0 ≤ fractionFold [1, 4, 8, 4, 9, 3] ∧ fractionFold [1, 4, 8, 4, 9, 3] < 1 :=
  fractionFold_bounds _ (by norm_num [Digits])

theorem leading_zero :
    integer [0, 1, 2, 5] = 125 ∧ fractionParts [0, 1, 2, 5] = (125, 10000) ∧
      fractionFold [0, 1, 2, 5] = (1 : ℚ) / 80 := by
  norm_num [integer_spec, fractionParts_spec, fractionFold_spec, positionalValue, Nat.ofDigits]

theorem all_zero_denominator (n : Nat) :
    fractionParts (List.replicate n 0) = (0, 10 ^ n) ∧
      fractionFold (List.replicate n 0) = 0 :=
  ⟨fractionParts_replicate_zero n, fractionFold_replicate_zero n⟩

/-- Totalized division does not supply the reached-state step law at denominator zero. -/
theorem zero_denominator_step_fails :
    decodeParts (partsStep 1 (0, 0)) ≠ ((1 : ℚ) + decodeParts (0, 0)) / 10 := by
  norm_num [decodeParts, partsStep]

theorem pair_observation : fractionSquare.impl [1, 2, 5] = (1 : ℚ) / 8 := by
  rw [fractionSquare_value, fractionFold_eq_fraction]
  exact source_eighth

/-- The coefficient-list specification is independent of both realizations. -/
theorem polynomial_digits (coefficients : List Nat) :
    polynomial coefficients 10 = integer coefficients.reverse := by
  rw [integer_spec, positionalValue, List.reverse_reverse, Nat.ofDigits_eq_sum_mapIdx,
    List.mapIdx_eq_zipIdx_map, List.zipIdx_eq_zip_range', List.map_zip_eq_zipWith,
    ← List.range_eq_range']
  rfl

/-- Every existing scan recipe computes the same decimal numeral meaning. -/
theorem parallel_integer (plan : ScanPlan) (data : plan.shape.Data Nat) :
    evaluatePolynomial plan data 10 = integer (plan.shape.flatten data).reverse := by
  rw [evaluatePolynomial_correct, polynomial_digits]

/-- Decoding reverses low-to-high coefficients to source digit order. -/
def coefficientRep (plan : ScanPlan) : Squares.Rep where
  R := plan.shape.Data Nat
  S := List Nat
  decode data := (plan.shape.flatten data).reverse

def parallelIntegerSquare (plan : ScanPlan) :
    Squares.Square (coefficientRep plan) ⟨Nat, Nat, id⟩ where
  impl data := evaluatePolynomial plan data 10
  spec := integer
  commutes := parallel_integer plan

/-- The actual scan output is consumed as an exact ratio with its known digit count. -/
theorem parallel_fraction (plan : ScanPlan) (data : plan.shape.Data Nat) :
    (evaluatePolynomial (R := Nat) plan data 10 : ℚ) / (10 : ℚ) ^ plan.shape.size =
      fractionFold (plan.shape.flatten data).reverse := by
  rw [parallel_integer, fractionFold_eq_fraction, fractionRat_eq_integer_ratio,
    List.length_reverse, Shape.flatten_length]

def parallelFractionSquare (plan : ScanPlan) :
    Squares.Square (coefficientRep plan) ⟨ℚ, ℚ, id⟩ where
  impl data := (evaluatePolynomial (R := Nat) plan data 10 : ℚ) / (10 : ℚ) ^ plan.shape.size
  spec := fractionFold
  commutes := parallel_fraction plan

def four : ScanPlan := .prod (.prod .leaf .leaf) (.prod .leaf .leaf)

/-- A concrete natural-number container usable by both four-entry recipes. -/
def decimalCoefficients : (Nat × Nat) × (Nat × Nat) := ((8, 1), (7, 2))

theorem balanced_integer : evaluatePolynomial four decimalCoefficients 10 = 2718 := by
  exact (parallel_integer four decimalCoefficients).trans source_digits

theorem balanced_fraction :
    (parallelFractionSquare four).impl decimalCoefficients = (1359 : ℚ) / 5000 := by
  calc
    (parallelFractionSquare four).impl decimalCoefficients = fractionFold [2, 7, 1, 8] :=
      (parallelFractionSquare four).commutes decimalCoefficients
    _ = (1359 : ℚ) / 5000 := by
      rw [fractionFold_spec]
      norm_num [positionalValue, Nat.ofDigits]

/-- Functor-composition and product plans have distinct recipes, even at one shape. -/
def compound : ScanPlan := .comp (.prod .leaf .leaf) (.prod .leaf .leaf)

theorem compound_integer : evaluatePolynomial compound decimalCoefficients 10 = 2718 := by
  exact (parallel_integer compound decimalCoefficients).trans source_digits

theorem recipes_agree :
    (parallelIntegerSquare four).impl decimalCoefficients =
      (parallelIntegerSquare compound).impl decimalCoefficients :=
  balanced_integer.trans compound_integer.symm

end Examples.Numerals
