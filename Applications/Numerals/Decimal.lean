import Squares
import SquareKit.ListFusion
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp

/-!
# Exact decimal folds and positional meaning

Input digits are most significant first. The actual integer left fold and
rational right fold have a standard positional meaning. The unreduced pair
fold is a separate realization; its decoding law holds on reached states with
positive denominator. These exact Nat/Rat claims do not assert machine or
floating arithmetic behavior. See `docs/research/adwh-numerals.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Numerals.Decimal

/-- Mathlib's positional interpretation expects little-endian digits. -/
abbrev positionalValue (digits : List Nat) : Nat := Nat.ofDigits 10 digits.reverse

theorem positionalValue_nil : positionalValue [] = 0 := rfl

theorem positionalValue_cons (d : Nat) (digits : List Nat) :
    positionalValue (d :: digits) = d * 10 ^ digits.length + positionalValue digits := by
  simpa [positionalValue, Nat.mul_comm, Nat.add_comm] using
    (Nat.ofDigits_reverse_cons (b := 10) digits d)

/-- The source's independent positional sum, with units assigned exponent zero. -/
theorem positionalValue_eq_sum (digits : List Nat) :
    positionalValue digits =
      (digits.reverse.zipIdx.map (fun p => p.1 * 10 ^ p.2)).sum := by
  rw [positionalValue, Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_zipIdx_map]

def shiftl (n d : Nat) : Nat := 10 * n + d

def integer (digits : List Nat) : Nat := digits.foldl shiftl 0

theorem integer_fold_invariant (seed : Nat) (digits : List Nat) :
    digits.foldl shiftl seed = seed * 10 ^ digits.length + positionalValue digits := by
  induction digits generalizing seed with
  | nil => simp [positionalValue]
  | cons d digits ih =>
    rw [List.foldl_cons, ih, positionalValue_cons]
    simp only [shiftl, List.length_cons, Nat.pow_succ]
    ring

theorem integer_spec (digits : List Nat) : integer digits = positionalValue digits := by
  simpa [integer] using integer_fold_invariant 0 digits

theorem integer_cons (d : Nat) (digits : List Nat) :
    integer (d :: digits) = d * 10 ^ digits.length + integer digits := by
  rw [integer_spec, positionalValue_cons, integer_spec]

def Digits (digits : List Nat) : Prop := ∀ d ∈ digits, d < 10

theorem positionalValue_lt (digits : List Nat) (h : Digits digits) :
    positionalValue digits < 10 ^ digits.length := by
  simpa only [positionalValue, List.length_reverse] using
    (Nat.ofDigits_lt_base_pow_length (b := 10) (l := digits.reverse) (by decide)
      (fun d hd => h d (List.mem_reverse.mp hd)))

theorem integer_lt (digits : List Nat) (h : Digits digits) :
    integer digits < 10 ^ digits.length := by
  rw [integer_spec]
  exact positionalValue_lt digits h

/-- A literal update of an unreduced numerator and denominator. -/
def partsStep (d : Nat) (p : Nat × Nat) : Nat × Nat := (d * p.2 + p.1, 10 * p.2)

def fractionParts (digits : List Nat) : Nat × Nat := digits.foldr partsStep (0, 1)

theorem fractionParts_spec (digits : List Nat) :
    fractionParts digits = (positionalValue digits, 10 ^ digits.length) := by
  induction digits with
  | nil => rfl
  | cons d digits ih =>
    change partsStep d (fractionParts digits) = _
    rw [ih, positionalValue_cons]
    simp [partsStep, Nat.pow_succ, Nat.mul_comm]

theorem fractionParts_numerator (digits : List Nat) :
    (fractionParts digits).1 = integer digits := by
  rw [fractionParts_spec, integer_spec]

theorem fractionParts_denominator (digits : List Nat) :
    (fractionParts digits).2 = 10 ^ digits.length := by rw [fractionParts_spec]

theorem fractionParts_den_pos (digits : List Nat) : 0 < (fractionParts digits).2 := by
  rw [fractionParts_denominator]
  exact Nat.pow_pos (by decide)

theorem fractionParts_proper (digits : List Nat) (h : Digits digits) :
    (fractionParts digits).1 < (fractionParts digits).2 := by
  rw [fractionParts_spec]
  exact positionalValue_lt digits h

/-- Total rational decoding. Its step law below requires positive denominator. -/
def decodeParts (p : Nat × Nat) : ℚ := (p.1 : ℚ) / (p.2 : ℚ)

theorem decodeParts_eq_mkRat (p : Nat × Nat) :
    decodeParts p = mkRat p.1 p.2 := by
  simp [decodeParts, Rat.mkRat_eq_div]

theorem partsStep_den_pos (d : Nat) (p : Nat × Nat) (h : 0 < p.2) :
    0 < (partsStep d p).2 := Nat.mul_pos (by decide) h

theorem decodeParts_step (d : Nat) (p : Nat × Nat) (h : 0 < p.2) :
    decodeParts (partsStep d p) = ((d : ℚ) + decodeParts p) / 10 := by
  have hp : (p.2 : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h)
  simp only [decodeParts, partsStep, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hp]

def fractionRat (digits : List Nat) : ℚ := decodeParts (fractionParts digits)

theorem fractionRat_spec (digits : List Nat) :
    fractionRat digits = (positionalValue digits : ℚ) / (10 : ℚ) ^ digits.length := by
  simp [fractionRat, decodeParts, fractionParts_spec]

theorem fractionRat_eq_integer_ratio (digits : List Nat) :
    fractionRat digits = (integer digits : ℚ) / (10 : ℚ) ^ digits.length := by
  rw [fractionRat_spec, integer_spec]

/-- The source fractional executor, using exact rational arithmetic. -/
def fractionFold (digits : List Nat) : ℚ :=
  digits.foldr (fun (d : Nat) (x : ℚ) => ((d : ℚ) + x) / 10) 0

theorem fractionFold_eq_fraction (digits : List Nat) :
    fractionFold digits = fractionRat digits := by
  have h := SquareKit.ListFusion.foldr_reachable partsStep
    (fun d (x : ℚ) => ((d : ℚ) + x) / 10) decodeParts
    (fun p => 0 < p.2) (0, 1) (by decide) partsStep_den_pos decodeParts_step digits
  have hz : decodeParts (0, 1) = 0 := by simp [decodeParts]
  rw [hz] at h
  exact h.symm

theorem fractionFold_spec (digits : List Nat) :
    fractionFold digits = (positionalValue digits : ℚ) / (10 : ℚ) ^ digits.length := by
  rw [fractionFold_eq_fraction, fractionRat_spec]

theorem fractionRat_nonneg (digits : List Nat) : 0 ≤ fractionRat digits := by
  rw [fractionRat_spec]
  exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos (by norm_num) _))

theorem fractionRat_lt_one (digits : List Nat) (h : Digits digits) : fractionRat digits < 1 := by
  rw [fractionRat_spec]
  apply (div_lt_one₀ (pow_pos (by norm_num) _)).mpr
  exact_mod_cast positionalValue_lt digits h

theorem fractionFold_bounds (digits : List Nat) (h : Digits digits) :
    0 ≤ fractionFold digits ∧ fractionFold digits < 1 := by
  rw [fractionFold_eq_fraction]
  exact ⟨fractionRat_nonneg digits, fractionRat_lt_one digits h⟩

theorem integer_zero_cons (digits : List Nat) : integer (0 :: digits) = integer digits := by
  simp [integer_cons]

theorem fractionFold_zero_cons (digits : List Nat) :
    fractionFold (0 :: digits) = fractionFold digits / 10 := by
  simp [fractionFold]

theorem fractionParts_replicate_zero (n : Nat) :
    fractionParts (List.replicate n 0) = (0, 10 ^ n) := by
  simp [fractionParts_spec, positionalValue]

theorem fractionFold_replicate_zero (n : Nat) : fractionFold (List.replicate n 0) = 0 := by
  simp [fractionFold_eq_fraction, fractionRat, fractionParts_replicate_zero, decodeParts]

def integerSquare : Squares.Square ⟨List Nat, List Nat, id⟩ ⟨Nat, Nat, id⟩ where
  impl := integer
  spec := positionalValue
  commutes := integer_spec

/-- Raw pairs have a total interpretation; no unrestricted step square is asserted. -/
def partsRep : Squares.Rep := ⟨Nat × Nat, ℚ, decodeParts⟩

/-- The whole pair-producing fold commutes because its reached denominators are positive. -/
def fractionPartsSquare : Squares.Square ⟨List Nat, List Nat, id⟩ partsRep where
  impl := fractionParts
  spec := fractionFold
  commutes digits := (fractionFold_eq_fraction digits).symm

def decodeSquare : Squares.Square partsRep ⟨ℚ, ℚ, id⟩ where
  impl := decodeParts
  spec := id
  commutes _ := rfl

def fractionSquare := Squares.compose decodeSquare fractionPartsSquare

theorem fractionSquare_value (digits : List Nat) :
    fractionSquare.impl digits = fractionFold digits := fractionSquare.commutes digits

end Numerals.Decimal
