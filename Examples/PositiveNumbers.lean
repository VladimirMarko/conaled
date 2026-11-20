import Applications.Numerals.PositiveArithmetic

/-!
# Positive numerals, shifted keys, carries, comparison and display

The worked values use the source constructors directly: ten is numeric ten
and shifted natural key nine. Carry cases include unequal sizes and both
terminal orientations. Comparison cases expose the higher-bit override.
All conclusions below use the maintained public observations and equations.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PositiveNumbers

open Numerals.PositiveKeys Numerals.PositiveArithmetic

universe u v

theorem shifted_boundaries :
    encode 0 = .one ∧ decode .one = 0 ∧ encode 1 = .bit0 .one :=
  ⟨encode_zero, decode_one, encode_one⟩

theorem zero_one_distinct : encode 0 ≠ encode 1 := by
  intro h
  exact Nat.zero_ne_one (encode_injective h)

/-- Source constructor calculation: 0 + 2 * (1 + 2 * (0 + 2 * 1)) = 10. -/
def ten : PosNum := .bit0 (.bit1 (.bit0 .one))

theorem ten_numeric : numeric ten = 10 := by
  calc
    numeric ten = 0 + 2 * numeric (.bit1 (.bit0 .one)) := numeric_bit0 _
    _ = 0 + 2 * (1 + 2 * numeric (.bit0 .one)) :=
      congrArg (fun n : Nat => 0 + 2 * n) (numeric_bit1 _)
    _ = 0 + 2 * (1 + 2 * (0 + 2 * numeric .one)) :=
      congrArg (fun n : Nat => 0 + 2 * (1 + 2 * n)) (numeric_bit0 _)
    _ = 0 + 2 * (1 + 2 * (0 + 2 * 1)) :=
      congrArg (fun n : Nat => 0 + 2 * (1 + 2 * (0 + 2 * n))) numeric_one
    _ = 10 := rfl

theorem ten_key : decode ten = 9 := by
  have h := numeric_eq_decode_add_one ten
  rw [ten_numeric] at h
  omega

theorem encode_nine : encode 9 = ten := by
  calc
    encode 9 = encode (decode ten) := congrArg encode ten_key.symm
    _ = ten := encode_decode ten

theorem ten_pnat_observations : (toPNat ten : Nat) = 10 ∧ (toPNat ten).natPred = 9 :=
  ⟨ten_numeric, ten_key⟩

theorem ofNat_zero_one_collision : PosNum.ofNat 0 = PosNum.one ∧ PosNum.ofNat 1 = PosNum.one :=
  ⟨rfl, rfl⟩

theorem ofNat_not_injective : ¬ Function.Injective PosNum.ofNat := by
  intro h
  have collision : PosNum.ofNat 0 = PosNum.ofNat 1 :=
    ofNat_zero_one_collision.1.trans ofNat_zero_one_collision.2.symm
  exact Nat.zero_ne_one (h collision)

theorem predecessor_boundary : numeric (PosNum.pred PosNum.one) = 1 ∧
    (PosNum.pred' PosNum.one : Nat) = 0 ∧ decode PosNum.one = 0 :=
  ⟨rfl, rfl, decode_one⟩

theorem numeric_one_before_two : PosNum.cmp (encode 0) (encode 1) = .lt :=
  (cmp_encoded_lt_iff 0 1).mpr (by decide)

theorem comparator_recovers_ten : PosNum.cmp (encode 9) ten = .eq :=
  (cmp_eq_iff _ _).mpr encode_nine

theorem numeric_ten_after_one : PosNum.cmp ten (encode 0) = .gt := by
  apply (cmp_gt_iff _ _).mpr
  rw [numeric_encode, ten_numeric]
  decide

/-- Absence, an empty stored value and a nonempty stored value are distinct observations. -/
def sampleObservation (n : Nat) : Option (List Nat) :=
  if n = 0 then none else if n = 1 then some [] else some [n, n + 1]

theorem observed_absence : ((sampleObservation ∘ decode) ∘ encode) 0 = none := by
  calc
    ((sampleObservation ∘ decode) ∘ encode) 0 = sampleObservation 0 :=
      congrFun (observation_roundtrip sampleObservation) 0
    _ = none := rfl

theorem observed_empty_value : ((sampleObservation ∘ decode) ∘ encode) 1 = some [] := by
  calc
    ((sampleObservation ∘ decode) ∘ encode) 1 = sampleObservation 1 :=
      congrFun (observation_roundtrip sampleObservation) 1
    _ = some [] := rfl

theorem observed_nine : ((sampleObservation ∘ decode) ∘ encode) 9 = some [9, 10] := by
  calc
    ((sampleObservation ∘ decode) ∘ encode) 9 = sampleObservation 9 :=
      congrFun (observation_roundtrip sampleObservation) 9
    _ = some [9, 10] := rfl

theorem type_observation (observe : Nat → Type u) :
    (observe ∘ decode) ∘ encode = observe :=
  observation_roundtrip observe

theorem mapped_observation {α : Type u} {β : Type v} (observe : PosNum → α) (mapValue : α → β) :
    ((mapValue ∘ observe) ∘ encode) ∘ decode = mapValue ∘ observe :=
  positive_observation_roundtrip (mapValue ∘ observe)

theorem successor_terminal : succ .one = .bit0 .one := succ_one

theorem successor_no_carry : succ (.bit0 (.bit1 .one)) = .bit1 (.bit1 .one) :=
  succ_bit0 _

theorem successor_carry_chain :
    succ (.bit1 (.bit1 .one)) = .bit0 (.bit0 (.bit0 .one)) := by
  rw [succ_bit1, succ_bit1, succ_one]

theorem successor_ten_value : numeric (succ ten) = 11 := by
  rw [succ_correct, ten_numeric]

theorem carry_false_left_terminal :
    addc false .one (.bit1 (.bit1 .one)) = .bit0 (.bit0 (.bit0 .one)) := by
  rw [addc_false_one_bit1, succ_bit1, succ_one]

theorem carry_false_right_terminal :
    addc false (.bit1 (.bit1 .one)) .one = .bit0 (.bit0 (.bit0 .one)) := by
  rw [addc_false_bit1_one, succ_bit1, succ_one]

theorem carry_true_left_terminal :
    addc true .one (.bit0 (.bit1 (.bit1 .one))) = .bit0 (.bit0 (.bit0 (.bit0 .one))) := by
  rw [addc_true_one_bit0, succ_bit1, succ_bit1, succ_one]

theorem carry_true_right_terminal :
    addc true (.bit0 (.bit1 (.bit1 .one))) .one = .bit0 (.bit0 (.bit0 (.bit0 .one))) := by
  rw [addc_true_bit0_one, succ_bit1, succ_bit1, succ_one]

theorem carry_true_both_odd :
    addc true (.bit1 .one) (.bit1 .one) = .bit1 (.bit1 .one) := by
  rw [addc_true_bit1_bit1, addc_true_one_one]

theorem carry_false_mixed :
    addc false (.bit1 .one) (.bit0 .one) = .bit1 (.bit0 .one) := by
  rw [addc_false_bit1_bit0, addc_false_one_one]

theorem carry_true_mixed :
    addc true (.bit1 .one) (.bit0 .one) = .bit0 (.bit1 .one) := by
  rw [addc_true_bit1_bit0, addc_true_one_one]

/-- Thirteen plus two remains four bits; the incoming carry produces sixteen. -/
def thirteen : PosNum := .bit1 (.bit0 (.bit1 .one))

theorem unequal_false : addc false thirteen (.bit0 .one) = .bit1 (.bit1 (.bit1 .one)) := by
  unfold thirteen
  rw [addc_false_bit1_bit0, addc_false_bit0_one]

theorem unequal_true : addc true thirteen (.bit0 .one) = .bit0 (.bit0 (.bit0 (.bit0 .one))) := by
  unfold thirteen
  rw [addc_true_bit1_bit0, addc_true_bit0_one, succ_bit1, succ_one]

theorem carry_numeric_ten_three : numeric (addc true ten (.bit1 .one)) = 14 := by
  rw [addc_correct, ten_numeric, numeric_bit1, numeric_one]
  rfl

theorem source_add_ten_three : numeric (Numerals.PositiveArithmetic.add ten (.bit1 .one)) = 13 := by
  rw [add_correct, ten_numeric, numeric_bit1, numeric_one]

theorem source_add_uses_existing_add : Numerals.PositiveArithmetic.add ten (.bit1 .one) = ten + .bit1 .one :=
  add_eq_add _ _

theorem incoming_carry_uses_existing_sum : addc true ten (.bit1 .one) = succ (ten + .bit1 .one) :=
  addc_true_eq_succ_add _ _

theorem mixed_equal_high_bits_odd : Numerals.PositiveArithmetic.compare (.bit1 .one) (.bit0 .one) = .gt := by
  rw [compare_bit1_bit0, compare_one_one]

theorem mixed_equal_high_bits_even : Numerals.PositiveArithmetic.compare (.bit0 .one) (.bit1 .one) = .lt := by
  rw [compare_bit0_bit1, compare_one_one]

theorem mixed_high_bits_override_odd : Numerals.PositiveArithmetic.compare (.bit1 .one) (.bit0 (.bit0 .one)) = .lt := by
  rw [compare_bit1_bit0, compare_one_bit0]

theorem mixed_high_bits_override_even : Numerals.PositiveArithmetic.compare (.bit0 (.bit0 .one)) (.bit1 .one) = .gt := by
  rw [compare_bit0_bit1, compare_bit0_one]

theorem comparison_numeric_three_four : numeric (.bit1 .one) < numeric (.bit0 (.bit0 .one)) := by
  have h := compare_correct (.bit1 .one) (.bit0 (.bit0 .one))
  rw [mixed_high_bits_override_odd] at h
  exact h

theorem comparison_equal_keys (p q : PosNum) (h : Numerals.PositiveArithmetic.compare p q = .eq) : p = q :=
  (compare_eq_iff p q).mp h

/-- The source's catch-all `.lt` cannot satisfy its own specification at one/one. -/
theorem placeholder_boundary : Numerals.PositiveArithmetic.compare .one .one = .eq ∧ ¬ numeric .one < numeric .one :=
  ⟨compare_one_one, Nat.lt_irrefl _⟩

theorem ten_digits : digits ten = [false, true, false, true] := by
  simp only [ten, digits_bit0, digits_bit1, digits_one]

theorem ten_print : printInBinary ten = [1, 0, 1, 0] := by
  rw [ten, printInBinary_bit0, printInBinary_bit1, printInBinary_bit0, printInBinary_one]
  rfl

theorem ten_bits_adapter : ((numeric ten).bits.reverse).map Bool.toNat = [1, 0, 1, 0] :=
  (printInBinary_eq_bits ten).symm.trans ten_print

theorem ten_four_digits : bitLength ten = 4 := by
  calc
    bitLength ten = (printInBinary ten).length := (printInBinary_length ten).symm
    _ = 4 := by rw [ten_print]; rfl

theorem ten_print_digits (d : Nat) (h : d ∈ printInBinary ten) : d = 0 ∨ d = 1 :=
  printInBinary_digit ten d h

theorem one_log_endpoint : bitLength .one = 1 ∧ Nat.log2 (numeric .one) = 0 := by
  have h := bitLength_eq_log2 .one
  rw [bitLength_one] at h
  exact ⟨bitLength_one, by omega⟩

def eight : PosNum := .bit0 (.bit0 (.bit0 .one))

theorem eight_numeric : numeric eight = 2 ^ 3 := by
  rw [eight, numeric_bit0, numeric_bit0, numeric_bit0, numeric_one]
  rfl

theorem eight_power_endpoint : bitLength eight = 4 :=
  bitLength_of_numeric_eq_pow eight 3 eight_numeric

theorem eight_power_bounds : 2 ^ (bitLength eight - 1) = numeric eight ∧ numeric eight < 2 ^ bitLength eight := by
  refine ⟨?_, numeric_lt_pow_bitLength eight⟩
  rw [eight_power_endpoint, eight_numeric]

theorem ten_power_bounds : 2 ^ (bitLength ten - 1) ≤ numeric ten ∧ numeric ten < 2 ^ bitLength ten :=
  ⟨pow_bitLength_pred_le ten, numeric_lt_pow_bitLength ten⟩

theorem both_carry_size_bounds (c : Bool) :
    4 ≤ bitLength (addc c thirteen (.bit0 .one)) ∧
      bitLength (addc c thirteen (.bit0 .one)) ≤ 5 := by
  have lower := max_bitLength_le_addc c thirteen (.bit0 .one)
  have upper := addc_bitLength_le c thirteen (.bit0 .one)
  simp only [thirteen, bitLength_bit0, bitLength_bit1, bitLength_one] at lower upper
  exact ⟨lower, upper⟩

theorem unequal_carry_size_endpoints :
    bitLength (addc false thirteen (.bit0 .one)) = 4 ∧
      bitLength (addc true thirteen (.bit0 .one)) = 5 := by
  rw [unequal_false, unequal_true]
  simp only [bitLength_bit0, bitLength_bit1, bitLength_one]
  decide

end Examples.PositiveNumbers
