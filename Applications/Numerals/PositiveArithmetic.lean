import Applications.Numerals.PositiveKeys
import Mathlib.Data.Nat.Log

/-!
# Source arithmetic and digit observations for positive binary numbers

Successor and completed comparison reuse the existing `PosNum` operations.
Carry addition follows all eighteen source branches, including successor on
the strict child of a remaining terminal-side operand. Its numeric theorem
connects this recurrence to existing addition without identifying their work.

The printer retains the source append-singleton equations. Its digit adapter
and the bit-length bounds describe values and sizes, not execution costs.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Numerals.PositiveArithmetic

open PositiveKeys

/-- The existing successor has exactly the source's three cases. -/
abbrev succ : PosNum → PosNum := PosNum.succ

@[simp] theorem succ_one : succ .one = .bit0 .one := rfl

@[simp] theorem succ_bit0 (p : PosNum) : succ (.bit0 p) = .bit1 p := rfl

@[simp] theorem succ_bit1 (p : PosNum) : succ (.bit1 p) = .bit0 (succ p) := rfl

theorem succ_correct (p : PosNum) : numeric (succ p) = numeric p + 1 :=
  PosNum.succ_to_nat p

/-- Carry addition in the source branch order, with both terminal orientations. -/
def addc : Bool → PosNum → PosNum → PosNum
  | false, .bit1 p, .bit1 q => .bit0 (addc true p q)
  | false, .bit1 p, .bit0 q => .bit1 (addc false p q)
  | false, .bit1 p, .one => .bit0 (succ p)
  | false, .bit0 p, .bit1 q => .bit1 (addc false p q)
  | false, .bit0 p, .bit0 q => .bit0 (addc false p q)
  | false, .bit0 p, .one => .bit1 p
  | false, .one, .bit1 q => .bit0 (succ q)
  | false, .one, .bit0 q => .bit1 q
  | false, .one, .one => .bit0 .one
  | true, .bit1 p, .bit1 q => .bit1 (addc true p q)
  | true, .bit1 p, .bit0 q => .bit0 (addc true p q)
  | true, .bit1 p, .one => .bit1 (succ p)
  | true, .bit0 p, .bit1 q => .bit0 (addc true p q)
  | true, .bit0 p, .bit0 q => .bit1 (addc false p q)
  | true, .bit0 p, .one => .bit0 (succ p)
  | true, .one, .bit1 q => .bit1 (succ q)
  | true, .one, .bit0 q => .bit0 (succ q)
  | true, .one, .one => .bit1 .one
termination_by structural _ p _ => p

@[simp] theorem addc_false_bit1_bit1 (p q : PosNum) :
    addc false (.bit1 p) (.bit1 q) = .bit0 (addc true p q) := rfl

@[simp] theorem addc_false_bit1_bit0 (p q : PosNum) :
    addc false (.bit1 p) (.bit0 q) = .bit1 (addc false p q) := rfl

@[simp] theorem addc_false_bit1_one (p : PosNum) :
    addc false (.bit1 p) .one = .bit0 (succ p) := rfl

@[simp] theorem addc_false_bit0_bit1 (p q : PosNum) :
    addc false (.bit0 p) (.bit1 q) = .bit1 (addc false p q) := rfl

@[simp] theorem addc_false_bit0_bit0 (p q : PosNum) :
    addc false (.bit0 p) (.bit0 q) = .bit0 (addc false p q) := rfl

@[simp] theorem addc_false_bit0_one (p : PosNum) :
    addc false (.bit0 p) .one = .bit1 p := rfl

@[simp] theorem addc_false_one_bit1 (q : PosNum) :
    addc false .one (.bit1 q) = .bit0 (succ q) := rfl

@[simp] theorem addc_false_one_bit0 (q : PosNum) :
    addc false .one (.bit0 q) = .bit1 q := rfl

@[simp] theorem addc_false_one_one : addc false .one .one = .bit0 .one := rfl

@[simp] theorem addc_true_bit1_bit1 (p q : PosNum) :
    addc true (.bit1 p) (.bit1 q) = .bit1 (addc true p q) := rfl

@[simp] theorem addc_true_bit1_bit0 (p q : PosNum) :
    addc true (.bit1 p) (.bit0 q) = .bit0 (addc true p q) := rfl

@[simp] theorem addc_true_bit1_one (p : PosNum) :
    addc true (.bit1 p) .one = .bit1 (succ p) := rfl

@[simp] theorem addc_true_bit0_bit1 (p q : PosNum) :
    addc true (.bit0 p) (.bit1 q) = .bit0 (addc true p q) := rfl

@[simp] theorem addc_true_bit0_bit0 (p q : PosNum) :
    addc true (.bit0 p) (.bit0 q) = .bit1 (addc false p q) := rfl

@[simp] theorem addc_true_bit0_one (p : PosNum) :
    addc true (.bit0 p) .one = .bit0 (succ p) := rfl

@[simp] theorem addc_true_one_bit1 (q : PosNum) :
    addc true .one (.bit1 q) = .bit1 (succ q) := rfl

@[simp] theorem addc_true_one_bit0 (q : PosNum) :
    addc true .one (.bit0 q) = .bit0 (succ q) := rfl

@[simp] theorem addc_true_one_one : addc true .one .one = .bit1 .one := rfl

theorem addc_correct (c : Bool) (p q : PosNum) :
    numeric (addc c p q) = (if c then 1 else 0) + numeric p + numeric q := by
  induction p generalizing c q with
  | one =>
    cases q <;> cases c <;>
      simp only [addc, succ_correct, numeric_one, numeric_bit0, numeric_bit1, Bool.false_eq_true,
        ite_false, ite_true] <;> omega
  | bit1 p ih =>
    cases q <;> cases c <;>
      simp only [addc, succ_correct, numeric_one, numeric_bit0, numeric_bit1, ih,
        Bool.false_eq_true, ite_false, ite_true] <;> omega
  | bit0 p ih =>
    cases q <;> cases c <;>
      simp only [addc, succ_correct, numeric_one, numeric_bit0, numeric_bit1, ih,
        Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- Source addition starts with carry false. -/
def add (p q : PosNum) : PosNum := addc false p q

theorem add_correct (p q : PosNum) : numeric (add p q) = numeric p + numeric q := by
  simpa only [add, Bool.false_eq_true, ite_false, Nat.zero_add] using addc_correct false p q

theorem add_eq_add (p q : PosNum) : add p q = p + q := by
  apply numeric_injective
  exact (add_correct p q).trans (PosNum.add_to_nat p q).symm

theorem addc_true_eq_succ_add (p q : PosNum) : addc true p q = succ (p + q) := by
  apply numeric_injective
  rw [addc_correct, succ_correct]
  have hadd : numeric (p + q) = numeric p + numeric q := PosNum.add_to_nat p q
  rw [hadd]
  simp only [ite_true]
  omega

/-- The existing comparison completes the source exercise. -/
abbrev compare : PosNum → PosNum → Ordering := PosNum.cmp

@[simp] theorem compare_one_one : compare .one .one = .eq := rfl

@[simp] theorem compare_one_bit0 (q : PosNum) : compare .one (.bit0 q) = .lt := rfl

@[simp] theorem compare_one_bit1 (q : PosNum) : compare .one (.bit1 q) = .lt := rfl

@[simp] theorem compare_bit0_one (p : PosNum) : compare (.bit0 p) .one = .gt := rfl

@[simp] theorem compare_bit1_one (p : PosNum) : compare (.bit1 p) .one = .gt := rfl

@[simp] theorem compare_bit0_bit0 (p q : PosNum) :
    compare (.bit0 p) (.bit0 q) = compare p q := rfl

@[simp] theorem compare_bit1_bit1 (p q : PosNum) :
    compare (.bit1 p) (.bit1 q) = compare p q := rfl

theorem compare_bit1_bit0 (p q : PosNum) :
    compare (.bit1 p) (.bit0 q) = match compare p q with | .lt => .lt | _ => .gt := by
  change (Ordering.casesOn (compare p q) .lt .gt .gt : Ordering) = _
  cases compare p q <;> rfl

theorem compare_bit0_bit1 (p q : PosNum) :
    compare (.bit0 p) (.bit1 q) = match compare p q with | .gt => .gt | _ => .lt := by
  change (Ordering.casesOn (compare p q) .lt .lt .gt : Ordering) = _
  cases compare p q <;> rfl

/-- In the equal branch the actual binary keys agree. -/
theorem compare_keys (p q : PosNum) :
    match compare p q with
    | .lt => numeric p < numeric q
    | .eq => p = q
    | .gt => numeric q < numeric p := by
  have h := PosNum.cmp_to_nat p q
  cases hc : PosNum.cmp p q <;> simpa only [compare, hc] using h

theorem compare_correct (p q : PosNum) :
    match compare p q with
    | .lt => numeric p < numeric q
    | .eq => numeric p = numeric q
    | .gt => numeric q < numeric p := by
  have h := compare_keys p q
  cases hc : compare p q <;> simp only [hc] at h ⊢
  · exact h
  · exact congrArg numeric h
  · exact h

theorem compare_eq_iff (p q : PosNum) : compare p q = .eq ↔ p = q :=
  cmp_eq_iff p q

/-- Low bits first, including the final one. This is an observation of numeric value. -/
abbrev digits (p : PosNum) : List Bool := (numeric p).bits

@[simp] theorem digits_one : digits .one = [true] := Nat.one_bits

@[simp] theorem digits_bit0 (p : PosNum) : digits (.bit0 p) = false :: digits p := by
  change (numeric (.bit0 p)).bits = false :: (numeric p).bits
  rw [numeric_bit0, Nat.zero_add, Nat.bit0_bits _ (Nat.ne_of_gt (numeric_pos p))]

@[simp] theorem digits_bit1 (p : PosNum) : digits (.bit1 p) = true :: digits p := by
  change (numeric (.bit1 p)).bits = true :: (numeric p).bits
  rw [numeric_bit1, Nat.add_comm 1, Nat.bit1_bits]

/-- The literal source printer appends the next low digit after the child's display. -/
def printInBinary : PosNum → List Nat
  | .one => [1]
  | .bit0 p => printInBinary p ++ [0]
  | .bit1 p => printInBinary p ++ [1]

@[simp] theorem printInBinary_one : printInBinary .one = [1] := rfl

@[simp] theorem printInBinary_bit0 (p : PosNum) :
    printInBinary (.bit0 p) = printInBinary p ++ [0] := rfl

@[simp] theorem printInBinary_bit1 (p : PosNum) :
    printInBinary (.bit1 p) = printInBinary p ++ [1] := rfl

theorem printInBinary_eq_bits (p : PosNum) :
    printInBinary p = ((numeric p).bits.reverse).map Bool.toNat := by
  change printInBinary p = (digits p).reverse.map Bool.toNat
  induction p with
  | one => rw [printInBinary_one, digits_one]; rfl
  | bit0 p ih => rw [printInBinary_bit0, digits_bit0, List.reverse_cons, List.map_append, ← ih]; rfl
  | bit1 p ih => rw [printInBinary_bit1, digits_bit1, List.reverse_cons, List.map_append, ← ih]; rfl

theorem printInBinary_digit (p : PosNum) (d : Nat) (h : d ∈ printInBinary p) : d = 0 ∨ d = 1 := by
  rw [printInBinary_eq_bits] at h
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp h
  cases b <;> simp

theorem printInBinary_leading_one (p : PosNum) : ∃ tail, printInBinary p = 1 :: tail := by
  induction p with
  | one => exact ⟨[], rfl⟩
  | bit0 p ih =>
    obtain ⟨tail, ht⟩ := ih
    exact ⟨tail ++ [0], by rw [printInBinary_bit0, ht]; rfl⟩
  | bit1 p ih =>
    obtain ⟨tail, ht⟩ := ih
    exact ⟨tail ++ [1], by rw [printInBinary_bit1, ht]; rfl⟩

theorem digits_final_one (p : PosNum) : ∃ front, digits p = front ++ [true] := by
  induction p with
  | one => exact ⟨[], digits_one⟩
  | bit0 p ih =>
    obtain ⟨front, hp⟩ := ih
    exact ⟨false :: front, by rw [digits_bit0, hp]; rfl⟩
  | bit1 p ih =>
    obtain ⟨front, hp⟩ := ih
    exact ⟨true :: front, by rw [digits_bit1, hp]; rfl⟩

/-- The existing size counts binary digits including the terminal one. -/
abbrev bitLength : PosNum → Nat := PosNum.natSize

@[simp] theorem bitLength_one : bitLength .one = 1 := rfl

@[simp] theorem bitLength_bit0 (p : PosNum) : bitLength (.bit0 p) = bitLength p + 1 := rfl

@[simp] theorem bitLength_bit1 (p : PosNum) : bitLength (.bit1 p) = bitLength p + 1 := rfl

theorem bitLength_pos (p : PosNum) : 0 < bitLength p := PosNum.natSize_pos p

theorem bitLength_eq_size (p : PosNum) : bitLength p = Nat.size (numeric p) :=
  PosNum.natSize_to_nat p

theorem digits_length (p : PosNum) : (digits p).length = bitLength p :=
  (Nat.size_eq_bits_len (numeric p)).trans (bitLength_eq_size p).symm

theorem digits_nonempty (p : PosNum) : digits p ≠ [] := by
  intro h
  have hl := digits_length p
  rw [h] at hl
  have hp := bitLength_pos p
  simp only [List.length_nil] at hl
  omega

theorem printInBinary_length (p : PosNum) : (printInBinary p).length = bitLength p := by
  rw [printInBinary_eq_bits, List.length_map, List.length_reverse]
  exact digits_length p

theorem pow_bitLength_pred_le (p : PosNum) : 2 ^ (bitLength p - 1) ≤ numeric p := by
  apply Nat.lt_size.mp
  rw [← bitLength_eq_size]
  have hp := bitLength_pos p
  omega

theorem numeric_lt_pow_bitLength (p : PosNum) : numeric p < 2 ^ bitLength p := by
  rw [bitLength_eq_size]
  exact Nat.lt_size_self _

theorem bitLength_eq_log (p : PosNum) : bitLength p = Nat.log 2 (numeric p) + 1 := by
  have hp := bitLength_pos p
  have hupper : numeric p < 2 ^ ((bitLength p - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ bitLength p)]
    exact numeric_lt_pow_bitLength p
  have hlog := Nat.log_eq_of_pow_le_of_lt_pow (pow_bitLength_pred_le p) hupper
  omega

theorem bitLength_eq_log2 (p : PosNum) : bitLength p = Nat.log2 (numeric p) + 1 := by
  rw [Nat.log2_eq_log_two]
  exact bitLength_eq_log p

theorem bitLength_of_numeric_eq_pow (p : PosNum) (n : Nat) (h : numeric p = 2 ^ n) :
    bitLength p = n + 1 := by
  rw [bitLength_eq_size, h, Nat.size_pow]

theorem bitLength_mono {p q : PosNum} (h : numeric p ≤ numeric q) : bitLength p ≤ bitLength q := by
  rw [bitLength_eq_size, bitLength_eq_size]
  exact Nat.size_le_size h

theorem max_bitLength_le_addc (c : Bool) (p q : PosNum) :
    max (bitLength p) (bitLength q) ≤ bitLength (addc c p q) := by
  apply max_le
  · apply bitLength_mono
    rw [addc_correct]
    omega
  · apply bitLength_mono
    rw [addc_correct]
    omega

theorem addc_bitLength_le (c : Bool) (p q : PosNum) :
    bitLength (addc c p q) ≤ max (bitLength p) (bitLength q) + 1 := by
  have hp : numeric p < 2 ^ max (bitLength p) (bitLength q) :=
    Nat.size_le.mp (by rw [← bitLength_eq_size]; exact le_max_left _ _)
  have hq : numeric q < 2 ^ max (bitLength p) (bitLength q) :=
    Nat.size_le.mp (by rw [← bitLength_eq_size]; exact le_max_right _ _)
  rw [bitLength_eq_size]
  apply Nat.size_le.mpr
  rw [addc_correct, Nat.pow_succ]
  cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

end Numerals.PositiveArithmetic
