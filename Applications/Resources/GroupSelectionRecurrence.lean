import Applications.Resources.RoundedRecurrenceBounds
import Applications.Resources.Growth

/-! Group-size arithmetic and total scalar majorants for FDSA Exercise 3.8.

The half-size parameter is natural division before casting. The precise
two-group count bound implies the rounded child bound with an explicit
additive group-size allowance. For positive group size, the sum of recursive
fractions is less than one exactly from size five onward. Equality at three
or four only describes this sufficient recurrence argument.

The natural majorant is defined after proving both children decrease above
its explicit cutoff. Its uniform affine bound uses the checked rounded
recurrence theorem. A measured algorithm must separately establish its cost
comparison; this scalar is not itself an execution or source-call count.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.GroupSelectionRecurrence

noncomputable section

def pivotFraction (d : Nat) : ℝ := 1 / (d : ℝ)

def sideFraction (d : Nat) : ℝ :=
  ((d : ℝ) + ((d / 2 : Nat) : ℝ)) / (2 * (d : ℝ))

theorem fractions_pos (d : Nat) (hd : 0 < d) :
    0 < pivotFraction d ∧ 0 < sideFraction d := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  constructor
  · unfold pivotFraction
    positivity
  · unfold sideFraction
    positivity

theorem fraction_sum_eq (d : Nat) (hd : 0 < d) :
    pivotFraction d + sideFraction d =
      ((d : ℝ) + ((d / 2 : Nat) : ℝ) + 2) / (2 * (d : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  unfold pivotFraction sideFraction
  field_simp
  ring

/-- The subtraction is natural subtraction; its cast is justified explicitly. -/
theorem contracts_iff_half_gap (d : Nat) (hd : 0 < d) :
    pivotFraction d + sideFraction d < 1 ↔ 2 < d - d / 2 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsub : ((d - d / 2 : Nat) : ℝ) = (d : ℝ) - ((d / 2 : Nat) : ℝ) :=
    Nat.cast_sub (Nat.div_le_self d 2)
  rw [fraction_sum_eq d hd, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))]
  constructor
  · intro h
    have hr : (2 : ℝ) < ((d - d / 2 : Nat) : ℝ) := by rw [hsub]; linarith
    exact_mod_cast hr
  · intro h
    have hr : (2 : ℝ) < ((d - d / 2 : Nat) : ℝ) := by exact_mod_cast h
    rw [hsub] at hr
    linarith

theorem contracts_iff_five_le (d : Nat) (hd : 0 < d) :
    pivotFraction d + sideFraction d < 1 ↔ 5 ≤ d := by
  rw [contracts_iff_half_gap d hd]
  omega

/-- Among odd positive sizes, five is the smallest sufficient size. -/
theorem odd_contracts_iff (r : Nat) :
    pivotFraction (2 * r + 1) + sideFraction (2 * r + 1) < 1 ↔ 2 ≤ r := by
  rw [contracts_iff_five_le _ (by omega)]
  omega

/-- Among even positive sizes, six is the smallest sufficient size. -/
theorem even_contracts_iff (r : Nat) (hr : 0 < r) :
    pivotFraction (2 * r) + sideFraction (2 * r) < 1 ↔ 3 ≤ r := by
  rw [contracts_iff_five_le _ (by omega)]
  omega

def pivotChild (d n : Nat) : Nat := ⌈pivotFraction d * (n : ℝ) + 0⌉₊

def sideChild (d n : Nat) : Nat := ⌈sideFraction d * (n : ℝ) + (d : ℝ)⌉₊

/-- A group of size one leaves the first recursive problem unchanged. -/
theorem pivotChild_one (n : Nat) : pivotChild 1 n = n := by
  simp [pivotChild, pivotFraction]

theorem pivotChild_monotone (d : Nat) : Monotone (pivotChild d) := by
  intro m n h
  apply Nat.ceil_mono
  have hm : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  exact add_le_add_right (mul_le_mul_of_nonneg_left hm (by unfold pivotFraction; positivity : (0 : ℝ) ≤ pivotFraction d)) 0

theorem sideChild_monotone (d : Nat) : Monotone (sideChild d) := by
  intro m n h
  apply Nat.ceil_mono
  have hm : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  exact add_le_add_right (mul_le_mul_of_nonneg_left hm (by unfold sideFraction; positivity : (0 : ℝ) ≤ sideFraction d)) _

/-- Transport the exact two-group bound, retaining the final short chunk.
The same arithmetic applies separately to the less-than and greater-than sides. -/
theorem two_group_bound_le_child (d n s : Nat) (hd : 0 < d)
    (bound : s ≤ (d / 2) * pivotChild d n +
      (d - d / 2) * (pivotChild d n / 2)) : s ≤ sideChild d n := by
  let m := pivotChild d n
  have hq : d / 2 ≤ d := Nat.div_le_self d 2
  have hhalf : 2 * (m / 2) ≤ m := by omega
  have hscaled := Nat.mul_le_mul_left (d - d / 2) hhalf
  have hsplit : (d - d / 2) * m + (d / 2) * m = d * m := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hq]
  have hdouble : 2 * s ≤ (d + d / 2) * m := by
    change s ≤ (d / 2) * m + (d - d / 2) * (m / 2) at bound
    nlinarith
  have hm : (m : ℝ) ≤ pivotFraction d * (n : ℝ) + 1 := by
    dsimp [m, pivotChild]
    simpa only [add_zero] using
      (Nat.ceil_lt_add_one (by unfold pivotFraction; positivity :
        (0 : ℝ) ≤ pivotFraction d * (n : ℝ))).le
  have hdoubleR : 2 * (s : ℝ) ≤ ((d : ℝ) + ((d / 2 : Nat) : ℝ)) * (m : ℝ) := by
    exact_mod_cast hdouble
  have hmul := mul_le_mul_of_nonneg_left hm
    (by positivity : (0 : ℝ) ≤ (d : ℝ) + ((d / 2 : Nat) : ℝ))
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hfrac : ((d : ℝ) + ((d / 2 : Nat) : ℝ)) * pivotFraction d =
      2 * sideFraction d := by
    unfold pivotFraction sideFraction
    field_simp
  have expand : ((d : ℝ) + ((d / 2 : Nat) : ℝ)) *
      (pivotFraction d * (n : ℝ) + 1) =
      2 * sideFraction d * (n : ℝ) + ((d : ℝ) + ((d / 2 : Nat) : ℝ)) := by
    rw [mul_add, mul_one, ← mul_assoc, hfrac]
  have hqR : ((d / 2 : Nat) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hq
  rw [expand] at hmul
  have hs : (s : ℝ) ≤ sideFraction d * (n : ℝ) + (d : ℝ) := by nlinarith
  apply (Nat.cast_le (α := ℝ)).mp
  exact hs.trans (Nat.le_ceil _)

/-- The extra one makes the combined rounded-child threshold strict. -/
def cutoff (d : Nat) : Nat :=
  ⌈((d : ℝ) + 2) / (1 - pivotFraction d - sideFraction d)⌉₊ + 1

theorem cutoff_threshold (d : Nat) :
    (max 0 (0 : ℝ) + max 0 (d : ℝ) + 2) /
      (1 - pivotFraction d - sideFraction d) < (cutoff d : ℝ) := by
  have h := (RoundedRecurrence.explicit_cutoff_bounds
    (pivotFraction d) 0 (sideFraction d) (d : ℝ) 0).2
  simpa [cutoff, max_eq_right (Nat.cast_nonneg d)] using h

theorem children_lt (d n : Nat) (hd : 5 ≤ d) (large : cutoff d < n) :
    pivotChild d n < n ∧ sideChild d n < n :=
  RoundedRecurrence.ceil_children_lt (pivotFraction d) 0 (sideFraction d) d
    (cutoff d) n (fractions_pos d (by omega)).1 (fractions_pos d (by omega)).2
    ((contracts_iff_five_le d (by omega)).mpr hd) (cutoff_threshold d) large

/-- A total scalar family, with explicit finite base and natural linear toll.
Termination is established by child decrease before affine growth is used. -/
def majorant (d base slope constant : Nat) (hd : 5 ≤ d) (n : Nat) : Nat :=
  if _h : n ≤ cutoff d then base else
    majorant d base slope constant hd (pivotChild d n) +
      majorant d base slope constant hd (sideChild d n) + slope * n + constant
termination_by n
decreasing_by
  · exact (children_lt d n hd (Nat.lt_of_not_ge _h)).1
  · exact (children_lt d n hd (Nat.lt_of_not_ge _h)).2

theorem majorant_small (d base slope constant : Nat) (hd : 5 ≤ d)
    (n : Nat) (small : n ≤ cutoff d) : majorant d base slope constant hd n = base := by
  rw [majorant]
  split
  · rfl
  · rename_i h
    exact (h small).elim

theorem majorant_large (d base slope constant : Nat) (hd : 5 ≤ d)
    (n : Nat) (large : cutoff d < n) :
    majorant d base slope constant hd n =
      majorant d base slope constant hd (pivotChild d n) +
        majorant d base slope constant hd (sideChild d n) + slope * n + constant := by
  rw [majorant]
  split
  · rename_i h
    exact ((not_le_of_gt large) h).elim
  · rfl

theorem base_le_majorant (d base slope constant : Nat) (hd : 5 ≤ d) (n : Nat) :
    base ≤ majorant d base slope constant hd n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases h : n ≤ cutoff d
      · rw [majorant_small d base slope constant hd n h]
      · have large : cutoff d < n := Nat.lt_of_not_ge h
        have child := ih (pivotChild d n) (children_lt d n hd large).1
        rw [majorant_large d base slope constant hd n large]
        omega

theorem majorant_monotone (d base slope constant : Nat) (hd : 5 ≤ d) :
    Monotone (majorant d base slope constant hd) := by
  have compare : ∀ n m : Nat, m ≤ n →
      majorant d base slope constant hd m ≤ majorant d base slope constant hd n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro m hmn
        by_cases hn : n ≤ cutoff d
        · rw [majorant_small d base slope constant hd m (hmn.trans hn),
            majorant_small d base slope constant hd n hn]
        · by_cases hm : m ≤ cutoff d
          · rw [majorant_small d base slope constant hd m hm]
            exact base_le_majorant d base slope constant hd n
          · have ln : cutoff d < n := Nat.lt_of_not_ge hn
            have lm : cutoff d < m := Nat.lt_of_not_ge hm
            have left := ih (pivotChild d n) (children_lt d n hd ln).1
              (pivotChild d m) (pivotChild_monotone d hmn)
            have right := ih (sideChild d n) (children_lt d n hd ln).2
              (sideChild d m) (sideChild_monotone d hmn)
            have toll := Nat.mul_le_mul_left slope hmn
            rw [majorant_large d base slope constant hd m lm,
              majorant_large d base slope constant hd n ln]
            omega
  intro m n h
  exact compare n m h

/-- A fixed sufficient group size, base and toll give one pair of constants
for every natural input, including zero and the entire finite prefix. -/
theorem majorant_affine_bound (d base slope constant : Nat) (hd : 5 ≤ d) :
    ∃ A B : Nat, ∀ n : Nat, majorant d base slope constant hd n ≤ A * n + B :=
  RoundedRecurrence.exists_affine_bound_nat (majorant d base slope constant hd)
    (pivotFraction d) 0 (sideFraction d) d slope constant (cutoff d)
    (fractions_pos d (by omega)).1 (fractions_pos d (by omega)).2
    ((contracts_iff_five_le d (by omega)).mpr hd)
    (majorant_large d base slope constant hd)

theorem majorant_isBigO (d base slope constant : Nat) (hd : 5 ≤ d) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => (majorant d base slope constant hd n : ℝ)) (fun n => (n : ℝ)) := by
  obtain ⟨A, B, bound⟩ := majorant_affine_bound d base slope constant hd
  apply isBigO_of_nat_bound (majorant d base slope constant hd) (fun n => n) (A + B) 1
  intro n hn
  have hb : B ≤ B * n := by nlinarith
  calc
    majorant d base slope constant hd n ≤ A * n + B := bound n
    _ ≤ (A + B) * n := by nlinarith

/-- Arbitrary signed offsets can also be retained when an exact scalar
recurrence has already been established. No desired growth bound is assumed. -/
theorem rounded_group_affine_bound (f : Nat → Nat) (d : Nat) (hd : 5 ≤ d)
    (leftOffset rightOffset : ℝ) (slope constant n0 : Nat)
    (recurrence : ∀ n, n0 < n →
      f n = f ⌈pivotFraction d * (n : ℝ) + leftOffset⌉₊ +
        f ⌈sideFraction d * (n : ℝ) + rightOffset⌉₊ + slope * n + constant) :
    ∃ A B : Nat, ∀ n : Nat, f n ≤ A * n + B :=
  RoundedRecurrence.exists_affine_bound_nat f (pivotFraction d) leftOffset
    (sideFraction d) rightOffset slope constant n0
    (fractions_pos d (by omega)).1 (fractions_pos d (by omega)).2
    ((contracts_iff_five_le d (by omega)).mpr hd) recurrence

end
end Resources.GroupSelectionRecurrence
