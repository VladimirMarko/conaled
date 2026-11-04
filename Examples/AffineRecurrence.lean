import Applications.Resources.AffineRecurrence
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Connected scalar recurrence clients and quantifier boundaries.

The independently calculated quarter-recurrence values at 0, 1, 2, 4, 8, 16
are 1, 1, 5, 7, 19, 31. Its recursive definition must terminate at its own
cutoff, before the generic affine theorem enlarges any proof prefix. This
scalar example is not a selector implementation or an inferred execution cost.
Provenance and statement review: `docs/research/fdsa-affine-recurrence.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.AffineRecurrence
open Resources.AffineRecurrence

/-- The natural scalar recurrence Q from the shared unit's worked example. -/
def quarter (n : Nat) : Nat :=
  if h : n ≤ 1 then 1 else 2 * quarter (n / 4) + n + 1
termination_by n
decreasing_by
  exact Nat.div_lt_self (by omega) (by decide)

theorem quarter_of_le_one (n : Nat) (small : n ≤ 1) : quarter n = 1 := by
  rw [quarter]
  split
  · rfl
  · omega

theorem quarter_of_one_lt (n : Nat) (large : 1 < n) :
    quarter n = 2 * quarter (n / 4) + n + 1 := by
  rw [quarter]
  split
  · omega
  · rfl

theorem quarter_zero : quarter 0 = 1 := quarter_of_le_one 0 (by decide)
theorem quarter_one : quarter 1 = 1 := quarter_of_le_one 1 (by decide)

theorem quarter_two : quarter 2 = 5 := by
  rw [quarter_of_one_lt 2 (by decide)]
  norm_num [quarter_zero]

theorem quarter_four : quarter 4 = 7 := by
  rw [quarter_of_one_lt 4 (by decide)]
  norm_num [quarter_one]

theorem quarter_eight : quarter 8 = 19 := by
  rw [quarter_of_one_lt 8 (by decide)]
  norm_num [quarter_two]

theorem quarter_sixteen : quarter 16 = 31 := by
  rw [quarter_of_one_lt 16 (by decide)]
  norm_num [quarter_four]

/-- Apply the shared theorem to Q's actual branch equation and rounded sizes.
The two children sum to at most n/2, even when n is not divisible by four. -/
theorem quarter_affine_bound :
    ∃ A B : ℚ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ n : Nat, (quarter n : ℚ) ≤ A * (n : ℚ) + B := by
  refine exists_affine_bound_of_two_branch
    (fun n => (quarter n : ℚ)) (fun n => n / 4) (fun n => n / 4)
    1 (1 / 2) 0 1 1 (by norm_num) ?_ ?_
  · intro n _
    have divided : ((n / 4 : Nat) : ℚ) * 4 ≤ (n : ℚ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.cast_le (α := ℚ)).mpr (Nat.div_mul_le_self n 4)
    nlinarith only [divided]
  · intro n hn
    rw [quarter_of_one_lt n hn]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    linarith

/-- Negative function values and a negative linear toll over an integer ring. -/
def signed (n : Nat) : Int := -(n : Int) - 1

theorem signed_base : signed 0 = -1 := rfl

theorem signed_nonpositive (n : Nat) : signed n ≤ 0 := by
  have nonneg : (0 : Int) ≤ (n : Int) := Nat.cast_nonneg n
  simp only [signed]
  omega

theorem signed_recurrence (n : Nat) :
    signed n = signed 0 + signed 0 + (-1) * (n : Int) + 1 := by
  simp only [signed, Nat.cast_zero]
  ring

/-- This client cannot obtain its scalar instance from a field requirement.
Its local toll is 1-n and becomes negative; its base is already negative. -/
theorem signed_affine_bound :
    ∃ A B : Int, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ n : Nat, signed n ≤ A * (n : Int) + B := by
  refine exists_affine_bound_of_two_branch signed (fun _ => 0) (fun _ => 0)
    0 0 0 (-1) 1 (by decide) ?_ ?_
  · intro n _
    simp
  · intro n _
    exact (signed_recurrence n).le

/-- A one-sided signed bound does not control the absolute value. -/
theorem negative_square_upper {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (n : Nat) : -((n : R) ^ 2) ≤ 0 := by
  nlinarith only [sq_nonneg (n : R)]

theorem negative_square_absolute_value :
    -((2 : Int) ^ 2) ≤ 0 ∧ | -((2 : Int) ^ 2)| = 4 := by
  norm_num

/-- The same recurrence parameters work for each p, but the prefix depends on p.
The constants remain inside that parameter's quantifier. -/
theorem parameterwise_affine_bound (p : Nat) :
    ∃ A B : Int, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ n : Nat, (p : Int) ≤ A * (n : Int) + B := by
  refine exists_affine_bound_of_two_branch (fun _ => (p : Int))
    (fun _ => 0) (fun _ => 0) 0 0 0 0 0 (by decide) ?_ ?_
  · intro n _
    simp
  · intro n _
    have nonneg : (0 : Int) ≤ (p : Int) := Nat.cast_nonneg p
    simp only [zero_mul, add_zero]
    omega

/-- For f(p,n)=p, n=0 rules out constants uniform over every natural p. -/
theorem no_uniform_natural_family_bound :
    ¬ ∃ A B : Nat, ∀ p n : Nat, p ≤ A * n + B := by
  rintro ⟨A, B, bound⟩
  have exceeded := bound (B + 1) 0
  omega

/-- The same obstruction applies to arbitrary integer coefficients, so the
preceding parameterwise application cannot exchange its quantifiers. -/
theorem no_uniform_integer_family_bound :
    ¬ ∃ A B : Int, ∀ p n : Nat, (p : Int) ≤ A * (n : Int) + B := by
  rintro ⟨A, B, bound⟩
  obtain ⟨p, hp⟩ := exists_nat_gt B
  have at_zero := bound p 0
  simp only [Nat.cast_zero, mul_zero, zero_add] at at_zero
  exact (not_le_of_gt hp) at_zero

end Examples.AffineRecurrence
