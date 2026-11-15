import Applications.Resources.RoundedRecurrenceBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Connected all-input clients of the source's rounded recurrence bound.

The rounded-quarter scalar below has values 1, 6, 13 and 48 at 0, 5, 6 and 21.
Its well-founded construction uses exact child descent before any affine bound
is applied. It is a scalar recurrence, not a selector or a measured algorithm.
The real and natural clients consume that same actual recurrence.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RoundedRecurrenceBounds
open Resources.RoundedRecurrence

/-- The exact maximum-based source choices give zero slope and zero intercept
for the zero recurrence. Equality in the slope condition covers every input. -/
theorem zero_source_witness_bound :
    ∀ n : Nat, (0 : ℝ) ≤ 0 * (n : ℝ) + 0 := by
  have bound := bound_with_source_constants (fun _ : Nat => (0 : ℝ))
    (1 / 4) 0 (1 / 4) 0 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro n _; simp)
  simpa only [Finset.sup'_const, zero_mul, zero_div, zero_add, add_zero, max_self]
    using bound

/-- The completed induction retains a genuinely negative prefix maximum and
intercept, rather than replacing them by zero. The offsets are also negative. -/
theorem negative_intercept_all_inputs :
    ∀ n : Nat, (-3 : ℝ) ≤ 0 * (n : ℝ) + (-3) := by
  exact affine_bound_of_prefix (fun _ : Nat => (-3 : ℝ))
    (1 / 4) (-7) (1 / 4) (-2) 0 3 0 (-3) 0 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by intro n _; exact le_rfl)
    (by norm_num) (by norm_num) (by intro n _; norm_num)

/-- Positive constant values with a negative constant toll satisfy the actual
recurrence, so signed C2 is supported by the complete existence theorem. -/
theorem negative_constant_toll_affine_bound :
    ∃ A B : ℝ, ∀ n : Nat, (3 : ℝ) ≤ A * (n : ℝ) + B := by
  exact exists_affine_bound (fun _ : Nat => (3 : ℝ))
    (1 / 4) (-7) (1 / 4) (-2) 0 (-3) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro n _; norm_num)

/-- An actual natural scalar recurrence with rounded children and a nonconstant
base prefix. Real ceiling makes the specification noncomputable. -/
noncomputable def roundedQuarter (n : Nat) : Nat :=
  if h : n ≤ 5 then n + 1 else
    roundedQuarter ⌈(1 / 4 : ℝ) * (n : ℝ)⌉₊ +
      roundedQuarter ⌈(1 / 4 : ℝ) * (n : ℝ)⌉₊ + n + 1
termination_by n
decreasing_by
  all_goals
    simpa only [add_zero] using
      ceil_affine_lt_of_threshold (1 / 4) 0 5 n
        (by norm_num) (by norm_num) (by norm_num) (Nat.lt_of_not_ge h)

theorem roundedQuarter_of_le_five (n : Nat) (small : n ≤ 5) :
    roundedQuarter n = n + 1 := by
  rw [roundedQuarter]
  split
  · rfl
  · rename_i not_small
    exact (not_small small).elim

theorem roundedQuarter_of_five_lt (n : Nat) (large : 5 < n) :
    roundedQuarter n = roundedQuarter ⌈(1 / 4 : ℝ) * (n : ℝ)⌉₊ +
      roundedQuarter ⌈(1 / 4 : ℝ) * (n : ℝ)⌉₊ + n + 1 := by
  rw [roundedQuarter]
  split
  · rename_i small
    exact ((not_le_of_gt large) small).elim
  · rfl

theorem roundedQuarter_zero : roundedQuarter 0 = 1 :=
  roundedQuarter_of_le_five 0 (by decide)

theorem roundedQuarter_five : roundedQuarter 5 = 6 :=
  roundedQuarter_of_le_five 5 (by decide)

/-- The first recursive input uses ceiling 6/4=2, not floor 6/4=1. -/
theorem roundedQuarter_six : roundedQuarter 6 = 13 := by
  have child : ⌈(1 / 4 : ℝ) * ((6 : Nat) : ℝ)⌉₊ = 2 := by
    apply (Nat.ceil_eq_iff (by decide : (2 : Nat) ≠ 0)).mpr
    norm_num
  rw [roundedQuarter_of_five_lt 6 (by decide), child,
    roundedQuarter_of_le_five 2 (by decide)]

/-- This value follows a genuinely recursive child: ceil(21/4)=6 and Q(6)=13. -/
theorem roundedQuarter_twenty_one : roundedQuarter 21 = 48 := by
  have child : ⌈(1 / 4 : ℝ) * ((21 : Nat) : ℝ)⌉₊ = 6 := by
    apply (Nat.ceil_eq_iff (by decide : (6 : Nat) ≠ 0)).mpr
    norm_num
  rw [roundedQuarter_of_five_lt 21 (by decide), child, roundedQuarter_six]

/-- Apply the exact source constants: N=5, prefix maximum 6, slope 24. -/
theorem roundedQuarter_sharp_affine_bound :
    ∀ n : Nat, (roundedQuarter n : ℝ) ≤ 24 * (n : ℝ) + 6 := by
  refine affine_bound_of_prefix (fun n => (roundedQuarter n : ℝ))
    (1 / 4) 0 (1 / 4) 0 1 1 24 6 5 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num) ?_
  · intro n hn
    rw [roundedQuarter_of_le_five n hn]
    have bound : (n : ℝ) ≤ 5 := (Nat.cast_le (α := ℝ)).mpr hn
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [bound]
  · intro n hn
    have equation := congrArg (fun value : Nat => (value : ℝ))
      (roundedQuarter_of_five_lt n hn)
    simpa only [Nat.cast_add, Nat.cast_one, add_zero, one_mul] using equation

/-- Real existence consumes the same exact rounded recurrence. -/
theorem roundedQuarter_real_affine_bound :
    ∃ A B : ℝ, ∀ n : Nat, (roundedQuarter n : ℝ) ≤ A * (n : ℝ) + B := by
  refine exists_affine_bound (fun n => (roundedQuarter n : ℝ))
    (1 / 4) 0 (1 / 4) 0 1 1 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  intro n hn
  have equation := congrArg (fun value : Nat => (value : ℝ))
    (roundedQuarter_of_five_lt n hn)
  simpa only [Nat.cast_add, Nat.cast_one, add_zero, one_mul] using equation

/-- The natural corollary applies to Q without proving a second growth induction. -/
theorem roundedQuarter_nat_affine_bound :
    ∃ A B : Nat, ∀ n : Nat, roundedQuarter n ≤ A * n + B := by
  refine exists_affine_bound_nat roundedQuarter (1 / 4) 0 (1 / 4) 0 1 1 5
    (by norm_num) (by norm_num) (by norm_num) ?_
  intro n hn
  simpa only [add_zero, one_mul] using roundedQuarter_of_five_lt n hn

/-- At a+c=1 with positive linear toll, no fixed affine induction estimate
closes beyond any finite cutoff. Even inputs have exact half-size children.
This is a failure of the affine step, not a converse about every scalar law. -/
theorem noncontracting_affine_step_impossible (A B : ℝ) (N : Nat) :
    ¬ ∀ n : Nat, N < n →
      (A * (⌈(1 / 2 : ℝ) * (n : ℝ)⌉₊ : ℝ) + B) +
        (A * (⌈(1 / 2 : ℝ) * (n : ℝ)⌉₊ : ℝ) + B) + (n : ℝ) ≤
          A * (n : ℝ) + B := by
  intro step
  obtain ⟨m, hm⟩ := exists_nat_gt (max (N : ℝ) (-B))
  have above_cutoff : (N : ℝ) < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have above_intercept : -B < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have large : N < 2 * m := by
    apply (Nat.cast_lt (α := ℝ)).mp
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    linarith only [above_cutoff, nonneg]
  have exact_half : (1 / 2 : ℝ) * ((2 * m : Nat) : ℝ) = (m : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  have child : ⌈(1 / 2 : ℝ) * ((2 * m : Nat) : ℝ)⌉₊ = m := by
    rw [exact_half, Nat.ceil_natCast]
  have estimate := step (2 * m) large
  rw [child] at estimate
  simp only [Nat.cast_mul, Nat.cast_ofNat] at estimate
  nlinarith only [estimate, above_intercept, nonneg]

end Examples.RoundedRecurrenceBounds
