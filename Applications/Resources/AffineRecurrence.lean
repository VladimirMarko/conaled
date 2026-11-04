import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.Linarith

/-! An all-input affine upper bound for a contracting two-child recurrence.

The scalar function is already total. An enlarged finite prefix permits strong
induction; it does not establish termination of an independently proposed
recursive definition. Values and toll coefficients may be signed. This is a
one-sided order bound, with no norm or asymptotic conclusion for signed values.

The argument abstracts the affine recurrence proof in FDSA Theorem 3.9 and
Manuel Eberl's `Selection.thy`, using division-free Archimedean witnesses.
Provenance, statement review and remaining source scope:
`docs/research/fdsa-affine-recurrence.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.AffineRecurrence
universe u
variable {R : Type u} [CommRing R] [LinearOrder R]
  [IsStrictOrderedRing R] [Archimedean R]

/-- Fixed recurrence data give one pair of nonnegative constants covering every
natural input, including the entire finite base prefix. Neither `f` nor the child
maps need be monotone; the function values and toll coefficients may be signed.
-/
theorem exists_affine_bound_of_two_branch
    (f : Nat → R) (left right : Nat → Nat) (n0 : Nat)
    (rho K C D : R) (contract : rho < 1)
    (sizes : ∀ n, n0 < n →
      (left n : R) + (right n : R) ≤ rho * (n : R) + K)
    (step : ∀ n, n0 < n →
      f n ≤ f (left n) + f (right n) + C * (n : R) + D) :
    ∃ A B : R, 0 ≤ A ∧ 0 ≤ B ∧ ∀ n : Nat, f n ≤ A * (n : R) + B := by
  have margin : 0 < 1 - rho := sub_pos.mpr contract
  obtain ⟨M, hM⟩ := Archimedean.arch (2 * K) margin
  let N := max n0 (max 1 M)
  have original_cutoff : n0 ≤ N := le_max_left _ _
  have one_cutoff : 1 ≤ N := (le_max_left 1 M).trans (le_max_right n0 (max 1 M))
  have multiple_cutoff : M ≤ N := (le_max_right 1 M).trans (le_max_right n0 (max 1 M))
  have cutoff_margin : 2 * K ≤ (1 - rho) * (N : R) := by
    calc
      2 * K ≤ (M : R) * (1 - rho) := by simpa only [nsmul_eq_mul] using hM
      _ ≤ (N : R) * (1 - rho) :=
        mul_le_mul_of_nonneg_right ((Nat.cast_le (α := R)).mpr multiple_cutoff) margin.le
      _ = (1 - rho) * (N : R) := mul_comm _ _
  have prefix_nonempty : (Finset.range (N + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  let B : R := max 0 ((Finset.range (N + 1)).sup' prefix_nonempty f)
  have intercept_nonneg : 0 ≤ B := le_max_left _ _
  have prefix_bound : ∀ n, n ≤ N → f n ≤ B := by
    intro n hn
    exact (Finset.le_sup' f (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))).trans
      (le_max_right _ _)
  obtain ⟨a, ha⟩ := Archimedean.arch (2 * (max 0 C + max 0 D + B)) margin
  let A : R := a
  have slope_nonneg : 0 ≤ A := Nat.cast_nonneg a
  have slope_margin : 2 * (max 0 C + max 0 D + B) ≤ A * (1 - rho) := by
    simpa only [nsmul_eq_mul] using ha
  refine ⟨A, B, slope_nonneg, intercept_nonneg, ?_⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases small : n ≤ N
      · exact (prefix_bound n small).trans
          (le_add_of_nonneg_left (mul_nonneg slope_nonneg (Nat.cast_nonneg n)))
      · have above : N < n := Nat.lt_of_not_ge small
        have active : n0 < n := lt_of_le_of_lt original_cutoff above
        have one_le_n : (1 : R) ≤ (n : R) :=
          Nat.one_le_cast.mpr (one_cutoff.trans above.le)
        have n_nonneg : (0 : R) ≤ (n : R) := Nat.cast_nonneg n
        have n_pos : (0 : R) < (n : R) := lt_of_lt_of_le zero_lt_one one_le_n
        have cutoff_at_n : 2 * K ≤ (1 - rho) * (n : R) :=
          cutoff_margin.trans (mul_le_mul_of_nonneg_left
            ((Nat.cast_le (α := R)).mpr above.le) margin.le)
        have size_bound := sizes n active
        have doubled_sizes :
            2 * ((left n : R) + (right n : R)) ≤ (1 + rho) * (n : R) := by
          nlinarith only [size_bound, cutoff_at_n]
        have strict_sizes : (1 + rho) * (n : R) < 2 * (n : R) := by
          nlinarith only [mul_pos margin n_pos]
        have left_nonneg : (0 : R) ≤ (left n : R) := Nat.cast_nonneg (left n)
        have right_nonneg : (0 : R) ≤ (right n : R) := Nat.cast_nonneg (right n)
        have left_smaller : left n < n := (Nat.cast_lt (α := R)).mp (by
          nlinarith only [doubled_sizes, strict_sizes, right_nonneg])
        have right_smaller : right n < n := (Nat.cast_lt (α := R)).mp (by
          nlinarith only [doubled_sizes, strict_sizes, left_nonneg])
        have left_bound := ih (left n) left_smaller
        have right_bound := ih (right n) right_smaller
        have scaled_sizes := mul_le_mul_of_nonneg_left doubled_sizes slope_nonneg
        have linear_toll : C * (n : R) ≤ max 0 C * (n : R) :=
          mul_le_mul_of_nonneg_right (le_max_right 0 C) n_nonneg
        have constant_toll : max 0 D ≤ max 0 D * (n : R) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left one_le_n (le_max_left 0 D)
        have intercept_at_n : B ≤ B * (n : R) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left one_le_n intercept_nonneg
        have toll_bound : C * (n : R) + D + B ≤
            (max 0 C + max 0 D + B) * (n : R) := by
          nlinarith only [linear_toll, le_max_right 0 D, constant_toll, intercept_at_n]
        have slope_at_n := mul_le_mul_of_nonneg_right slope_margin n_nonneg
        have absorption : 2 * (C * (n : R) + D + B) ≤
            A * (1 - rho) * (n : R) := by
          nlinarith only [toll_bound, slope_at_n]
        have recurrence := step n active
        nlinarith only [recurrence, left_bound, right_bound, scaled_sizes, absorption]

end Resources.AffineRecurrence
