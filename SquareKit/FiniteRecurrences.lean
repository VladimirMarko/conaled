import SquareKit.FiniteSums
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Finite affine recurrences on positive indices

The native left fold over `List.range' 1 n` executes the transitions at indices
`1` through `n` in order. Its initial value is independent of the natural weight
and toll functions, and weights may be zero. The finite identities below make
no execution-cost or asymptotic claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.FiniteRecurrences

open scoped BigOperators

/-- An empty positive-index fold returns its independent initial value. -/
theorem affine_fold_zero (weight toll : Nat → Nat) (base : Nat) :
    (List.range' 1 0).foldl (fun x k => weight k * x + toll k) base = base := by
  rfl

/-- The next chronological transition uses index `n + 1`, never index zero. -/
theorem affine_fold_succ (weight toll : Nat → Nat) (base n : Nat) :
    (List.range' 1 (n + 1)).foldl (fun x k => weight k * x + toll k) base =
      weight (n + 1) *
        (List.range' 1 n).foldl (fun x k => weight k * x + toll k) base +
      toll (n + 1) := by
  rw [List.range'_1_concat, List.foldl_concat]
  simp only [Nat.add_comm 1 n]

/-- A sequence satisfying the lower base and step inequalities lies below the fold. -/
theorem le_affine_fold (weight toll T : Nat → Nat) (base : Nat)
    (hzero : T 0 ≤ base)
    (hstep : ∀ n, T (n + 1) ≤ weight (n + 1) * T n + toll (n + 1))
    (n : Nat) :
    T n ≤ (List.range' 1 n).foldl (fun x k => weight k * x + toll k) base := by
  induction n with
  | zero => simpa only [affine_fold_zero] using hzero
  | succ n ih =>
      rw [affine_fold_succ]
      exact (hstep n).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left (weight (n + 1)) ih) _)

/-- A sequence satisfying the upper base and step inequalities bounds the fold. -/
theorem affine_fold_le (weight toll T : Nat → Nat) (base : Nat)
    (hzero : base ≤ T 0)
    (hstep : ∀ n, weight (n + 1) * T n + toll (n + 1) ≤ T (n + 1))
    (n : Nat) :
    (List.range' 1 n).foldl (fun x k => weight k * x + toll k) base ≤ T n := by
  induction n with
  | zero => simpa only [affine_fold_zero] using hzero
  | succ n ih =>
      rw [affine_fold_succ]
      exact (Nat.add_le_add_right (Nat.mul_le_mul_left (weight (n + 1)) ih) _).trans
        (hstep n)

/-- Arbitrary positive-index tolls accumulate without using the toll at zero. -/
theorem additive_toll_exact (toll : Nat → Nat) (b n : Nat) :
    (List.range' 1 n).foldl (fun x k => x + toll k) b =
      b + ∑ k ∈ Finset.Ico 1 (n + 1), toll k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := affine_fold_succ (fun _ => 1) toll b n
      simp only [one_mul] at hstep
      rw [hstep, ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
      ring

/-- An eventual pointwise lower bound leaves only the finite triangular reserve.
The conclusion includes every prefix, and the coefficient may be zero. -/
theorem triangle_le_scaled_toll_sum (toll : Nat → Nat) (D N : Nat)
    (hlower : ∀ k : Nat, N ≤ k → k ≤ D * toll k) :
    ∀ n : Nat,
      (∑ k ∈ Finset.Ico 1 (n + 1), k) ≤
        D * (∑ k ∈ Finset.Ico 1 (n + 1), toll k) +
          ∑ k ∈ Finset.Ico 1 (N + 1), k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hsmall : n + 1 ≤ N
      · have hprefix : (∑ k ∈ Finset.Ico 1 (n + 1 + 1), k) ≤
            ∑ k ∈ Finset.Ico 1 (N + 1), k := by
          apply Finset.sum_le_sum_of_subset
          intro k hk
          rcases Finset.mem_Ico.mp hk with ⟨hk, hkn⟩
          exact Finset.mem_Ico.mpr ⟨hk, by omega⟩
        exact hprefix.trans (Nat.le_add_left _ _)
      · have htail := hlower (n + 1) (by omega)
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1),
          Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
        calc
          (∑ k ∈ Finset.Ico 1 (n + 1), k) + (n + 1) ≤
              (D * (∑ k ∈ Finset.Ico 1 (n + 1), toll k) +
                ∑ k ∈ Finset.Ico 1 (N + 1), k) + D * toll (n + 1) :=
            Nat.add_le_add ih htail
          _ = D * ((∑ k ∈ Finset.Ico 1 (n + 1), toll k) + toll (n + 1)) +
                ∑ k ∈ Finset.Ico 1 (N + 1), k := by ring

/-- Linear tolls accumulate to the existing positive triangular sum. -/
theorem additive_exact (b c n : Nat) :
    (List.range' 1 n).foldl (fun x k => x + c * k) b =
      b + c * ∑ k ∈ Finset.Ico 1 (n + 1), k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := affine_fold_succ (fun _ => 1) (fun k => c * k) b n
      simp only [one_mul] at hstep
      rw [hstep, ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
      ring

/-- Positive tolls give the recorded quadratic bounds from index one onward. -/
theorem additive_bounds (b c n : Nat) (hc : 0 < c) (hn : 1 ≤ n) :
    n * n ≤ 2 * (List.range' 1 n).foldl (fun x k => x + c * k) b ∧
      (List.range' 1 n).foldl (fun x k => x + c * k) b ≤ (b + c) * (n * n) := by
  simp only [additive_exact]
  have htriangle := FiniteSums.triangle_bounds n
  have hc_one : 1 ≤ c := hc
  have hn_square : 1 ≤ n * n := Nat.mul_le_mul hn hn
  constructor
  · have hscale : (∑ k ∈ Finset.Ico 1 (n + 1), k) ≤
        c * ∑ k ∈ Finset.Ico 1 (n + 1), k := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right (∑ k ∈ Finset.Ico 1 (n + 1), k) hc_one
    calc
      n * n ≤ 2 * (∑ k ∈ Finset.Ico 1 (n + 1), k) := htriangle.1
      _ ≤ 2 * (c * ∑ k ∈ Finset.Ico 1 (n + 1), k) :=
        Nat.mul_le_mul_left 2 hscale
      _ ≤ 2 * (b + c * ∑ k ∈ Finset.Ico 1 (n + 1), k) :=
        Nat.mul_le_mul_left 2 (Nat.le_add_left _ _)
  · have hbase : b ≤ b * (n * n) := by
      simpa only [mul_one] using Nat.mul_le_mul_left b hn_square
    calc
      b + c * (∑ k ∈ Finset.Ico 1 (n + 1), k) ≤
          b * (n * n) + c * (n * n) :=
        Nat.add_le_add hbase (Nat.mul_le_mul_left c htriangle.2)
      _ = (b + c) * (n * n) := by ring

/-- Every initial value contributes its full exponential factor, even with zero toll. -/
theorem doubling_base_lower (toll : Nat → Nat) (b n : Nat) :
    b * 2 ^ n ≤
      (List.range' 1 n).foldl (fun x k => 2 * x + toll k) b := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [affine_fold_succ (fun _ => 2) toll b n, pow_succ]
      calc
        b * (2 ^ n * 2) = 2 * (b * 2 ^ n) := by ring
        _ ≤ 2 * (List.range' 1 n).foldl (fun x k => 2 * x + toll k) b :=
          Nat.mul_le_mul_left 2 ih
        _ ≤ 2 * (List.range' 1 n).foldl (fun x k => 2 * x + toll k) b +
            toll (n + 1) := Nat.le_add_right _ _

/-- The doubling identity retains its reserve term, so no natural subtraction is needed. -/
theorem doubling_exact (b c n : Nat) :
    (List.range' 1 n).foldl (fun x k => 2 * x + c * k) b + c * (n + 2) =
      2 ^ n * (b + 2 * c) := by
  induction n with
  | zero => simp [Nat.mul_comm]
  | succ n ih =>
      rw [affine_fold_succ (fun _ => 2) (fun k => c * k) b n, pow_succ]
      nlinarith [ih]

/-- The exact reserve identity gives an upper bound even at zero and with zero toll. -/
theorem doubling_upper (b c n : Nat) :
    (List.range' 1 n).foldl (fun x k => 2 * x + c * k) b ≤
      (b + 2 * c) * 2 ^ n := by
  calc
    (List.range' 1 n).foldl (fun x k => 2 * x + c * k) b ≤
        (List.range' 1 n).foldl (fun x k => 2 * x + c * k) b + c * (n + 2) :=
      Nat.le_add_right _ _
    _ = 2 ^ n * (b + 2 * c) := doubling_exact b c n
    _ = (b + 2 * c) * 2 ^ n := Nat.mul_comm _ _

/-- The lower exponential bound starts at one and does not require a positive toll. -/
theorem doubling_lower (b c n : Nat) (hn : 1 ≤ n) :
    c * 2 ^ n ≤ 2 * (List.range' 1 n).foldl (fun x k => 2 * x + c * k) b := by
  cases n with
  | zero => omega
  | succ n =>
      clear hn
      induction n with
      | zero => simp [List.range', List.foldl]; omega
      | succ n ih =>
          rw [affine_fold_succ (fun _ => 2) (fun k => c * k) b (n + 1), pow_succ]
          calc
            c * (2 ^ (n + 1) * 2) = 2 * (c * 2 ^ (n + 1)) := by ring
            _ ≤ 2 * (2 * (List.range' 1 (n + 1)).foldl
                (fun x k => 2 * x + c * k) b) :=
              Nat.mul_le_mul_left 2 ih
            _ ≤ 2 * (2 * (List.range' 1 (n + 1)).foldl
                (fun x k => 2 * x + c * k) b + c * (n + 1 + 1)) :=
              Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)

/-- Normalize using the existing half-sum identity, without cancelling the toll. -/
theorem doubling_normalized_sum (b c n : Nat) :
    (((List.range' 1 n).foldl (fun x k => 2 * x + c * k) b : Nat) : ℚ) =
      (2 : ℚ) ^ n * ((b : ℚ) + (c : ℚ) *
        ∑ k ∈ Finset.Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) := by
  have hd :
      (((List.range' 1 n).foldl (fun x k => 2 * x + c * k) b : Nat) : ℚ) +
        (c : ℚ) * ((n : ℚ) + 2) =
      (2 : ℚ) ^ n * ((b : ℚ) + 2 * (c : ℚ)) := by
    exact_mod_cast doubling_exact b c n
  have hH := FiniteSums.half_sum_scaled n
  rw [pow_succ] at hH
  linear_combination hd - (c : ℚ) * hH

end SquareKit.FiniteRecurrences

namespace SquareKit.FiniteRecurrences

open scoped BigOperators

/-- Every initial value contributes its factorial factor for all natural prefixes. -/
theorem factorial_base_lower (toll : Nat → Nat) (b n : Nat) :
    b * Nat.factorial n ≤
      (List.range' 1 n).foldl (fun x k => k * x + toll k) b := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [affine_fold_succ (fun k => k) toll b n, Nat.factorial_succ]
      calc
        b * ((n + 1) * Nat.factorial n) = (n + 1) * (b * Nat.factorial n) := by ring
        _ ≤ (n + 1) * (List.range' 1 n).foldl (fun x k => k * x + toll k) b :=
          Nat.mul_le_mul_left (n + 1) ih
        _ ≤ (n + 1) * (List.range' 1 n).foldl (fun x k => k * x + toll k) b +
            toll (n + 1) := Nat.le_add_right _ _

/-- The factorial-weighted fold retains a reserve of twice its toll coefficient. -/
theorem factorial_reserve (b c n : Nat) (hn : 1 ≤ n) :
    (List.range' 1 n).foldl (fun x k => k * x + c * k) b + 2 * c ≤
      (b + 3 * c) * Nat.factorial n := by
  cases n with
  | zero => omega
  | succ n =>
    clear hn
    induction n with
    | zero =>
      rw [affine_fold_succ (fun k => k) (fun k => c * k) b 0]
      simp only [affine_fold_zero, Nat.zero_add, Nat.one_mul, Nat.mul_one,
        Nat.factorial_one]; omega
    | succ n ih =>
      rw [affine_fold_succ (fun k => k) (fun k => c * k) b (n + 1),
        Nat.factorial_succ (n + 1)]
      have hm := Nat.mul_le_mul_left (n + 2) ih
      have hc := Nat.mul_le_mul_right c (show 2 ≤ n + 2 by omega)
      nlinarith only [hm, hc]

/-- From index one, the toll coefficient times the factorial is a lower bound. -/
theorem factorial_lower (b c n : Nat) (hn : 1 ≤ n) :
    c * Nat.factorial n ≤
      (List.range' 1 n).foldl (fun x k => k * x + c * k) b := by
  cases n with
  | zero => omega
  | succ n =>
    clear hn
    induction n with
    | zero =>
      rw [affine_fold_succ (fun k => k) (fun k => c * k) b 0]
      simp only [affine_fold_zero, Nat.zero_add, Nat.one_mul, Nat.mul_one,
        Nat.factorial_one]; omega
    | succ n ih =>
      rw [affine_fold_succ (fun k => k) (fun k => c * k) b (n + 1),
        Nat.factorial_succ (n + 1)]
      have hm := Nat.mul_le_mul_left (n + 2) ih
      nlinarith only [hm, Nat.zero_le (c * (n + 2))]

/-- Exact normalization keeps the independent base and the zero-indexed sum. -/
theorem factorial_normalized_sum (b c n : Nat) :
    (((List.range' 1 n).foldl (fun x k => k * x + c * k) b : Nat) : ℚ) =
      (Nat.factorial n : ℚ) *
        ((b : ℚ) + (c : ℚ) * ∑ k ∈ Finset.range n, 1 / (Nat.factorial k : ℚ)) := by
  induction n with
  | zero =>
    simp only [affine_fold_zero, Nat.factorial_zero, Nat.cast_one,
      Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, one_mul]
  | succ n ih =>
    have hp : (0 : ℚ) < (Nat.factorial n : ℚ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hc : (Nat.factorial n : ℚ) * (1 / (Nat.factorial n : ℚ)) = 1 :=
      mul_one_div_cancel (ne_of_gt hp)
    simp only [affine_fold_succ (fun k => k) (fun k => c * k) b n,
      Nat.factorial_succ n, Finset.sum_range_succ, Nat.cast_add,
      Nat.cast_mul, Nat.cast_one, ih]
    linear_combination -((n : ℚ) + 1) * (c : ℚ) * hc

/-- Every finite reciprocal-factorial partial sum is nonnegative, including zero. -/
theorem reciprocal_factorial_sum_nonneg (n : Nat) :
    0 ≤ ∑ k ∈ Finset.range n, 1 / (Nat.factorial k : ℚ) := by
  apply Finset.sum_nonneg
  intro k _
  exact div_nonneg zero_le_one (Nat.cast_nonneg (Nat.factorial k))

/-- The finite reserve gives a strict bound without an infinite-series premise. -/
theorem reciprocal_factorial_sum_lt_three (n : Nat) :
    (∑ k ∈ Finset.range n, 1 / (Nat.factorial k : ℚ)) < 3 := by
  cases n with
  | zero => simp
  | succ n =>
    have hnat := factorial_reserve 0 1 (n + 1) (by omega)
    simp only [Nat.mul_one, Nat.zero_add] at hnat
    have hq :
        (((List.range' 1 (n + 1)).foldl (fun x k => k * x + 1 * k) 0 : Nat) : ℚ) + 2 ≤
          3 * (Nat.factorial (n + 1) : ℚ) := by
      exact_mod_cast hnat
    rw [factorial_normalized_sum 0 1 (n + 1)] at hq
    simp only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul] at hq
    have hp : (0 : ℚ) < (Nat.factorial (n + 1) : ℚ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos (n + 1))
    apply lt_of_mul_lt_mul_left (a := (Nat.factorial (n + 1) : ℚ)) ?_ (le_of_lt hp)
    nlinarith only [hq]

end SquareKit.FiniteRecurrences

namespace SquareKit.FiniteRecurrences

/-- A constant toll specializes the arbitrary positive-index additive fold. -/
theorem constant_toll_exact (b c m : Nat) :
    (List.range' 1 m).foldl (fun x _ => x + c) b = b + m * c := by
  rw [additive_toll_exact]
  simp

/-- Positive independent base and toll coefficients bound every pair, including zeros. -/
theorem constant_toll_bounds (b c m n : Nat) (hb : 0 < b) (hc : 0 < c) :
    m * n + n * n ≤ (List.range' 1 m).foldl (fun x _ => x + c * n) (b * n * n) ∧
      (List.range' 1 m).foldl (fun x _ => x + c * n) (b * n * n) ≤
        (b + c) * (m * n + n * n) := by
  rw [constant_toll_exact]
  have hb1 := Nat.mul_le_mul_right (n * n) (show 1 ≤ b by omega)
  have hc1 := Nat.mul_le_mul_right (m * n) (show 1 ≤ c by omega)
  constructor
  · nlinarith only [hb1, hc1]
  · calc
      b * n * n + m * (c * n) = b * (n * n) + c * (m * n) := by ring
      _ ≤ b * (m * n + n * n) + c * (m * n + n * n) :=
        Nat.add_le_add
          (Nat.mul_le_mul_left b (Nat.le_add_left _ _))
          (Nat.mul_le_mul_left c (Nat.le_add_right _ _))
      _ = (b + c) * (m * n + n * n) := by ring

/-- Separate base and step bounds sandwich an arbitrary two-parameter family.
No coefficient positivity is required for this comparison. -/
theorem constant_toll_comparison (T : Nat → Nat → Nat) (bl bu cl cu : Nat)
    (hb : ∀ n, bl * n * n ≤ T 0 n ∧ T 0 n ≤ bu * n * n)
    (hs : ∀ m n, T m n + cl * n ≤ T (m + 1) n ∧
      T (m + 1) n ≤ T m n + cu * n) (m n : Nat) :
    (List.range' 1 m).foldl (fun x _ => x + cl * n) (bl * n * n) ≤ T m n ∧
      T m n ≤ (List.range' 1 m).foldl (fun x _ => x + cu * n) (bu * n * n) := by
  constructor
  · simpa only [one_mul] using
      affine_fold_le (fun _ => 1) (fun _ => cl * n) (fun k => T k n)
        (bl * n * n) (hb n).1
        (fun k => by simpa only [one_mul] using (hs k n).1) m
  · simpa only [one_mul] using
      le_affine_fold (fun _ => 1) (fun _ => cu * n) (fun k => T k n)
        (bu * n * n) (hb n).2
        (fun k => by simpa only [one_mul] using (hs k n).2) m

/-- A positive reciprocal lower slope permits sublinear-in-n increments.
The finite bound needs only E positive and preserves every first-coordinate fiber. -/
theorem two_param_eventual_bounds (T : Nat → Nat → Nat) (B D C E N : Nat)
    (hE : 0 < E)
    (hb : ∀ n, N ≤ n → n * n ≤ D * T 0 n ∧ T 0 n ≤ B * (n * n))
    (hs : ∀ m n, N ≤ n → E * T m n + n ≤ E * T (m + 1) n ∧
      T (m + 1) n ≤ T m n + C * n) (m n : Nat) (hn : N ≤ n) :
    n * n + m * n ≤ (D + E) * T m n ∧
      T m n ≤ (B + C) * (n * n + m * n) := by
  have hl : E * T 0 n + m * n ≤ E * T m n := by
    have h := affine_fold_le (fun _ => 1) (fun _ => n) (fun k => E * T k n)
      (E * T 0 n) (Nat.le_refl _)
      (fun k => by simpa only [one_mul] using (hs k n hn).1) m
    simpa only [one_mul, constant_toll_exact] using h
  have hu : T m n ≤ B * (n * n) + m * (C * n) := by
    have h := le_affine_fold (fun _ => 1) (fun _ => C * n) (fun k => T k n)
      (B * (n * n)) (hb n hn).2
      (fun k => by simpa only [one_mul] using (hs k n hn).2) m
    simpa only [one_mul, constant_toll_exact] using h
  have hmono : T 0 n ≤ T m n :=
    Nat.le_of_mul_le_mul_left ((Nat.le_add_right _ _).trans hl) hE
  have hbase : n * n ≤ D * T m n :=
    (hb n hn).1.trans (Nat.mul_le_mul_left D hmono)
  have htoll : m * n ≤ E * T m n := (Nat.le_add_left _ _).trans hl
  constructor
  · calc
      n * n + m * n ≤ D * T m n + E * T m n := Nat.add_le_add hbase htoll
      _ = (D + E) * T m n := by ring
  · calc
      T m n ≤ B * (n * n) + m * (C * n) := hu
      _ = B * (n * n) + C * (m * n) := by ring
      _ ≤ B * (n * n + m * n) + C * (n * n + m * n) :=
        Nat.add_le_add
          (Nat.mul_le_mul_left B (Nat.le_add_right _ _))
          (Nat.mul_le_mul_left C (Nat.le_add_left _ _))
      _ = (B + C) * (n * n + m * n) := by ring

end SquareKit.FiniteRecurrences
