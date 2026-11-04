import Applications.Resources.RoundedRecurrence
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Range

/-! All-input bounds for the exact rounded scalar recurrence in FDSA §3.5.

The cutoff, finite-prefix maximum and slope are the source's explicit choices.
The intercept remains signed; only the linear toll coefficient is assumed
nonnegative. The natural-valued corollary casts the actual recurrence and rounds
the real bounding constants upward, without a second induction.

The scalar function is already total. These theorems do not supply termination
or a resource interpretation for an independently proposed recursive algorithm.
For signed values the conclusion is a one-sided bound, not a norm estimate.

Mathematical source: FDSA, July 27, 2026, printed pp. 41–44; Manuel Eberl's
Selection.thy at Isabelle f86f290225eebcc52c1ae7dba2e098f405f51c21.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RoundedRecurrence

/-- The exact source cutoff dominates the original cutoff and strictly exceeds
the combined quotient. This ceiling fact itself needs no sign assumptions. -/
theorem explicit_cutoff_bounds (a b c d : ℝ) (n0 : Nat) :
    let N : Nat := max n0 (⌈(max 0 b + max 0 d + 2) / (1 - a - c)⌉₊ + 1)
    n0 ≤ N ∧ (max 0 b + max 0 d + 2) / (1 - a - c) < (N : ℝ) := by
  dsimp only
  constructor
  · exact le_max_left _ _
  · calc
      (max 0 b + max 0 d + 2) / (1 - a - c) ≤
          (⌈(max 0 b + max 0 d + 2) / (1 - a - c)⌉₊ : ℝ) := Nat.le_ceil _
      _ < ((⌈(max 0 b + max 0 d + 2) / (1 - a - c)⌉₊ + 1 : Nat) : ℝ) :=
        (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_succ_self _)
      _ ≤ ((max n0 (⌈(max 0 b + max 0 d + 2) / (1 - a - c)⌉₊ + 1) : Nat) : ℝ) :=
        (Nat.cast_le (α := ℝ)).mpr (le_max_right _ _)

/-- Sharp strong induction with the two source slope constraints. All inputs,
including zero and the entire prefix, are covered by the same C3 and C4.
Neither the scalar values nor the intercept need be nonnegative. -/
theorem affine_bound_of_prefix (f : Nat → ℝ)
    (a b c d C1 C2 C3 C4 : ℝ) (n0 N : Nat)
    (ha : 0 < a) (hc : 0 < c) (contract : a + c < 1) (toll_nonneg : 0 ≤ C1)
    (cutoff : n0 ≤ N)
    (threshold : (max 0 b + max 0 d + 2) / (1 - a - c) < (N : ℝ))
    (hprefix : ∀ n, n ≤ N → f n ≤ C4)
    (slope : C1 / (1 - a - c) ≤ C3)
    (absorb : (C1 * (N : ℝ) + C2 + C4) /
      ((1 - a - c) * (N : ℝ) - max 0 b - max 0 d - 2) ≤ C3)
    (recurrence : ∀ n, n0 < n →
      f n = f ⌈a * (n : ℝ) + b⌉₊ + f ⌈c * (n : ℝ) + d⌉₊ +
        C1 * (n : ℝ) + C2) :
    ∀ n : Nat, f n ≤ C3 * (n : ℝ) + C4 := by
  have nonneg := (slope_nonneg_and_margin a c C1 C3 contract toll_nonneg slope).1
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases small : n ≤ N
      · exact (hprefix n small).trans
          (le_add_of_nonneg_left (mul_nonneg nonneg (Nat.cast_nonneg n)))
      · have above : N < n := Nat.lt_of_not_ge small
        have children := ceil_children_lt a b c d N n ha hc contract threshold above
        exact recurrence_step_le f a b c d C1 C2 C3 C4 N n ha.le hc.le contract
          toll_nonneg threshold slope absorb above.le
          (recurrence n (lt_of_le_of_lt cutoff above))
          (ih _ children.1) (ih _ children.2)

/-- The source construction exposed before existentially hiding its constants.
C4 is the actual maximum of the nonempty finite prefix, with no truncation to
zero. The maximum defining C3 retains both exact source quotients. -/
theorem bound_with_source_constants (f : Nat → ℝ)
    (a b c d C1 C2 : ℝ) (n0 : Nat)
    (ha : 0 < a) (hc : 0 < c) (contract : a + c < 1) (toll_nonneg : 0 ≤ C1)
    (recurrence : ∀ n, n0 < n →
      f n = f ⌈a * (n : ℝ) + b⌉₊ + f ⌈c * (n : ℝ) + d⌉₊ +
        C1 * (n : ℝ) + C2) :
    let N : Nat := max n0 (⌈(max 0 b + max 0 d + 2) / (1 - a - c)⌉₊ + 1)
    let C4 : ℝ := (Finset.range (N + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ f
    let C3 : ℝ := max (C1 / (1 - a - c))
      ((C1 * (N : ℝ) + C2 + C4) /
        ((1 - a - c) * (N : ℝ) - max 0 b - max 0 d - 2))
    ∀ n : Nat, f n ≤ C3 * (n : ℝ) + C4 := by
  let N : Nat := max n0 (⌈(max 0 b + max 0 d + 2) / (1 - a - c)⌉₊ + 1)
  let C4 : ℝ := (Finset.range (N + 1)).sup'
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ f
  let C3 : ℝ := max (C1 / (1 - a - c))
    ((C1 * (N : ℝ) + C2 + C4) /
      ((1 - a - c) * (N : ℝ) - max 0 b - max 0 d - 2))
  change ∀ n : Nat, f n ≤ C3 * (n : ℝ) + C4
  have cutoff : n0 ≤ N ∧ (max 0 b + max 0 d + 2) / (1 - a - c) < (N : ℝ) :=
    explicit_cutoff_bounds a b c d n0
  refine affine_bound_of_prefix f a b c d C1 C2 C3 C4 n0 N ha hc contract
    toll_nonneg cutoff.1 cutoff.2 ?_ (le_max_left _ _) (le_max_right _ _) recurrence
  intro n hn
  exact Finset.le_sup' f (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-- FDSA Theorem 3.9: fixed recurrence data admit fixed real affine constants
for every natural input. Offsets, constant toll and scalar values may be signed. -/
theorem exists_affine_bound (f : Nat → ℝ) (a b c d C1 C2 : ℝ) (n0 : Nat)
    (ha : 0 < a) (hc : 0 < c) (contract : a + c < 1) (toll_nonneg : 0 ≤ C1)
    (recurrence : ∀ n, n0 < n →
      f n = f ⌈a * (n : ℝ) + b⌉₊ + f ⌈c * (n : ℝ) + d⌉₊ +
        C1 * (n : ℝ) + C2) :
    ∃ C3 C4 : ℝ, ∀ n : Nat, f n ≤ C3 * (n : ℝ) + C4 := by
  have bound := bound_with_source_constants f a b c d C1 C2 n0 ha hc contract
    toll_nonneg recurrence
  dsimp only at bound
  exact ⟨_, _, bound⟩

/-- The natural-valued corollary uses natural ceilings of the real witnesses.
It preserves the exact rounded children and all natural inputs, including zero. -/
theorem exists_affine_bound_nat (f : Nat → Nat) (a b c d : ℝ) (C1 C2 n0 : Nat)
    (ha : 0 < a) (hc : 0 < c) (contract : a + c < 1)
    (recurrence : ∀ n, n0 < n →
      f n = f ⌈a * (n : ℝ) + b⌉₊ + f ⌈c * (n : ℝ) + d⌉₊ + C1 * n + C2) :
    ∃ C3 C4 : Nat, ∀ n : Nat, f n ≤ C3 * n + C4 := by
  have real_recurrence : ∀ n, n0 < n →
      (f n : ℝ) = (f ⌈a * (n : ℝ) + b⌉₊ : ℝ) + (f ⌈c * (n : ℝ) + d⌉₊ : ℝ) +
        (C1 : ℝ) * (n : ℝ) + (C2 : ℝ) := by
    intro n hn
    have equation := congrArg (fun value : Nat => (value : ℝ)) (recurrence n hn)
    simpa only [Nat.cast_add, Nat.cast_mul] using equation
  obtain ⟨A, B, bound⟩ := exists_affine_bound (fun n => (f n : ℝ))
    a b c d (C1 : ℝ) (C2 : ℝ) n0 ha hc contract (Nat.cast_nonneg C1) real_recurrence
  refine ⟨⌈A⌉₊, ⌈B⌉₊, ?_⟩
  intro n
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_add, Nat.cast_mul]
  exact (bound n).trans (add_le_add
    (mul_le_mul_of_nonneg_right (Nat.le_ceil A) (Nat.cast_nonneg n)) (Nat.le_ceil B))

end Resources.RoundedRecurrence
