import Applications.Resources.SelectionPolicy
import Applications.Resources.FixedRank

/-!
FDSA p35: corrected deterministic minimum-pivot analysis.

All executions use the actual measured linear minimum constructor. The exact
path theorem assumes distinct occurrences and a valid zero-based rank. It
separates active invocations, recursive edges, scan volume and source calls.
The largest-rank specialization is uniformly quadratic. With a fixed rank
the cost is linear; duplicates can stop at an entire equal block immediately.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.MinimumPivot
open Applications.Selection
universe u
variable {α : Type u} [LinearOrder α]

/-- The minimum constructor is charged on every active invocation. -/
def run (fuel k : Nat) (xs : List α) : SelectionPolicy.Observed α :=
  SelectionPolicy.runWith FixedRank.select0Run fuel k xs

theorem policy_valid : PivotValid (fun xs : List α => (FixedRank.select0Run xs).1) := by
  simpa only [FixedRank.select0Run_value] using
    (Applications.Selection.FixedRank.select0_pivot_valid (α := α))

theorem run_value (fuel k : Nat) (xs : List α) (hf : xs.length ≤ fuel) :
    (run fuel k xs).1.1 = (ordered xs)[k]? :=
  SelectionPolicy.runWith_correct FixedRank.select0Run policy_valid fuel k xs hf

/-- Distinctness is used only for one equal occurrence, not for value correctness. -/
theorem minimum_bucket_sizes (xs : List α) (p : α) (hn : xs.Nodup)
    (hp : Applications.Selection.FixedRank.select0 xs = some p) :
    (partition3 p xs).1.length = 0 ∧ (partition3 p xs).2.1.length = 1 ∧
      (partition3 p xs).2.2.length + 1 = xs.length ∧
      (partition3 p xs).2.2.Nodup := by
  have hr := (Applications.Selection.FixedRank.select0_some_iff_ranked xs p).mp hp
  have hc := ranked_strict_counts xs 0 p hn hr
  have hl : (partition3 p xs).1.length = 0 := by
    simpa only [partition3_eq_filters, List.countP_eq_length_filter] using hc.1
  have hu : (partition3 p xs).2.2.length = xs.length - 1 := by
    simpa only [partition3_eq_filters, List.countP_eq_length_filter,
      Nat.sub_zero] using hc.2
  have hpos := hr.lt_length
  have hs := partition_lengths p xs
  have hnodup : (partition3 p xs).2.2.Nodup := by
    rw [partition3_eq_filters]
    exact hn.filter _
  exact ⟨hl, by omega, by omega, hnodup⟩

/-- With rank zero the first minimum pivot is already the desired occurrence. -/
theorem run_zero_rank (fuel : Nat) (xs : List α) (hn : xs.Nodup) (hx : xs ≠ []) :
    run (fuel + 1) 0 xs =
      ((Applications.Selection.FixedRank.select0 xs, [xs.length]), 3 * xs.length + 8) := by
  obtain ⟨p, hp, _⟩ := Applications.Selection.FixedRank.select0_pivot_valid xs hx
  obtain ⟨hl, he, _, _⟩ := minimum_bucket_sizes xs p hn hp
  have hp' : (FixedRank.select0Run xs).1 = some p := by
    rw [FixedRank.select0Run_value, hp]
  have hi := partition_equal_getElem? p xs 0 (by omega)
  rw [run, SelectionPolicy.runWith_step _ fuel 0 xs hx p hp']
  simp only [hl, he, FixedRank.select0Run_cost]
  change (((partition3 p xs).2.1[0]?, [xs.length]),
    (xs.length + 1) + (xs.length + 1) + (xs.length + 1) + 1 + 2 + 1 + 1) =
      ((Applications.Selection.FixedRank.select0 xs, [xs.length]), 3 * xs.length + 8)
  rw [hi, hp]
  congr 1
  omega

/-- On distinct data, one minimum occurrence is removed and rank drops by one.
The real minimum construction contributes `n+1` to the step's `3*n+7` calls. -/
theorem run_succ_rank (fuel k : Nat) (xs : List α) (p : α) (hn : xs.Nodup)
    (hp : Applications.Selection.FixedRank.select0 xs = some p) :
    run (fuel + 1) (k + 1) xs =
      SelectionPolicy.prepend xs.length (3 * xs.length + 7)
        (run fuel k (partition3 p xs).2.2) := by
  have hx : xs ≠ [] := by
    intro he
    subst xs
    simp [Applications.Selection.FixedRank.select0] at hp
  obtain ⟨hl, he, _, _⟩ := minimum_bucket_sizes xs p hn hp
  have hp' : (FixedRank.select0Run xs).1 = some p := by
    rw [FixedRank.select0Run_value, hp]
  rw [run, SelectionPolicy.runWith_step _ fuel (k + 1) xs hx p hp']
  simp only [hl, he, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add,
    show ¬ k + 1 < 1 by omega, Nat.sub_zero, Nat.add_sub_cancel,
    FixedRank.select0Run_cost]
  unfold run SelectionPolicy.prepend
  congr 1
  omega

/-- The predicted active sizes, independent of input order. -/
def sizes (n : Nat) : Nat → List Nat
  | 0 => [n]
  | k + 1 => n :: sizes (n - 1) k

theorem sizes_length (n k : Nat) : (sizes n k).length = k + 1 := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [sizes, List.length_cons, ih]

/-- The observation theorem follows the actual selected strict bucket. -/
theorem run_observations (fuel k : Nat) (xs : List α) (hn : xs.Nodup)
    (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    (run fuel k xs).1.2 = sizes xs.length k ∧
      (run fuel k xs).2 = 3 * (sizes xs.length k).sum + 7 * (k + 1) + 1 := by
  induction fuel generalizing k xs with
  | zero => omega
  | succ fuel ih =>
      have hx : xs ≠ [] := List.ne_nil_of_length_pos (by omega)
      cases k with
      | zero =>
          rw [run_zero_rank fuel xs hn hx]
          constructor
          · rfl
          · change 3 * xs.length + 8 = 3 * xs.length + 7 + 1
            omega
      | succ k =>
          obtain ⟨p, hp, _⟩ := Applications.Selection.FixedRank.select0_pivot_valid xs hx
          obtain ⟨_, _, hs, hd⟩ := minimum_bucket_sizes xs p hn hp
          have hi := ih k (partition3 p xs).2.2 hd (by omega) (by omega)
          rw [run_succ_rank fuel k xs p hn hp]
          have he : (partition3 p xs).2.2.length = xs.length - 1 := by omega
          constructor
          · change xs.length :: (run fuel k (partition3 p xs).2.2).1.2 =
              xs.length :: sizes (xs.length - 1) k
            rw [hi.1, he]
          · change (3 * xs.length + 7) + (run fuel k (partition3 p xs).2.2).2 =
              3 * (xs.length + (sizes (xs.length - 1) k).sum) + 7 * (k + 1 + 1) + 1
            rw [hi.2, he]
            omega

theorem run_trace (fuel k : Nat) (xs : List α) (hn : xs.Nodup)
    (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    (run fuel k xs).1.2 = sizes xs.length k :=
  (run_observations fuel k xs hn hk hf).1

/-- Entries include the final equal-branch invocation. -/
theorem active_calls (fuel k : Nat) (xs : List α) (hn : xs.Nodup)
    (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    (run fuel k xs).1.2.length = k + 1 := by
  rw [run_trace fuel k xs hn hk hf, sizes_length]

/-- Each active invocation except the last makes one recursive edge. -/
theorem recursive_edges (fuel k : Nat) (xs : List α) (hn : xs.Nodup)
    (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    (run fuel k xs).1.2.length - 1 = k := by
  rw [active_calls fuel k xs hn hk hf]
  omega

/-- Division-free triangular subtraction, retaining the valid-rank domain. -/
theorem sizes_sum_double (n k : Nat) (hk : k < n) :
    2 * (sizes n k).sum + k * (k + 1) = 2 * ((k + 1) * n) := by
  induction k generalizing n with
  | zero => simp [sizes]
  | succ k ih =>
      cases n with
      | zero => omega
      | succ n =>
          have ht := ih n (by omega)
          simp only [sizes, Nat.add_sub_cancel, List.sum_cons]
          nlinarith

theorem sizes_sum (n k : Nat) (hk : k < n) :
    (sizes n k).sum = (k + 1) * n - k * (k + 1) / 2 := by
  have h := sizes_sum_double n k hk
  omega

theorem sizes_sum_bounds (n k : Nat) (hk : k < n) :
    n ≤ (sizes n k).sum ∧ (sizes n k).sum ≤ (k + 1) * n := by
  constructor
  · cases k <;> simp [sizes]
  · rw [sizes_sum n k hk]
    exact Nat.sub_le _ _

/-- The p35 exact scan formula counts occurrences scanned, not source calls. -/
theorem scan_exact (fuel k : Nat) (xs : List α) (hn : xs.Nodup)
    (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    (run fuel k xs).1.2.sum = (k + 1) * xs.length - k * (k + 1) / 2 := by
  rw [run_trace fuel k xs hn hk hf, sizes_sum xs.length k hk]

/-- Transfer the actual minimum/partition/length/lookup charge to the trace. -/
theorem cost_exact (fuel k : Nat) (xs : List α) (hn : xs.Nodup)
    (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    (run fuel k xs).2 = 3 * (run fuel k xs).1.2.sum + 7 * (k + 1) + 1 := by
  rw [run_trace fuel k xs hn hk hf]
  exact (run_observations fuel k xs hn hk hf).2

/-- One constant for every list at the chosen fixed rank; pivot search is paid. -/
theorem fixed_rank_linear (fuel k : Nat) (xs : List α) (hn : xs.Nodup)
    (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    xs.length ≤ (run fuel k xs).2 ∧
      (run fuel k xs).2 ≤ (10 * (k + 1) + 1) * xs.length := by
  rw [(run_observations fuel k xs hn hk hf).2]
  have hb := sizes_sum_bounds xs.length k hk
  have hp : 1 ≤ xs.length := by omega
  constructor
  · omega
  · have hm : k + 1 ≤ (k + 1) * xs.length := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (k + 1) hp
    nlinarith

/-- At the largest valid rank, the active sizes are `n,n-1,...,1`. -/
theorem largest_scan_double (fuel : Nat) (xs : List α) (hn : xs.Nodup)
    (hx : xs ≠ []) (hf : xs.length ≤ fuel) :
    2 * (run fuel (xs.length - 1) xs).1.2.sum = xs.length * (xs.length + 1) := by
  have hp := List.length_pos_iff.mpr hx
  rw [run_trace fuel (xs.length - 1) xs hn (by omega) hf]
  have h := sizes_sum_double xs.length (xs.length - 1) (by omega)
  have he : xs.length - 1 + 1 = xs.length := by omega
  have hm := congrArg (fun m : Nat => m * xs.length) he
  rw [he] at h
  nlinarith

theorem largest_scan (fuel : Nat) (xs : List α) (hn : xs.Nodup)
    (hx : xs ≠ []) (hf : xs.length ≤ fuel) :
    (run fuel (xs.length - 1) xs).1.2.sum = xs.length * (xs.length + 1) / 2 := by
  rw [← largest_scan_double fuel xs hn hx hf]
  omega

/-- Explicit quadratic constants, valid on every positive distinct input.
No asymptotic assertion is made for arbitrary target ranks or duplicate data. -/
theorem largest_cost_quadratic (fuel : Nat) (xs : List α) (hn : xs.Nodup)
    (hx : xs ≠ []) (hf : xs.length ≤ fuel) :
    xs.length ^ 2 ≤ 2 * (run fuel (xs.length - 1) xs).2 ∧
      (run fuel (xs.length - 1) xs).2 ≤ 11 * xs.length ^ 2 := by
  have hp := List.length_pos_iff.mpr hx
  have hs := largest_scan_double fuel xs hn hx hf
  have hc := cost_exact fuel (xs.length - 1) xs hn (by omega) hf
  have he : xs.length - 1 + 1 = xs.length := by omega
  rw [he] at hc
  have hnn : xs.length ≤ xs.length ^ 2 := by
    simpa only [Nat.pow_two, Nat.mul_one] using
      Nat.mul_le_mul_left xs.length (show 1 ≤ xs.length by omega)
  constructor <;> nlinarith

end Resources.MinimumPivot
