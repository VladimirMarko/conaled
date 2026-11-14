import Applications.Sorting.BottomUp
import Applications.Resources.ListMerge
import Applications.Resources.Growth
import Mathlib.Data.Nat.Log

/-!
# Comparisons in adjacent-run bottom-up merge sort

The FDSA §2.5 pass executes the existing measured merge on each adjacent pair.
Repeated merging uses the runs that this execution actually returned. Only
head comparisons are charged: run dispatch, singleton initialization, outer-list
construction and traversal, and the comparator's own implementation are outside
this tariff. Value erasure and the source counter equations are separate laws.

Exercise 2.6's append-free accumulator pass compares the same pairs, but reverses
the order of the completed runs. Its per-pass comparison count is unchanged;
its complete merge tree can have a different count. Both repeated algorithms
satisfy the same total-length times ceiling-log run-count bound.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.BottomUpSorting

open Applications.Sorting
universe u
variable {α : Type u}

/-- Merge each actual adjacent pair, then retain the returned run and tail runs. -/
def pairsRun (cmp : α → α → Bool) : List (List α) → Measured (List (List α)) Nat
  | [] => Resources.pure []
  | [xs] => Resources.pure [xs]
  | xs :: ys :: rest =>
    Resources.bind (Resources.reweight Prod.fst (ListMerge.run cmp xs ys)) fun merged =>
      Resources.bind (pairsRun cmp rest) fun runs => Resources.pure (merged :: runs)

abbrev pairsComparisons (cmp : α → α → Bool) (xss : List (List α)) : Nat :=
  (pairsRun cmp xss).2

@[simp] theorem pairsRun_nil (cmp : α → α → Bool) : pairsRun cmp [] = ([], 0) := rfl

@[simp] theorem pairsRun_singleton (cmp : α → α → Bool) (xs : List α) :
    pairsRun cmp [xs] = ([xs], 0) := rfl

theorem pairsRun_step (cmp : α → α → Bool) (xs ys : List α) (rest : List (List α)) :
    pairsRun cmp (xs :: ys :: rest) =
      Resources.bind (Resources.reweight Prod.fst (ListMerge.run cmp xs ys)) fun merged =>
        Resources.bind (pairsRun cmp rest) fun runs => Resources.pure (merged :: runs) := rfl

theorem pairsRun_value (cmp : α → α → Bool) (xss : List (List α)) :
    (pairsRun cmp xss).1 = mergePairsBy cmp xss := by
  match xss with
  | [] => rfl
  | [xs] => rfl
  | xs :: ys :: rest =>
    simp only [pairsRun_step, Resources.bind_value, Resources.reweight_value,
      ListMerge.run_value, Resources.pure, pairsRun_value cmp rest, mergePairsBy_step]

@[simp] theorem pairsComparisons_nil (cmp : α → α → Bool) :
    pairsComparisons cmp [] = 0 := rfl

@[simp] theorem pairsComparisons_singleton (cmp : α → α → Bool) (xs : List α) :
    pairsComparisons cmp [xs] = 0 := rfl

/-- The source's exact additive counter, projected from the executed pass. -/
theorem pairsComparisons_step (cmp : α → α → Bool) (xs ys : List α)
    (rest : List (List α)) :
    pairsComparisons cmp (xs :: ys :: rest) =
      ListMerge.comparisons cmp xs ys + pairsComparisons cmp rest := by
  simp [pairsComparisons, pairsRun_step, Resources.bind, Resources.reweight,
    Resources.pure, ListMerge.comparisons]

/-- Empty runs and odd leftovers are allowed; no ordering or uniformity is needed. -/
theorem pairsComparisons_le (cmp : α → α → Bool) (xss : List (List α)) :
    pairsComparisons cmp xss ≤ xss.flatten.length := by
  match xss with
  | [] => simp
  | [xs] => simp
  | xs :: ys :: rest =>
    rw [pairsComparisons_step]
    have hm := ListMerge.comparisons_le cmp xs ys
    have hr := pairsComparisons_le cmp rest
    simp only [List.flatten_cons, List.length_append]
    omega

private theorem flatten_length_uniform (xss : List (List α)) (m : Nat)
    (hl : ∀ xs ∈ xss, xs.length = m) : xss.flatten.length = m * xss.length := by
  match xss with
  | [] => simp
  | xs :: rest =>
    have hr := flatten_length_uniform rest m (fun ys hy => hl ys (by simp [hy]))
    rw [List.flatten_cons, List.length_append, List.length_cons,
      hl xs (by simp), hr, Nat.mul_succ]
    omega

/-- The printed uniform-run pass bound does not require an even number of runs. -/
theorem pairsComparisons_le_uniform (cmp : α → α → Bool) (xss : List (List α))
    (m : Nat) (hl : ∀ xs ∈ xss, xs.length = m) :
    pairsComparisons cmp xss ≤ m * xss.length := by
  rw [← flatten_length_uniform xss m hl]
  exact pairsComparisons_le cmp xss

/-- The pinned natural ceiling-log recurrence at the actual next run count. -/
theorem clog_two_ceil_half (n : Nat) (hn : 2 ≤ n) :
    Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
  have heq : n + 2 - 1 = n + 1 := by omega
  simpa only [heq] using Nat.clog_of_two_le (b := 2) (n := n) (by decide) hn

/-- Source display (2.29)'s arithmetically equivalent half, with its necessary domain. -/
theorem clog_two_source_half (n : Nat) (hn : 2 ≤ n) :
    Nat.clog 2 n = Nat.clog 2 ((n - 1) / 2 + 1) + 1 := by
  have heq : (n + 1) / 2 = (n - 1) / 2 + 1 := by omega
  simpa only [heq] using clog_two_ceil_half n hn

/-- The integer-ceiling source convention agrees also at zero and one. -/
theorem int_ceil_logb_two_nat (n : Nat) :
    ⌈Real.logb 2 (n : ℝ)⌉ = (Nat.clog 2 n : ℤ) := by
  simpa only [Nat.cast_ofNat, Int.clog_natCast] using
    Real.ceil_logb_natCast (b := 2) (r := (n : ℝ)) (Nat.cast_nonneg n)

theorem int_ceil_logb_two_source_half (n : Nat) (hn : 2 ≤ n) :
    ⌈Real.logb 2 (n : ℝ)⌉ =
      ⌈Real.logb 2 (((n - 1) / 2 + 1 : Nat) : ℝ)⌉ + 1 := by
  rw [int_ceil_logb_two_nat n, int_ceil_logb_two_nat ((n - 1) / 2 + 1),
    clog_two_source_half n hn,
    Nat.cast_add, Nat.cast_one]

/-- The recursive call uses the first projection of the same measured pass.
Capturing that pair exposes its decreasing run count without executing it twice. -/
def allRun (cmp : α → α → Bool) (xss : List (List α)) : Measured (List α) Nat :=
  match xss with
  | [] => Resources.pure []
  | [xs] => Resources.pure xs
  | xs :: ys :: rest =>
    let next := pairsRun cmp (xs :: ys :: rest)
    Resources.bind next (fun _ => allRun cmp next.1)
termination_by xss.length
decreasing_by
  rw [pairsRun_value]
  exact mergePairsBy_length_lt cmp _ (by simp)

abbrev allComparisons (cmp : α → α → Bool) (xss : List (List α)) : Nat :=
  (allRun cmp xss).2

@[simp] theorem allRun_nil (cmp : α → α → Bool) : allRun cmp [] = ([], 0) := by
  rw [allRun]
  rfl

@[simp] theorem allRun_singleton (cmp : α → α → Bool) (xs : List α) :
    allRun cmp [xs] = (xs, 0) := by
  rw [allRun]
  rfl

/-- Sequencing feeds the pass's actual returned list into the next execution. -/
theorem allRun_step (cmp : α → α → Bool) (xs ys : List α) (rest : List (List α)) :
    allRun cmp (xs :: ys :: rest) =
      Resources.bind (pairsRun cmp (xs :: ys :: rest)) (allRun cmp) := by
  rw [allRun]
  rfl

theorem allRun_value (cmp : α → α → Bool) (xss : List (List α)) :
    (allRun cmp xss).1 = mergeAllBy cmp xss := by
  match xss with
  | [] => simp
  | [xs] => simp
  | xs :: ys :: rest =>
    rw [allRun_step, Resources.bind_value, pairsRun_value, mergeAllBy_step]
    exact allRun_value cmp (mergePairsBy cmp (xs :: ys :: rest))
termination_by xss.length
decreasing_by
  exact mergePairsBy_length_lt cmp _ (by simp)

theorem allRun_perm (cmp : α → α → Bool) (xss : List (List α)) :
    (allRun cmp xss).1.Perm xss.flatten := by
  rw [allRun_value]
  exact mergeAllBy_perm cmp xss

@[simp] theorem allComparisons_nil (cmp : α → α → Bool) :
    allComparisons cmp [] = 0 := by simp [allComparisons]

@[simp] theorem allComparisons_singleton (cmp : α → α → Bool) (xs : List α) :
    allComparisons cmp [xs] = 0 := by simp [allComparisons]

theorem allComparisons_step (cmp : α → α → Bool) (xs ys : List α)
    (rest : List (List α)) :
    allComparisons cmp (xs :: ys :: rest) =
      pairsComparisons cmp (xs :: ys :: rest) +
      allComparisons cmp (mergePairsBy cmp (xs :: ys :: rest)) := by
  simp [allComparisons, allRun_step, Resources.bind, pairsRun_value, pairsComparisons]

/-- The general bound uses total payload length and the number of runs separately. -/
theorem allComparisons_le_clog (cmp : α → α → Bool) (xss : List (List α)) :
    allComparisons cmp xss ≤ xss.flatten.length * Nat.clog 2 xss.length := by
  match xss with
  | [] => simp
  | [xs] => simp
  | xs :: ys :: rest =>
    have hp := pairsComparisons_le cmp (xs :: ys :: rest)
    have hi := allComparisons_le_clog cmp (mergePairsBy cmp (xs :: ys :: rest))
    rw [mergePairsBy_flatten_length, mergePairsBy_length] at hi
    have hlog := clog_two_ceil_half (xs :: ys :: rest).length (by simp)
    rw [allComparisons_step]
    calc
      _ ≤ (xs :: ys :: rest).flatten.length +
          (xs :: ys :: rest).flatten.length * Nat.clog 2 (((xs :: ys :: rest).length + 1) / 2) :=
        Nat.add_le_add hp hi
      _ = (xs :: ys :: rest).flatten.length * Nat.clog 2 (xs :: ys :: rest).length := by
        rw [hlog, Nat.mul_add, Nat.mul_one]
        omega
termination_by xss.length
decreasing_by
  exact mergePairsBy_length_lt cmp _ (by simp)

/-- The source's integer-ceiling statement, with no hidden positivity restriction. -/
theorem allComparisons_le_int_ceil (cmp : α → α → Bool) (xss : List (List α)) :
    (allComparisons cmp xss : ℤ) ≤
      (xss.flatten.length : ℤ) * ⌈Real.logb 2 (xss.length : ℝ)⌉ := by
  rw [int_ceil_logb_two_nat]
  exact_mod_cast allComparisons_le_clog cmp xss

/-- Lemma 2.5 retains both the uniform-length and power-of-two premises, including `m=0`. -/
theorem allComparisons_le_uniform_pow (cmp : α → α → Bool) (xss : List (List α))
    (m k : Nat) (hl : ∀ xs ∈ xss, xs.length = m) (hk : xss.length = 2 ^ k) :
    allComparisons cmp xss ≤ m * k * 2 ^ k := by
  calc
    _ ≤ xss.flatten.length * Nat.clog 2 xss.length := allComparisons_le_clog cmp xss
    _ = (m * 2 ^ k) * k := by
      rw [flatten_length_uniform xss m hl, hk, Nat.clog_pow 2 k (by decide)]
    _ = m * k * 2 ^ k := by ring

/-- Initialize one singleton run for each occurrence; initialization is uncharged. -/
def run (cmp : α → α → Bool) (xs : List α) : Measured (List α) Nat :=
  allRun cmp (xs.map fun x => [x])

abbrev comparisons (cmp : α → α → Bool) (xs : List α) : Nat := (run cmp xs).2

@[simp] theorem run_nil (cmp : α → α → Bool) : run cmp [] = ([], 0) := by simp [run]

@[simp] theorem run_singleton (cmp : α → α → Bool) (x : α) :
    run cmp [x] = ([x], 0) := by simp [run]

theorem run_value (cmp : α → α → Bool) (xs : List α) :
    (run cmp xs).1 = sortBottomUpBy cmp xs := by
  simp only [run, allRun_value, sortBottomUpBy]

theorem run_perm (cmp : α → α → Bool) (xs : List α) : (run cmp xs).1.Perm xs := by
  rw [run_value]
  exact sortBottomUpBy_perm cmp xs

/-- The handwritten sorter counter is the projection after singleton initialization. -/
theorem comparisons_eq_all (cmp : α → α → Bool) (xs : List α) :
    comparisons cmp xs = allComparisons cmp (xs.map fun x => [x]) := rfl

theorem comparisons_le_clog (cmp : α → α → Bool) (xs : List α) :
    comparisons cmp xs ≤ xs.length * Nat.clog 2 xs.length := by
  have hflat : (xs.map fun x => [x]).flatten = xs := List.flatMap_singleton' xs
  simpa only [comparisons_eq_all, hflat, List.length_map] using
    allComparisons_le_clog cmp (xs.map fun x => [x])

/-- Corollary 2.6, including the exponent-zero singleton case. -/
theorem comparisons_le_of_length_pow (cmp : α → α → Bool) (xs : List α) (k : Nat)
    (hlen : xs.length = 2 ^ k) : comparisons cmp xs ≤ k * 2 ^ k := by
  simpa [hlen, Nat.mul_comm] using comparisons_le_clog cmp xs

theorem comparisons_le_real_log_of_length_pow (cmp : α → α → Bool) (xs : List α)
    (k : Nat) (hlen : xs.length = 2 ^ k) :
    (comparisons cmp xs : ℝ) ≤ (xs.length : ℝ) * Real.logb 2 xs.length := by
  have hb : (comparisons cmp xs : ℝ) ≤ (k : ℝ) * (2 : ℝ) ^ k := by
    exact_mod_cast comparisons_le_of_length_pow cmp xs k hlen
  have hlog : Real.logb 2 ((2 : ℝ) ^ k) = k := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  simpa only [hlen, Nat.cast_pow, Nat.cast_ofNat, hlog, mul_comm] using hb

theorem comparisons_isBigO (cmp : α → α → Bool) (inputs : Nat → List α)
    (hlen : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (comparisons cmp (inputs n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Resources.isBigO_of_clog_two_bound (C := 1) (N := 0)
  intro n _
  simpa only [hlen, one_mul] using comparisons_le_clog cmp (inputs n)

/-- The measured accumulator pass uses the returned merged run, cons and recursion.
Its implementation contains neither append nor reverse. -/
def pairsRevRun (cmp : α → α → Bool) (acc : List (List α)) :
    List (List α) → Measured (List (List α)) Nat
  | [] => Resources.pure acc
  | [xs] => Resources.pure (xs :: acc)
  | xs :: ys :: rest =>
    Resources.bind (Resources.reweight Prod.fst (ListMerge.run cmp xs ys)) fun merged =>
      pairsRevRun cmp (merged :: acc) rest

abbrev pairsRevComparisons (cmp : α → α → Bool) (acc xss : List (List α)) : Nat :=
  (pairsRevRun cmp acc xss).2

@[simp] theorem pairsRevRun_nil (cmp : α → α → Bool) (acc : List (List α)) :
    pairsRevRun cmp acc [] = (acc, 0) := rfl

@[simp] theorem pairsRevRun_singleton (cmp : α → α → Bool)
    (acc : List (List α)) (xs : List α) :
    pairsRevRun cmp acc [xs] = (xs :: acc, 0) := rfl

theorem pairsRevRun_step (cmp : α → α → Bool) (acc : List (List α))
    (xs ys : List α) (rest : List (List α)) :
    pairsRevRun cmp acc (xs :: ys :: rest) =
      Resources.bind (Resources.reweight Prod.fst (ListMerge.run cmp xs ys)) fun merged =>
        pairsRevRun cmp (merged :: acc) rest := rfl

theorem pairsRevRun_value (cmp : α → α → Bool) (acc xss : List (List α)) :
    (pairsRevRun cmp acc xss).1 = mergePairsRevBy cmp acc xss := by
  match xss with
  | [] => rfl
  | [xs] => rfl
  | xs :: ys :: rest =>
    rw [pairsRevRun_step, Resources.bind_value, Resources.reweight_value,
      ListMerge.run_value, mergePairsRevBy_step]
    exact pairsRevRun_value cmp (List.merge xs ys cmp :: acc) rest

@[simp] theorem pairsRevComparisons_nil (cmp : α → α → Bool) (acc : List (List α)) :
    pairsRevComparisons cmp acc [] = 0 := rfl

@[simp] theorem pairsRevComparisons_singleton (cmp : α → α → Bool)
    (acc : List (List α)) (xs : List α) : pairsRevComparisons cmp acc [xs] = 0 := rfl

theorem pairsRevComparisons_step (cmp : α → α → Bool) (acc : List (List α))
    (xs ys : List α) (rest : List (List α)) :
    pairsRevComparisons cmp acc (xs :: ys :: rest) = ListMerge.comparisons cmp xs ys +
      pairsRevComparisons cmp (List.merge xs ys cmp :: acc) rest := by
  simp [pairsRevComparisons, pairsRevRun_step, Resources.bind, Resources.reweight,
    ListMerge.comparisons, ListMerge.run_value]

/-- The untouched arbitrary accumulator contributes no comparisons to this pass. -/
theorem pairsRevComparisons_eq (cmp : α → α → Bool) (acc xss : List (List α)) :
    pairsRevComparisons cmp acc xss = pairsComparisons cmp xss := by
  match xss with
  | [] => rfl
  | [xs] => rfl
  | xs :: ys :: rest =>
    rw [pairsRevComparisons_step, pairsComparisons_step,
      pairsRevComparisons_eq cmp (List.merge xs ys cmp :: acc) rest]

/-- Exact value and cost correspondence for one pass, for every accumulator. -/
theorem pairsRevRun_eq (cmp : α → α → Bool) (acc xss : List (List α)) :
    pairsRevRun cmp acc xss =
      ((pairsRun cmp xss).1.reverse ++ acc, (pairsRun cmp xss).2) := by
  apply Prod.ext
  · simp only [pairsRevRun_value, pairsRun_value, mergePairsRevBy_eq_reverse_append]
  · exact pairsRevComparisons_eq cmp acc xss

theorem pairsRevComparisons_le (cmp : α → α → Bool) (acc xss : List (List α)) :
    pairsRevComparisons cmp acc xss ≤ xss.flatten.length := by
  rw [pairsRevComparisons_eq]
  exact pairsComparisons_le cmp xss

theorem pairsRevComparisons_le_uniform (cmp : α → α → Bool)
    (acc xss : List (List α)) (m : Nat) (hl : ∀ xs ∈ xss, xs.length = m) :
    pairsRevComparisons cmp acc xss ≤ m * xss.length := by
  rw [pairsRevComparisons_eq]
  exact pairsComparisons_le_uniform cmp xss m hl

/-- Repeated reversed passes use an empty accumulator and their actual returned runs. -/
def allRevRun (cmp : α → α → Bool) (xss : List (List α)) : Measured (List α) Nat :=
  match xss with
  | [] => Resources.pure []
  | [xs] => Resources.pure xs
  | xs :: ys :: rest =>
    let next := pairsRevRun cmp [] (xs :: ys :: rest)
    Resources.bind next (fun _ => allRevRun cmp next.1)
termination_by xss.length
decreasing_by
  rw [pairsRevRun_value]
  exact mergePairsRevBy_empty_length_lt cmp _ (by simp)

abbrev allRevComparisons (cmp : α → α → Bool) (xss : List (List α)) : Nat :=
  (allRevRun cmp xss).2

@[simp] theorem allRevRun_nil (cmp : α → α → Bool) : allRevRun cmp [] = ([], 0) := by
  rw [allRevRun]
  rfl

@[simp] theorem allRevRun_singleton (cmp : α → α → Bool) (xs : List α) :
    allRevRun cmp [xs] = (xs, 0) := by
  rw [allRevRun]
  rfl

theorem allRevRun_step (cmp : α → α → Bool) (xs ys : List α)
    (rest : List (List α)) :
    allRevRun cmp (xs :: ys :: rest) =
      Resources.bind (pairsRevRun cmp [] (xs :: ys :: rest)) (allRevRun cmp) := by
  rw [allRevRun]
  rfl

theorem allRevRun_value (cmp : α → α → Bool) (xss : List (List α)) :
    (allRevRun cmp xss).1 = mergeAllRevBy cmp xss := by
  match xss with
  | [] => simp
  | [xs] => simp
  | xs :: ys :: rest =>
    rw [allRevRun_step, Resources.bind_value, pairsRevRun_value, mergeAllRevBy_step]
    exact allRevRun_value cmp (mergePairsRevBy cmp [] (xs :: ys :: rest))
termination_by xss.length
decreasing_by
  exact mergePairsRevBy_empty_length_lt cmp _ (by simp)

theorem allRevRun_perm (cmp : α → α → Bool) (xss : List (List α)) :
    (allRevRun cmp xss).1.Perm xss.flatten := by
  rw [allRevRun_value]
  exact mergeAllRevBy_perm cmp xss

@[simp] theorem allRevComparisons_nil (cmp : α → α → Bool) :
    allRevComparisons cmp [] = 0 := by simp [allRevComparisons]

@[simp] theorem allRevComparisons_singleton (cmp : α → α → Bool) (xs : List α) :
    allRevComparisons cmp [xs] = 0 := by simp [allRevComparisons]

theorem allRevComparisons_step (cmp : α → α → Bool) (xs ys : List α)
    (rest : List (List α)) :
    allRevComparisons cmp (xs :: ys :: rest) =
      pairsRevComparisons cmp [] (xs :: ys :: rest) +
      allRevComparisons cmp (mergePairsRevBy cmp [] (xs :: ys :: rest)) := by
  simp [allRevComparisons, allRevRun_step, Resources.bind,
    pairsRevRun_value, pairsRevComparisons]

/-- A separate bound for the actual reversed-pass merge tree, not equality of totals. -/
theorem allRevComparisons_le_clog (cmp : α → α → Bool) (xss : List (List α)) :
    allRevComparisons cmp xss ≤ xss.flatten.length * Nat.clog 2 xss.length := by
  match xss with
  | [] => simp
  | [xs] => simp
  | xs :: ys :: rest =>
    have hp := pairsRevComparisons_le cmp [] (xs :: ys :: rest)
    have hi := allRevComparisons_le_clog cmp (mergePairsRevBy cmp [] (xs :: ys :: rest))
    rw [mergePairsRevBy_flatten_length, mergePairsRevBy_length] at hi
    simp only [List.flatten_nil, List.length_nil, Nat.zero_add] at hi
    have hlog := clog_two_ceil_half (xs :: ys :: rest).length (by simp)
    rw [allRevComparisons_step]
    calc
      _ ≤ (xs :: ys :: rest).flatten.length +
          (xs :: ys :: rest).flatten.length * Nat.clog 2 (((xs :: ys :: rest).length + 1) / 2) :=
        Nat.add_le_add hp hi
      _ = (xs :: ys :: rest).flatten.length * Nat.clog 2 (xs :: ys :: rest).length := by
        rw [hlog, Nat.mul_add, Nat.mul_one]
        omega
termination_by xss.length
decreasing_by
  exact mergePairsRevBy_empty_length_lt cmp _ (by simp)

theorem allRevComparisons_le_int_ceil (cmp : α → α → Bool) (xss : List (List α)) :
    (allRevComparisons cmp xss : ℤ) ≤
      (xss.flatten.length : ℤ) * ⌈Real.logb 2 (xss.length : ℝ)⌉ := by
  rw [int_ceil_logb_two_nat]
  exact_mod_cast allRevComparisons_le_clog cmp xss

theorem allRevComparisons_le_uniform_pow (cmp : α → α → Bool) (xss : List (List α))
    (m k : Nat) (hl : ∀ xs ∈ xss, xs.length = m) (hk : xss.length = 2 ^ k) :
    allRevComparisons cmp xss ≤ m * k * 2 ^ k := by
  calc
    _ ≤ xss.flatten.length * Nat.clog 2 xss.length := allRevComparisons_le_clog cmp xss
    _ = (m * 2 ^ k) * k := by
      rw [flatten_length_uniform xss m hl, hk, Nat.clog_pow 2 k (by decide)]
    _ = m * k * 2 ^ k := by ring

def revRun (cmp : α → α → Bool) (xs : List α) : Measured (List α) Nat :=
  allRevRun cmp (xs.map fun x => [x])

abbrev revComparisons (cmp : α → α → Bool) (xs : List α) : Nat := (revRun cmp xs).2

@[simp] theorem revRun_nil (cmp : α → α → Bool) : revRun cmp [] = ([], 0) := by
  simp [revRun]

@[simp] theorem revRun_singleton (cmp : α → α → Bool) (x : α) :
    revRun cmp [x] = ([x], 0) := by simp [revRun]

theorem revRun_value (cmp : α → α → Bool) (xs : List α) :
    (revRun cmp xs).1 = sortBottomUpRevBy cmp xs := by
  simp only [revRun, allRevRun_value, sortBottomUpRevBy]

theorem revRun_perm (cmp : α → α → Bool) (xs : List α) :
    (revRun cmp xs).1.Perm xs := by
  rw [revRun_value]
  exact sortBottomUpRevBy_perm cmp xs

theorem revComparisons_eq_all (cmp : α → α → Bool) (xs : List α) :
    revComparisons cmp xs = allRevComparisons cmp (xs.map fun x => [x]) := rfl

theorem revComparisons_le_clog (cmp : α → α → Bool) (xs : List α) :
    revComparisons cmp xs ≤ xs.length * Nat.clog 2 xs.length := by
  have hflat : (xs.map fun x => [x]).flatten = xs := List.flatMap_singleton' xs
  simpa only [revComparisons_eq_all, hflat, List.length_map] using
    allRevComparisons_le_clog cmp (xs.map fun x => [x])

theorem revComparisons_le_of_length_pow (cmp : α → α → Bool) (xs : List α) (k : Nat)
    (hlen : xs.length = 2 ^ k) : revComparisons cmp xs ≤ k * 2 ^ k := by
  simpa [hlen, Nat.mul_comm] using revComparisons_le_clog cmp xs

theorem revComparisons_le_real_log_of_length_pow (cmp : α → α → Bool) (xs : List α)
    (k : Nat) (hlen : xs.length = 2 ^ k) :
    (revComparisons cmp xs : ℝ) ≤ (xs.length : ℝ) * Real.logb 2 xs.length := by
  have hb : (revComparisons cmp xs : ℝ) ≤ (k : ℝ) * (2 : ℝ) ^ k := by
    exact_mod_cast revComparisons_le_of_length_pow cmp xs k hlen
  have hlog : Real.logb 2 ((2 : ℝ) ^ k) = k := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  simpa only [hlen, Nat.cast_pow, Nat.cast_ofNat, hlog, mul_comm] using hb

theorem revComparisons_isBigO (cmp : α → α → Bool) (inputs : Nat → List α)
    (hlen : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (revComparisons cmp (inputs n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Resources.isBigO_of_clog_two_bound (C := 1) (N := 0)
  intro n _
  simpa only [hlen, one_mul] using revComparisons_le_clog cmp (inputs n)

end Resources.BottomUpSorting
