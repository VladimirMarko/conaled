import Applications.Resources.RandomSelectionDrift
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Absorbing size, residual expectations and the exact actual-selection tail.

These observations read the existing execution; they introduce no replacement
stochastic process or independence assumption. Time induction uses its checked
conditional drift. Standard Markov on the actual Nat residual marginal gives
the non-strict scan event at `(4+w)*n`, for natural `w` and positive length.
The checked same-run source bridge gives threshold `9*((4+w)*n)+2`.

The empty-input countercase explains the positive-length premise. These are
original proofs for the declared scan/source metrics, not a claim to reconstruct
the inaccessible Karp citation or an implementation of random-bit sampling.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomSelection
open MeasureTheory
open scoped BigOperators ENNReal
universe u v
variable {α : Type u}

/-- The recorded active size at time `j`, with absorbing zero once the actual
finite trace has ended. -/
def activeSize : Nat → Trace → Nat
  | _, [] => 0
  | 0, (n, _) :: _ => n
  | j + 1, _ :: trace => activeSize j trace

@[simp] theorem activeSize_nil (j : Nat) : activeSize j [] = 0 := by
  cases j <;> rfl

@[simp] theorem activeSize_zero_cons (n i : Nat) (trace : Trace) :
    activeSize 0 ((n, i) :: trace) = n := rfl

@[simp] theorem activeSize_succ_cons (j n i : Nat) (trace : Trace) :
    activeSize (j + 1) ((n, i) :: trace) = activeSize j trace := rfl

/-- Exhausting the finite trace gives zero at every later time. -/
theorem activeSize_eq_zero_of_length_le (j : Nat) (trace : Trace)
    (h : trace.length ≤ j) : activeSize j trace = 0 := by
  induction trace generalizing j with
  | nil => exact activeSize_nil j
  | cons entry trace ih =>
      cases j with
      | zero => simp only [List.length_cons] at h; omega
      | succ j =>
          rcases entry with ⟨n, i⟩
          rw [activeSize_succ_cons]
          exact ih j (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using h)

/-- Scan volume is the sum of the actual active-size observations before
absorption. -/
theorem scanVolume_eq_sum_activeSize (trace : Trace) :
    scanVolume trace = ∑ j ∈ Finset.range trace.length, activeSize j trace := by
  induction trace with
  | nil => simp
  | cons entry trace ih =>
      rcases entry with ⟨n, i⟩
      rw [scanVolume_cons, List.length_cons, Finset.sum_range_succ']
      simp only [activeSize_succ_cons, activeSize_zero_cons]
      rw [← ih, Nat.add_comm]

/-- Work still recorded after the first `w` active invocations. -/
def residualWork (w : Nat) (trace : Trace) : Nat := scanVolume (trace.drop w)

@[simp] theorem residualWork_nil (w : Nat) : residualWork w [] = 0 := by
  simp [residualWork]

@[simp] theorem residualWork_zero (trace : Trace) : residualWork 0 trace = scanVolume trace := rfl

@[simp] theorem residualWork_succ_cons (w n i : Nat) (trace : Trace) :
    residualWork (w + 1) ((n, i) :: trace) = residualWork w trace := rfl

theorem scanVolume_append (front back : Trace) :
    scanVolume (front ++ back) = scanVolume front + scanVolume back := by
  simp only [scanVolume, List.map_append, List.sum_append]

/-- Exact pathwise decomposition, including empty and overlong prefixes. -/
theorem scanVolume_take_add_residualWork (w : Nat) (trace : Trace) :
    scanVolume (trace.take w) + residualWork w trace = scanVolume trace := by
  rw [residualWork, ← scanVolume_append, List.take_append_drop]

theorem residualWork_le (w : Nat) (trace : Trace) :
    residualWork w trace ≤ scanVolume trace := by
  have h := scanVolume_take_add_residualWork w trace
  omega

theorem residualWork_eq_zero_of_length_le (w : Nat) (trace : Trace)
    (h : trace.length ≤ w) : residualWork w trace = 0 := by
  rw [residualWork, List.drop_of_length_le h, scanVolume_nil]

theorem activeSize_pos_of_lt (j : Nat) (trace : Trace) (hj : j < trace.length)
    (h : ∀ entry ∈ trace, 0 < entry.1) : 0 < activeSize j trace := by
  induction trace generalizing j with
  | nil => simp only [List.length_nil] at hj; omega
  | cons entry trace ih =>
      rcases entry with ⟨n, i⟩
      cases j with
      | zero => exact h (n, i) (List.mem_cons_self ..)
      | succ j =>
          apply ih j (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hj)
          intro entry he
          exact h entry (List.mem_cons_of_mem _ he)

theorem activeSize_le_of_entries_le (j n : Nat) (trace : Trace)
    (h : ∀ entry ∈ trace, entry.1 ≤ n) : activeSize j trace ≤ n := by
  induction trace generalizing j with
  | nil => simpa only [activeSize_nil] using Nat.zero_le n
  | cons entry trace ih =>
      rcases entry with ⟨m, i⟩
      cases j with
      | zero => exact h (m, i) (List.mem_cons_self ..)
      | succ j =>
          apply ih j
          intro entry he
          exact h entry (List.mem_cons_of_mem _ he)

/-- An initial segment pays at most its number of positions times the
common bound on actual recorded lengths. -/
theorem scanVolume_take_le (w n : Nat) (trace : Trace)
    (h : ∀ entry ∈ trace, entry.1 ≤ n) : scanVolume (trace.take w) ≤ w * n := by
  induction w generalizing trace with
  | zero => simp
  | succ w ih =>
      cases trace with
      | nil => simp
      | cons entry trace =>
          rcases entry with ⟨m, i⟩
          have hm := h (m, i) (List.mem_cons_self ..)
          have ht : ∀ entry ∈ trace, entry.1 ≤ n := by
            intro entry he
            exact h entry (List.mem_cons_of_mem _ he)
          change m + scanVolume (trace.take w) ≤ (w + 1) * n
          calc
            _ ≤ n + w * n := Nat.add_le_add hm (ih trace ht)
            _ = _ := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

noncomputable section

/-- A standard Nat marginal integral equals the weighted observation before
pushforward. No measurable structure on the original carrier is needed. -/
private theorem nat_map_lintegral {β : Type v} (p : PMF β) (f : β → Nat) :
    (∫⁻ n : Nat, (n : ℝ≥0∞) ∂(p.map f).toMeasure) =
      ∑' result, p result * (f result : ℝ≥0∞) := by
  classical
  rw [lintegral_countable']
  calc
    _ = ∑' n : Nat, (n : ℝ≥0∞) *
        (∑' result, if n = f result then p result else 0) := by
      apply tsum_congr
      intro n
      rw [PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n), PMF.map_apply]
      rfl
    _ = ∑' n : Nat, ∑' result,
        if n = f result then (n : ℝ≥0∞) * p result else 0 := by
      simp only [← ENNReal.tsum_mul_left, mul_ite, mul_zero]
    _ = ∑' result, ∑' n : Nat,
        if n = f result then (n : ℝ≥0∞) * p result else 0 := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro result
      rw [tsum_ite_eq, mul_comm]

section Ordered
variable [LinearOrder α]

/-- The first observation is the actual input length, including zero on the
empty worker extension. -/
theorem run_activeSize_zero (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) : activeSize 0 result.2.1 = xs.length := by
  cases xs with
  | nil =>
      have he : result = (none, ([], 2)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hr
      subst result
      rfl
  | cons head tail =>
      rw [run_cons] at hr
      obtain ⟨i, _, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
      dsimp only at hr
      cases hstep : (stepRun k (head :: tail) i).1 with
      | inl state =>
          rcases state with ⟨j, ys⟩
          rw [hstep] at hr
          obtain ⟨child, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
          rw [← he]
          rfl
      | inr p =>
          rw [hstep] at hr
          have he : result =
              (some p, ([((head :: tail).length, i.val)], (stepRun k (head :: tail) i).2)) :=
            (PMF.mem_support_pure_iff _ _).mp hr
          rw [he]
          rfl

theorem run_activeSize_le (j k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) : activeSize j result.2.1 ≤ xs.length :=
  activeSize_le_of_entries_le j xs.length result.2.1
    (fun entry he => (run_trace_entries k xs result hr entry he).2.2)

/-- Actual entries are positive; zero therefore occurs exactly after the
last active invocation, not at an intermediate state. -/
theorem run_activeSize_eq_zero_iff (j k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) :
    activeSize j result.2.1 = 0 ↔ result.2.1.length ≤ j := by
  constructor
  · intro hz
    by_contra hlen
    have hp := activeSize_pos_of_lt j result.2.1 (Nat.lt_of_not_ge hlen)
      (fun entry he => (run_trace_entries k xs result hr entry he).1)
    omega
  · exact activeSize_eq_zero_of_length_le j result.2.1

theorem run_activeSize_zero_persists (j l k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) (hjl : j ≤ l)
    (hz : activeSize j result.2.1 = 0) : activeSize l result.2.1 = 0 :=
  activeSize_eq_zero_of_length_le l result.2.1
    (((run_activeSize_eq_zero_iff j k xs result hr).mp hz).trans hjl)

theorem run_activeSize_absorbed (j k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) (hj : xs.length ≤ j) :
    activeSize j result.2.1 = 0 :=
  activeSize_eq_zero_of_length_le j result.2.1 ((run_active_calls_le k xs result hr).trans hj)

theorem run_residualWork_absorbed (w k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) (hw : xs.length ≤ w) :
    residualWork w result.2.1 = 0 :=
  residualWork_eq_zero_of_length_le w result.2.1 ((run_active_calls_le k xs result hr).trans hw)

theorem run_prefix_scan_le (w k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) : scanVolume (result.2.1.take w) ≤ w * xs.length :=
  scanVolume_take_le w xs.length result.2.1
    (fun entry he => (run_trace_entries k xs result hr entry he).2.2)

/-- The non-strict scan tail forces at least four initial lengths of work
to remain after the first `w` actual invocations. -/
theorem run_tail_residual (w k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support)
    (ht : (4 + w) * xs.length ≤ scanVolume result.2.1) :
    4 * xs.length ≤ residualWork w result.2.1 := by
  have hp := run_prefix_scan_le w k xs result hr
  have hd := scanVolume_take_add_residualWork w result.2.1
  rw [Nat.add_mul] at ht
  omega

def sizeExpectation (j k : Nat) (xs : List α) : ℝ≥0∞ :=
  workExpectation k xs (fun result => (activeSize j result.2.1 : ℝ≥0∞))

def residualExpectation (w k : Nat) (xs : List α) : ℝ≥0∞ :=
  workExpectation k xs (fun result => (residualWork w result.2.1 : ℝ≥0∞))

@[simp] theorem sizeExpectation_nil (j k : Nat) : sizeExpectation j k ([] : List α) = 0 := by
  rw [sizeExpectation, workExpectation_nil, activeSize_nil, Nat.cast_zero]

@[simp] theorem residualExpectation_nil (w k : Nat) :
    residualExpectation w k ([] : List α) = 0 := by
  rw [residualExpectation, workExpectation_nil, residualWork_nil, Nat.cast_zero]

@[simp] theorem sizeExpectation_zero (k : Nat) (xs : List α) :
    sizeExpectation 0 k xs = (xs.length : ℝ≥0∞) := by
  unfold sizeExpectation
  calc
    _ = workExpectation k xs (fun _ => (xs.length : ℝ≥0∞)) := by
      apply le_antisymm
      · apply workExpectation_mono
        intro result hr
        rw [run_activeSize_zero k xs result hr]
      · apply workExpectation_mono
        intro result hr
        rw [run_activeSize_zero k xs result hr]
    _ = _ := workExpectation_const k xs _

@[simp] theorem residualExpectation_zero (k : Nat) (xs : List α) :
    residualExpectation 0 k xs = scanExpectation k xs :=
  (scanExpectation_eq_workExpectation k xs).symm

/-- Exact time-shift equation from the fresh uniform current-occurrence
draw and the actual selected child. The equal branch is already absorbed. -/
theorem sizeExpectation_succ_cons (time k : Nat) (head : α) (tail : List α) :
    sizeExpectation (time + 1) k (head :: tail) =
      ∑ i : Fin (tail.length + 1), RandomQuickSort.uniformIndex tail.length i *
        match (stepRun k (head :: tail) i).1 with
        | Sum.inl (j, ys) => sizeExpectation time j ys
        | Sum.inr _ => 0 := by
  rw [sizeExpectation, workExpectation_cons]
  simp only [RandomQuickSort.uniformIndex_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun e : ℝ≥0∞ => (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) * e)
  cases (stepRun k (head :: tail) i).1 with
  | inl state => rcases state with ⟨j, ys⟩; rfl
  | inr _p => exact congrArg (fun n : Nat => (n : ℝ≥0∞)) (activeSize_nil time)

theorem residualExpectation_succ_cons (w k : Nat) (head : α) (tail : List α) :
    residualExpectation (w + 1) k (head :: tail) =
      ∑ i : Fin (tail.length + 1), RandomQuickSort.uniformIndex tail.length i *
        match (stepRun k (head :: tail) i).1 with
        | Sum.inl (j, ys) => residualExpectation w j ys
        | Sum.inr _ => 0 := by
  rw [residualExpectation, workExpectation_cons]
  simp only [RandomQuickSort.uniformIndex_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun e : ℝ≥0∞ => (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) * e)
  cases (stepRun k (head :: tail) i).1 with
  | inl state => rcases state with ⟨j, ys⟩; rfl
  | inr _p => exact congrArg (fun n : Nat => (n : ℝ≥0∞)) (residualWork_nil w)

/-- Conditional drift iterated on the actual trace; successive sizes are
not assumed independent. -/
theorem sizeExpectation_geometric_le (time k : Nat) (xs : List α) :
    sizeExpectation time k xs ≤ (3 / 4 : ℝ≥0∞) ^ time * xs.length := by
  induction time generalizing k xs with
  | zero => simp
  | succ time ih =>
      cases xs with
      | nil => simp
      | cons head tail =>
          rw [sizeExpectation_succ_cons]
          calc
            _ ≤ ∑ i : Fin (tail.length + 1),
                RandomQuickSort.uniformIndex tail.length i *
                  ((3 / 4 : ℝ≥0∞) ^ time * (nextSize k (head :: tail) i : ℝ≥0∞)) := by
              apply Finset.sum_le_sum
              intro i _
              apply mul_le_mul_right
              cases hstep : (stepRun k (head :: tail) i).1 with
              | inl state =>
                  rcases state with ⟨j, ys⟩
                  simpa only [nextSize, hstep] using ih j ys
              | inr _p => simp [nextSize, hstep]
            _ = (3 / 4 : ℝ≥0∞) ^ time *
                (∑ i : Fin (tail.length + 1), RandomQuickSort.uniformIndex tail.length i *
                  (nextSize k (head :: tail) i : ℝ≥0∞)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ac_rfl
            _ ≤ (3 / 4 : ℝ≥0∞) ^ time * ((3 / 4 : ℝ≥0∞) * (tail.length + 1 : Nat)) :=
              mul_le_mul_right (nextSize_drift k head tail) _
            _ = _ := by rw [pow_succ, List.length_cons]; ac_rfl

/-- Residual induction strips an actual trace entry at each step. Its base
is the checked four-times-length bound for the same execution. -/
theorem residualExpectation_geometric_le (w k : Nat) (xs : List α) :
    residualExpectation w k xs ≤ 4 * (3 / 4 : ℝ≥0∞) ^ w * xs.length := by
  induction w generalizing k xs with
  | zero => simpa only [residualExpectation_zero, pow_zero, mul_one] using
      scanExpectation_linear_le k xs
  | succ w ih =>
      cases xs with
      | nil => simp
      | cons head tail =>
          rw [residualExpectation_succ_cons]
          calc
            _ ≤ ∑ i : Fin (tail.length + 1),
                RandomQuickSort.uniformIndex tail.length i *
                  (4 * (3 / 4 : ℝ≥0∞) ^ w * (nextSize k (head :: tail) i : ℝ≥0∞)) := by
              apply Finset.sum_le_sum
              intro i _
              apply mul_le_mul_right
              cases hstep : (stepRun k (head :: tail) i).1 with
              | inl state =>
                  rcases state with ⟨j, ys⟩
                  simpa only [nextSize, hstep] using ih j ys
              | inr _p => simp [nextSize, hstep]
            _ = (4 * (3 / 4 : ℝ≥0∞) ^ w) *
                (∑ i : Fin (tail.length + 1), RandomQuickSort.uniformIndex tail.length i *
                  (nextSize k (head :: tail) i : ℝ≥0∞)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ac_rfl
            _ ≤ (4 * (3 / 4 : ℝ≥0∞) ^ w) * ((3 / 4 : ℝ≥0∞) * (tail.length + 1 : Nat)) :=
              mul_le_mul_right (nextSize_drift k head tail) _
            _ = _ := by rw [pow_succ, List.length_cons]; ac_rfl

theorem sizeExpectation_absorbed (j k : Nat) (xs : List α) (hj : xs.length ≤ j) :
    sizeExpectation j k xs = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ workExpectation k xs (fun _ => 0) := by
      apply workExpectation_mono
      intro result hr
      rw [run_activeSize_absorbed j k xs result hr hj, Nat.cast_zero]
    _ = _ := workExpectation_const k xs 0

theorem residualExpectation_absorbed (w k : Nat) (xs : List α) (hw : xs.length ≤ w) :
    residualExpectation w k xs = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ workExpectation k xs (fun _ => 0) := by
      apply workExpectation_mono
      intro result hr
      rw [run_residualWork_absorbed w k xs result hr hw, Nat.cast_zero]
    _ = _ := workExpectation_const k xs 0

theorem residualExpectation_le_scanExpectation (w k : Nat) (xs : List α) :
    residualExpectation w k xs ≤ scanExpectation k xs := by
  rw [scanExpectation_eq_workExpectation]
  apply workExpectation_mono
  intro result _hr
  exact_mod_cast residualWork_le w result.2.1

theorem residualExpectation_ne_top (w k : Nat) (xs : List α) :
    residualExpectation w k xs ≠ ∞ :=
  ne_top_of_le_ne_top (scanExpectation_ne_top k xs)
    (residualExpectation_le_scanExpectation w k xs)

/-- The Nat marginal of the actual remaining-work observation. -/
def residualLaw (w k : Nat) (xs : List α) : PMF Nat :=
  PMF.map (fun result => residualWork w result.2.1) (run k xs)

theorem residualLaw_support (w k : Nat) (xs : List α) :
    (residualLaw w k xs).support ⊆ Set.Iic (xs.length * (xs.length + 1) / 2) := by
  intro n hn
  obtain ⟨result, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
  rw [← he]
  exact (residualWork_le w result.2.1).trans (run_scanVolume_le k xs result hr)

theorem residualLaw_support_finite (w k : Nat) (xs : List α) :
    (residualLaw w k xs).support.Finite :=
  (Set.finite_Iic _).subset (residualLaw_support w k xs)

theorem residualLaw_lintegral (w k : Nat) (xs : List α) :
    (∫⁻ r : Nat, (r : ℝ≥0∞) ∂(residualLaw w k xs).toMeasure) = residualExpectation w k xs :=
  nat_map_lintegral (run k xs) (fun result => residualWork w result.2.1)

/-- Integrability follows from the actual finite scan bound; it is not an
assumption supplied to the tail theorem. -/
theorem residualLaw_integrable (w k : Nat) (xs : List α) :
    Integrable (fun r : Nat => (r : ℝ)) (residualLaw w k xs).toMeasure := by
  have hf : (∫⁻ r : Nat, (r : ℝ≥0∞) ∂(residualLaw w k xs).toMeasure) ≠ ∞ := by
    rw [residualLaw_lintegral]
    exact residualExpectation_ne_top w k xs
  have h := integrable_toReal_of_lintegral_ne_top
    (measurable_of_countable (fun r : Nat => (r : ℝ≥0∞))).aemeasurable hf
  simpa only [ENNReal.toReal_natCast] using h

/-- Event inclusion is established on supported outcomes of the same run,
then transported to the two Nat marginals. -/
theorem scanLaw_tail_le_residualLaw (w k : Nat) (xs : List α) :
    (scanLaw k xs).toMeasure {s : Nat | (4 + w) * xs.length ≤ s} ≤
      (residualLaw w k xs).toMeasure {r : Nat | 4 * xs.length ≤ r} := by
  simp only [PMF.toMeasure_apply_eq_toOuterMeasure, scanLaw, residualLaw,
    PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_mono
  intro result hr
  exact run_tail_residual w k xs result hr.2 hr.1

theorem residualLaw_markov (w k : Nat) (xs : List α) (threshold : Nat)
    (ht : 0 < threshold) :
    (residualLaw w k xs).toMeasure {r : Nat | threshold ≤ r} ≤
      residualExpectation w k xs / (threshold : ℝ≥0∞) := by
  have ht0 : (threshold : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hm := meas_ge_le_lintegral_div (μ := (residualLaw w k xs).toMeasure)
    (f := fun r : Nat => (r : ℝ≥0∞))
    (measurable_of_countable (fun r : Nat => (r : ℝ≥0∞))).aemeasurable
    ht0 (ENNReal.natCast_ne_top threshold)
  have hevent : {r : Nat | (threshold : ℝ≥0∞) ≤ (r : ℝ≥0∞)} =
      {r : Nat | threshold ≤ r} := by
    ext r
    simp only [Set.mem_ofPred_eq, Nat.cast_le]
  rw [hevent, residualLaw_lintegral] at hm
  exact hm

/-- The exact non-strict natural-excess tail for the actual selected-child
scan volume. Positive length is essential; no distinctness or input distribution
assumption is used. The statement also covers the worker's invalid-rank extension. -/
theorem scanLaw_tail (w k : Nat) (xs : List α) (hn : 0 < xs.length) :
    (scanLaw k xs).toMeasure {s : Nat | (4 + w) * xs.length ≤ s} ≤
      (3 / 4 : ℝ≥0∞) ^ w := by
  have hpos : 0 < 4 * xs.length := by omega
  have hzero : ((4 * xs.length : Nat) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  calc
    _ ≤ (residualLaw w k xs).toMeasure {r : Nat | 4 * xs.length ≤ r} :=
      scanLaw_tail_le_residualLaw w k xs
    _ ≤ residualExpectation w k xs / ((4 * xs.length : Nat) : ℝ≥0∞) :=
      residualLaw_markov w k xs (4 * xs.length) hpos
    _ ≤ _ := by
      apply (ENNReal.div_le_iff hzero (ENNReal.natCast_ne_top _)).2
      calc
        _ ≤ 4 * (3 / 4 : ℝ≥0∞) ^ w * xs.length := residualExpectation_geometric_le w k xs
        _ = _ := by
          rw [Nat.cast_mul, Nat.cast_ofNat]
          exact
            (mul_assoc (4 : ℝ≥0∞) ((3 / 4 : ℝ≥0∞) ^ w)
              (xs.length : ℝ≥0∞)).trans
              (mul_left_comm (4 : ℝ≥0∞) ((3 / 4 : ℝ≥0∞) ^ w)
                (xs.length : ℝ≥0∞))

theorem sourceLaw_tail_le_scanLaw (w k : Nat) (xs : List α) :
    (sourceLaw k xs).toMeasure {t : Nat | 9 * ((4 + w) * xs.length) + 2 ≤ t} ≤
      (scanLaw k xs).toMeasure {s : Nat | (4 + w) * xs.length ≤ s} := by
  simp only [PMF.toMeasure_apply_eq_toOuterMeasure, sourceLaw, scanLaw,
    PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_mono
  intro result hr
  have hc := (run_source_bridge k xs result hr.2).2
  have ht : 9 * ((4 + w) * xs.length) + 2 ≤ result.2.2 := hr.1
  change (4 + w) * xs.length ≤ scanVolume result.2.1
  omega

/-- Exact tail transported through the checked tariff on the same execution. -/
theorem sourceLaw_tail (w k : Nat) (xs : List α) (hn : 0 < xs.length) :
    (sourceLaw k xs).toMeasure {t : Nat | 9 * ((4 + w) * xs.length) + 2 ≤ t} ≤
      (3 / 4 : ℝ≥0∞) ^ w :=
  (sourceLaw_tail_le_scanLaw w k xs).trans (scanLaw_tail w k xs hn)

@[simp] theorem scanLaw_nil (k : Nat) : scanLaw k ([] : List α) = PMF.pure 0 := by
  rw [scanLaw, run_nil, PMF.pure_map]
  rfl

/-- At empty input the non-strict proportional threshold is zero, so its
event has probability one at every excess parameter. -/
theorem scanLaw_empty_tail (w k : Nat) :
    (scanLaw k ([] : List α)).toMeasure {s : Nat | (4 + w) * ([] : List α).length ≤ s} = 1 := by
  have hevent : {s : Nat | (4 + w) * ([] : List α).length ≤ s} = Set.univ := by
    ext s
    simp
  rw [hevent]
  exact measure_univ

/-- Removing the positive-length premise would make the proposed tail
inequality false already at natural excess one. -/
theorem scanLaw_empty_tail_bound_fails (k : Nat) :
    ¬ (scanLaw k ([] : List α)).toMeasure {s : Nat | (4 + 1) * ([] : List α).length ≤ s} ≤
      (3 / 4 : ℝ≥0∞) ^ (1 : Nat) := by
  rw [scanLaw_empty_tail, pow_one]
  apply not_le_of_gt
  apply (ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl ENNReal.ofNat_ne_top)).2
  rw [one_mul]
  exact_mod_cast (show (3 : Nat) < 4 by decide)

end Ordered
end
end Resources.RandomSelection
