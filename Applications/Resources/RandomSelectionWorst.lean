import Applications.Resources.RandomSelectionTrace
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.List.Range

/-! The specified endpoint path in the actual randomized selection execution.

For every distinct input and every valid worker rank, choose a minimum while
the rank is positive and a maximum after it reaches zero. The actual chosen
child removes one occurrence and retains the target until the singleton. Its
complete outcome and its projected trace both have exact probability `1/n!`.
Its scan volume is exactly `n*(n+1)/2`; its source calls retain their separate
observation and the established lower and upper transport bounds.

`EndpointTrace` records only the policy and actual transitions. In particular,
it assumes no probability or resource law. Mixed duplicates can satisfy this
structural predicate without the distinct-input factorial or triangular laws.
The natural-range family keeps every valid rank and has unbounded input sizes.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomSelection
open Applications.Selection
open scoped ENNReal
universe u
variable {α : Type u}

noncomputable section

private theorem inverse_factorial_step (m : Nat) :
    (((m + 1 : Nat) : ℝ≥0∞)⁻¹) * ((m.factorial : ℝ≥0∞)⁻¹) =
      (((m + 1).factorial : ℝ≥0∞)⁻¹) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top m.factorial))
    (Or.inl (ENNReal.natCast_ne_top (m + 1)))).symm

section Ordered
variable [LinearOrder α]

/-- A purely structural path of the specified endpoint policy. Every recorded
index is a current occurrence, every size is the actual current length, and
every continuation is the actual selected child. The path ends at a singleton.
No distinctness, probability, target equation or resource bound is a field. -/
def EndpointTrace : Nat → List α → Trace → Prop
  | _, _, [] => False
  | k, xs, (n, i) :: rest =>
      ∃ hi : i < xs.length,
        n = xs.length ∧ EndpointPivot k xs ⟨i, hi⟩ ∧
        match (stepRun k xs ⟨i, hi⟩).1 with
        | Sum.inl (j, ys) => EndpointTrace j ys rest
        | Sum.inr _ => xs.length = 1 ∧ rest = []

theorem endpointTrace_nil (k : Nat) (xs : List α) :
    ¬ EndpointTrace k xs [] := by
  simp [EndpointTrace]

theorem endpointTrace_empty_input (k : Nat) (trace : Trace) :
    ¬ EndpointTrace k ([] : List α) trace := by
  cases trace with
  | nil => exact endpointTrace_nil k []
  | cons entry rest =>
      rcases entry with ⟨n, i⟩
      intro ht
      obtain ⟨hi, _, _, _⟩ := ht
      simp at hi

theorem endpointTrace_singleton (x : α) : EndpointTrace 0 [x] [(1, 0)] := by
  have hs : (stepRun 0 [x] ⟨0, by simp⟩).1 = Sum.inr x := by
    simp [stepRun_eq, partition3_eq_filters]
  rw [EndpointTrace]
  refine ⟨by simp, rfl, ?_, ?_⟩
  · simp [EndpointPivot]
  · rw [hs]
    exact ⟨rfl, rfl⟩

/-- A checked policy occurrence extends a structural child path using the
actual selected state. This lemma is also meaningful for mixed duplicates. -/
theorem endpointTrace_child (k : Nat) (xs : List α) (i : Fin xs.length)
    (j : Nat) (ys : List α) (trace : Trace)
    (hp : EndpointPivot k xs i) (hs : (stepRun k xs i).1 = Sum.inl (j, ys))
    (ht : EndpointTrace j ys trace) :
    EndpointTrace k xs ((xs.length, i.val) :: trace) := by
  rw [EndpointTrace]
  refine ⟨i.isLt, rfl, hp, ?_⟩
  rw [hs]
  exact ht

/-- Successful target preservation is derived from the actual step semantics,
not included as an assumption in the structural path. -/
theorem endpointTrace_target (k : Nat) (xs : List α) (trace : Trace)
    (ht : EndpointTrace k xs trace) : ∃ a, (ordered xs)[k]? = some a := by
  induction trace generalizing k xs with
  | nil => exact False.elim ((endpointTrace_nil k xs) ht)
  | cons entry rest ih =>
      rcases entry with ⟨n, i⟩
      obtain ⟨hi, _, _, ht⟩ := ht
      have hv := stepRun_semantics k xs ⟨i, hi⟩
      cases hs : (stepRun k xs ⟨i, hi⟩).1 with
      | inl state =>
          rcases state with ⟨j, ys⟩
          rw [hs] at ht hv
          obtain ⟨a, ha⟩ := ih j ys ht
          exact ⟨a, hv.symm.trans ha⟩
      | inr p =>
          rw [hs] at hv
          exact ⟨p, hv.symm⟩

/-- Empty and invalid worker requests remain total actual executions, but
cannot have this singleton-ending successful endpoint path. -/
theorem endpointTrace_valid (k : Nat) (xs : List α) (trace : Trace)
    (ht : EndpointTrace k xs trace) : k < xs.length := by
  obtain ⟨a, ha⟩ := endpointTrace_target k xs trace ht
  by_contra hk
  have hlen : (ordered xs).length ≤ k := by
    rw [(ordered_perm xs).length_eq]
    omega
  have hn : (ordered xs)[k]? = none := List.getElem?_eq_none_iff.mpr hlen
  rw [ha] at hn
  cases hn

private theorem endpoint_outcome (k : Nat) (xs : List α)
    (hxs : xs.Nodup) (hk : k < xs.length) :
    ∃ r : Outcome α,
      EndpointTrace k xs r.2.1 ∧
      run k xs r = ((xs.length.factorial : ℝ≥0∞)⁻¹) ∧
      r.2.1.length = xs.length ∧
      2 * scanVolume r.2.1 = xs.length * (xs.length + 1) := by
  match xs with
  | [] => simp at hk
  | [head] =>
      have hk0 : k = 0 := by
        simp only [List.length_singleton] at hk
        omega
      subst k
      refine ⟨(some head, ([(1, 0)], 9)), endpointTrace_singleton head, ?_, rfl, ?_⟩
      · simpa using run_singleton_atom head
      · rfl
  | head :: second :: rest =>
      obtain ⟨i, ys, hp, hs, hy, hlen, hvalid, _⟩ :=
        exists_endpoint_child k (head :: second :: rest) hxs hk (by simp)
      obtain ⟨child, htrace, hmass, hcount, hscan⟩ :=
        endpoint_outcome (k - 1) ys hy hvalid
      refine ⟨prepend (head :: second :: rest).length i.val
        (stepRun k (head :: second :: rest) i).2 child, ?_, ?_, ?_, ?_⟩
      · exact endpointTrace_child k (head :: second :: rest) i
          (k - 1) ys child.2.1 hp hs htrace
      · rw [run_child_atom k head (second :: rest) i (k - 1) ys hs child, hmass]
        have hylen : ys.length = (second :: rest).length := by
          simp only [List.length_cons] at hlen ⊢
          omega
        rw [hylen]
        exact inverse_factorial_step (second :: rest).length
      · change child.2.1.length + 1 = (head :: second :: rest).length
        rw [hcount]
        exact hlen
      · change 2 * ((head :: second :: rest).length + scanVolume child.2.1) =
          (head :: second :: rest).length * ((head :: second :: rest).length + 1)
        rw [← hlen]
        nlinarith [hscan]
termination_by xs.length
decreasing_by
  exact (stepRun_child k (head :: second :: rest) i (k - 1) ys hs).1

/-- Every arbitrary distinct input and every valid target rank has the actual
specified endpoint path. Positivity of its derived factorial atom gives support;
supported-trace uniqueness then gives the exact projected trace probability.
The scan volume is triangular, while the source observation has explicit bounds. -/
theorem exists_endpoint_worst (k : Nat) (xs : List α)
    (hxs : xs.Nodup) (hk : k < xs.length) :
    ∃ r : Outcome α,
      EndpointTrace k xs r.2.1 ∧
      r ∈ (run k xs).support ∧
      run k xs r = ((xs.length.factorial : ℝ≥0∞)⁻¹) ∧
      traceLaw k xs r.2.1 = ((xs.length.factorial : ℝ≥0∞)⁻¹) ∧
      r.2.1.length = xs.length ∧
      2 * scanVolume r.2.1 = xs.length * (xs.length + 1) ∧
      scanVolume r.2.1 = xs.length * (xs.length + 1) / 2 ∧
      r.1 = (ordered xs)[k]? ∧
      xs.length * (xs.length + 1) / 2 ≤ r.2.2 ∧
      r.2.2 ≤ 9 * (xs.length * (xs.length + 1) / 2) + 2 := by
  obtain ⟨r, ht, ha, hcount, hdouble⟩ := endpoint_outcome k xs hxs hk
  have hr : r ∈ (run k xs).support := by
    rw [PMF.mem_support_iff, ha]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have htrace := (traceLaw_atom k xs r hr).trans ha
  have hw : scanVolume r.2.1 = xs.length * (xs.length + 1) / 2 := by omega
  have hc := run_source_bridge k xs r hr
  rw [hw] at hc
  exact ⟨r, ht, hr, ha, htrace, hcount, hdouble, hw,
    run_value k xs r hr, hc.1, hc.2⟩

/-- Distinct natural ranges supply every positive size without an unboundedness
assumption on arbitrary payload types. Every valid rank is retained. The actual
source observation has quadratic lower and upper bounds with explicit constants. -/
theorem range_endpoint_worst (n k : Nat) (hn : 0 < n) (hk : k < n) :
    ∃ r : Outcome Nat,
      EndpointTrace k (List.range n) r.2.1 ∧
      r ∈ (run k (List.range n)).support ∧
      run k (List.range n) r = ((n.factorial : ℝ≥0∞)⁻¹) ∧
      traceLaw k (List.range n) r.2.1 = ((n.factorial : ℝ≥0∞)⁻¹) ∧
      r.2.1.length = n ∧
      scanVolume r.2.1 = n * (n + 1) / 2 ∧
      n * (n + 1) / 2 ≤ r.2.2 ∧
      r.2.2 ≤ 9 * (n * (n + 1) / 2) + 2 ∧
      n * n ≤ 2 * r.2.2 ∧ r.2.2 ≤ 11 * (n * n) := by
  obtain ⟨r, ht, hr, ha, hm, hcount, hd, hw, _, hl, hu⟩ :=
    exists_endpoint_worst k (List.range n) List.nodup_range
      (by simpa only [List.length_range] using hk)
  simp only [List.length_range] at ha hm hcount hd hw hl hu
  have hc := run_source_bridge k (List.range n) r hr
  have hmul := Nat.le_mul_self n
  have hvolume : scanVolume r.2.1 ≤ n * n := by nlinarith [hd, hmul]
  have hpositive : 1 ≤ n * n := Nat.succ_le_of_lt (Nat.mul_pos hn hn)
  have hquadratic_lower : n * n ≤ 2 * r.2.2 := by nlinarith [hd, hc.1]
  have hquadratic_upper : r.2.2 ≤ 11 * (n * n) := by
    nlinarith [hc.2, hvolume, hpositive]
  exact ⟨r, ht, hr, ha, hm, hcount, hw, hl, hu, hquadratic_lower, hquadratic_upper⟩

/-- Unbounded actual source-cost witnesses, at every valid rank of each chosen
distinct range. The cost exceeds any given finite bound and remains quadratic
in the input size; no assigned abstract runtime or independence law is used. -/
theorem unbounded_endpoint_source_family (B : Nat) :
    ∃ n : Nat, B < n ∧ ∀ k : Nat, k < n →
      ∃ r : Outcome Nat,
        EndpointTrace k (List.range n) r.2.1 ∧
        r ∈ (run k (List.range n)).support ∧
        traceLaw k (List.range n) r.2.1 = ((n.factorial : ℝ≥0∞)⁻¹) ∧
        scanVolume r.2.1 = n * (n + 1) / 2 ∧
        B < r.2.2 ∧ n * n ≤ 2 * r.2.2 ∧ r.2.2 ≤ 11 * (n * n) := by
  refine ⟨B + 1, by omega, ?_⟩
  intro k hk
  obtain ⟨r, ht, hr, _, hm, _, hw, _, _, hl, hu⟩ :=
    range_endpoint_worst (B + 1) k (by omega) hk
  have hi := run_initial_scan_le k (List.range (B + 1)) r hr
  have hc := (run_source_bridge k (List.range (B + 1)) r hr).1
  simp only [List.length_range] at hi
  exact ⟨r, ht, hr, hm, hw, by omega, hl, hu⟩

end Ordered
end
end Resources.RandomSelection
