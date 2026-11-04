import Applications.Resources.RandomSelectionTail

/-! Exact all-equal executions of the existing fresh-occurrence selector.

Every valid rank in a nonempty equal block returns after its first partition.
The occurrence draw is still uniform: its recorded index and measured lookup
cost distinguish the outcomes even though the returned values coincide.
Invalid worker ranks take the actual empty continuation and pay its two calls.
These linear examples delimit the quadratic worst-case quantifier; they do not
replace the distinct-input endpoint-path obligation. Uniform sampling remains
the declared abstract choice, with no random-bit or elapsed-time claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomSelection
open Applications.Selection MeasureTheory
open scoped ENNReal
universe u v
variable {α : Type u}

noncomputable section

private theorem uniformIndex_map_atom {β : Type v} (n : Nat)
    (f : Fin (n + 1) → β) (hf : Function.Injective f) (i : Fin (n + 1)) :
    (PMF.map f (RandomQuickSort.uniformIndex n)) (f i) =
      (((n + 1 : Nat) : ℝ≥0∞)⁻¹) := by
  classical
  simpa only [PMF.map_apply, hf.eq_iff, tsum_ite_eq] using
    RandomQuickSort.uniformIndex_apply n i

section Ordered
variable [LinearOrder α]

/-- Every measured occurrence lookup gives the same pivot, the strict buckets
are empty, and the equal bucket is the complete input. -/
theorem stepRun_all_equal (k : Nat) (xs : List α) (x : α)
    (hall : ∀ a ∈ xs, a = x) (i : Fin xs.length) :
    stepRun k xs i =
      if k < xs.length then
        (Sum.inr x, 3 * xs.length + i.val + 6)
      else (Sum.inl (k - xs.length, []), 3 * xs.length + i.val + 6) := by
  have hv : xs[i.val]'i.isLt = x := hall _ (List.getElem_mem i.isLt)
  have hp : partition3 x xs = ([], xs, []) := by
    have hxs := List.eq_replicate_of_mem hall
    calc
      _ = partition3 x (List.replicate xs.length x) := congrArg (partition3 x) hxs
      _ = ([], List.replicate xs.length x, []) := by
        simp [partition3_eq_filters, List.filter_replicate]
      _ = _ := congrArg (fun ys : List α => (([] : List α), ys, ([] : List α))) hxs.symm
  rw [stepRun_eq]
  simp only [hv, hp, List.length_nil, Nat.not_lt_zero, Nat.zero_add,
    Nat.sub_zero, ↓reduceIte]
  split_ifs <;> apply Prod.ext <;> first | rfl | omega

/-- The full choice law retains each occurrence and the actual source tariff.
Its invalid branch includes the final empty call. -/
theorem run_all_equal_cons (k : Nat) (x : α) (tail : List α)
    (hall : ∀ a ∈ tail, a = x) :
    run k (x :: tail) =
      PMF.map (fun i : Fin (tail.length + 1) =>
        if k < tail.length + 1 then
          (some x, ([(tail.length + 1, i.val)], 3 * (tail.length + 1) + i.val + 6))
        else (none, ([(tail.length + 1, i.val)], 3 * (tail.length + 1) + i.val + 8)))
        (RandomQuickSort.uniformIndex tail.length) := by
  rw [run_cons, PMF.map]
  apply congrArg (PMF.bind _)
  funext i
  have hall' : ∀ a ∈ x :: tail, a = x := by
    intro a ha
    rcases List.mem_cons.mp ha with ha | ha
    · exact ha
    · exact hall a ha
  have hs := stepRun_all_equal k (x :: tail) x hall' i
  by_cases hk : k < tail.length + 1
  · simp only [List.length_cons, hk, ↓reduceIte] at hs
    simp only [hs, List.length_cons, hk, ↓reduceIte]
  · simp only [List.length_cons, hk, ↓reduceIte] at hs
    simp [hs, hk, PMF.pure_map, prepend, Nat.add_assoc]

theorem run_replicate_valid (n k : Nat) (x : α) (hk : k < n + 1) :
    run k (List.replicate (n + 1) x) =
      PMF.map (fun i : Fin (n + 1) =>
        (some x, ([(n + 1, i.val)], 3 * (n + 1) + i.val + 6)))
        (RandomQuickSort.uniformIndex n) := by
  rw [List.replicate_succ, run_all_equal_cons k x (List.replicate n x)
    (fun _ h => List.eq_of_mem_replicate h)]
  simp only [List.length_replicate, hk, ↓reduceIte]

theorem run_replicate_invalid (n k : Nat) (x : α) (hk : n + 1 ≤ k) :
    run k (List.replicate (n + 1) x) =
      PMF.map (fun i : Fin (n + 1) =>
        (none, ([(n + 1, i.val)], 3 * (n + 1) + i.val + 8)))
        (RandomQuickSort.uniformIndex n) := by
  rw [List.replicate_succ, run_all_equal_cons k x (List.replicate n x)
    (fun _ h => List.eq_of_mem_replicate h)]
  simp only [List.length_replicate, Nat.not_lt.mpr hk, ↓reduceIte]

theorem run_replicate_valid_support (n k : Nat) (x : α) (hk : k < n + 1)
    (result : Outcome α) :
    result ∈ (run k (List.replicate (n + 1) x)).support ↔
      ∃ i : Fin (n + 1), result =
        (some x, ([(n + 1, i.val)], 3 * (n + 1) + i.val + 6)) := by
  rw [run_replicate_valid n k x hk, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, RandomQuickSort.mem_support_uniformIndex n i, hi.symm⟩

theorem run_replicate_invalid_support (n k : Nat) (x : α) (hk : n + 1 ≤ k)
    (result : Outcome α) :
    result ∈ (run k (List.replicate (n + 1) x)).support ↔
      ∃ i : Fin (n + 1), result =
        (none, ([(n + 1, i.val)], 3 * (n + 1) + i.val + 8)) := by
  rw [run_replicate_invalid n k x hk, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, RandomQuickSort.mem_support_uniformIndex n i, hi.symm⟩

/-- Equal payload values do not merge these outcomes: their recorded occurrence
indices, and therefore their actual lookup costs, are distinct. -/
theorem run_replicate_valid_atom (n k : Nat) (x : α) (hk : k < n + 1)
    (i : Fin (n + 1)) :
    run k (List.replicate (n + 1) x)
      (some x, ([(n + 1, i.val)], 3 * (n + 1) + i.val + 6)) =
      (((n + 1 : Nat) : ℝ≥0∞)⁻¹) := by
  rw [run_replicate_valid n k x hk]
  refine uniformIndex_map_atom n _ ?_ i
  intro j l h
  apply Fin.ext
  have hc := congrArg (fun result : Outcome α => result.2.2) h
  dsimp only at hc
  omega

theorem run_replicate_invalid_atom (n k : Nat) (x : α) (hk : n + 1 ≤ k)
    (i : Fin (n + 1)) :
    run k (List.replicate (n + 1) x)
      (none, ([(n + 1, i.val)], 3 * (n + 1) + i.val + 8)) =
      (((n + 1 : Nat) : ℝ≥0∞)⁻¹) := by
  rw [run_replicate_invalid n k x hk]
  refine uniformIndex_map_atom n _ ?_ i
  intro j l h
  apply Fin.ext
  have hc := congrArg (fun result : Outcome α => result.2.2) h
  dsimp only at hc
  omega

/-- Scan volume is the input length for every worker rank, including the
empty and invalid extensions. Only the separate source cost changes. -/
theorem scanLaw_replicate (n k : Nat) (x : α) :
    scanLaw k (List.replicate n x) = PMF.pure n := by
  cases n with
  | zero => simp
  | succ n =>
      by_cases hk : k < n + 1
      · rw [scanLaw, run_replicate_valid n k x hk, PMF.map_comp]
        change PMF.map (Function.const (Fin (n + 1)) (n + 1))
          (RandomQuickSort.uniformIndex n) = PMF.pure (n + 1)
        exact PMF.map_const _ _
      · rw [scanLaw, run_replicate_invalid n k x (Nat.le_of_not_gt hk), PMF.map_comp]
        change PMF.map (Function.const (Fin (n + 1)) (n + 1))
          (RandomQuickSort.uniformIndex n) = PMF.pure (n + 1)
        exact PMF.map_const _ _

theorem sourceLaw_replicate_valid (n k : Nat) (x : α) (hk : k < n + 1) :
    sourceLaw k (List.replicate (n + 1) x) =
      PMF.map (fun i : Fin (n + 1) => 3 * (n + 1) + i.val + 6)
        (RandomQuickSort.uniformIndex n) := by
  rw [sourceLaw, run_replicate_valid n k x hk, PMF.map_comp]
  rfl

theorem sourceLaw_replicate_invalid (n k : Nat) (x : α) (hk : n + 1 ≤ k) :
    sourceLaw k (List.replicate (n + 1) x) =
      PMF.map (fun i : Fin (n + 1) => 3 * (n + 1) + i.val + 8)
        (RandomQuickSort.uniformIndex n) := by
  rw [sourceLaw, run_replicate_invalid n k x hk, PMF.map_comp]
  rfl

theorem run_replicate_scan (n k : Nat) (x : α) (result : Outcome α)
    (hr : result ∈ (run k (List.replicate n x)).support) :
    scanVolume result.2.1 = n := by
  have hs : scanVolume result.2.1 ∈ (scanLaw k (List.replicate n x)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨result, hr, rfl⟩
  rw [scanLaw_replicate] at hs
  exact (PMF.mem_support_pure_iff _ _).mp hs

theorem scanExpectation_replicate (n k : Nat) (x : α) :
    scanExpectation k (List.replicate n x) = (n : ℝ≥0∞) := by
  rw [scanExpectation, scanLaw_replicate, PMF.toMeasure_pure]
  simp

theorem scanMean_replicate (n k : Nat) (x : α) :
    scanMean k (List.replicate n x) = (n : ℝ) := by
  rw [scanMean_eq_toReal, scanExpectation_replicate, ENNReal.toReal_natCast]

/-- A memberwise all-equal premise suffices; the caller need not present its
input as a replicate expression. Empty inputs and all ranks are included. -/
theorem scanLaw_all_equal (k : Nat) (xs : List α) (x : α)
    (hall : ∀ a ∈ xs, a = x) : scanLaw k xs = PMF.pure xs.length := by
  calc
    _ = scanLaw k (List.replicate xs.length x) :=
      congrArg (fun ys : List α => scanLaw k ys) (List.eq_replicate_of_mem hall)
    _ = _ := scanLaw_replicate xs.length k x

theorem run_all_equal (k : Nat) (xs : List α) (x : α)
    (hall : ∀ a ∈ xs, a = x) (hk : k < xs.length) (result : Outcome α)
    (hr : result ∈ (run k xs).support) :
    ∃ i : Nat, i < xs.length ∧
      result = (some x, ([(xs.length, i)], 3 * xs.length + i + 6)) := by
  cases hlen : xs.length with
  | zero => omega
  | succ n =>
      have hxs : xs = List.replicate (n + 1) x := by
        simpa only [hlen] using List.eq_replicate_of_mem hall
      have hk' : k < n + 1 := by omega
      rw [hxs] at hr
      obtain ⟨i, hi⟩ := (run_replicate_valid_support n k x hk' result).mp hr
      exact ⟨i.val, i.isLt, hi⟩

/-- Every valid all-equal outcome has one active invocation and linear actual
source cost. This is uniform in the input length and requested rank. -/
theorem run_all_equal_summary (k : Nat) (xs : List α) (x : α)
    (hall : ∀ a ∈ xs, a = x) (hk : k < xs.length) (result : Outcome α)
    (hr : result ∈ (run k xs).support) :
    result.1 = some x ∧ result.2.1.length = 1 ∧ scanVolume result.2.1 = xs.length ∧
      3 * xs.length + 6 ≤ result.2.2 ∧ result.2.2 ≤ 4 * xs.length + 5 := by
  obtain ⟨i, hi, he⟩ := run_all_equal k xs x hall hk result hr
  subst result
  exact ⟨rfl, rfl, rfl, by omega, by omega⟩

theorem run_all_equal_absorbed (time k : Nat) (xs : List α) (x : α)
    (hall : ∀ a ∈ xs, a = x) (hk : k < xs.length) (result : Outcome α)
    (hr : result ∈ (run k xs).support) :
    activeSize (time + 1) result.2.1 = 0 ∧ residualWork (time + 1) result.2.1 = 0 := by
  obtain ⟨i, _, he⟩ := run_all_equal k xs x hall hk result hr
  rw [he]
  simp only [activeSize_succ_cons, activeSize_nil, residualWork_succ_cons, residualWork_nil,
    and_self]

/-- The quadratic bound is not attained separately by every duplicate pattern.
This family has exact linear scan volume at every size, for every worker rank. -/
theorem run_replicate_scan_lt_quadratic (n k : Nat) (x : α) (hn : 2 ≤ n)
    (result : Outcome α) (hr : result ∈ (run k (List.replicate n x)).support) :
    scanVolume result.2.1 < n * (n + 1) / 2 := by
  rw [run_replicate_scan n k x result hr]
  have hm : 2 * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right (n + 1) hn
  omega

end Ordered
end
end Resources.RandomSelection
