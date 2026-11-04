import Applications.Resources.HalvingSelection
import Applications.Resources.SelectionBounds

/-!
An actual linear-cost halving policy for FDSA p35.

The pivot constructor executes a measured length traversal to determine the
lower-occurrence median rank, then executes the proved measured deterministic
selector. Its wrapper entry is charged too. The outer policy executor retains
its own length observation, partition, bucket lengths and terminal lookup.
Those are separate source calls; this module does not assume a free median.

All selection ranks are zero-based. Optional failure covers empty and invalid
inputs; positive-size complexity claims require a valid rank and adequate
administrative fuel. Repeated values are permitted throughout.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.MedianPolicy
open Applications.Selection
universe u
variable {α : Type u} [LinearOrder α]

/-- Execute both the observation that selects the median rank and its actual
measured selection, with one entry for this pivot constructor. -/
def pivotRun (xs : List α) : Measured (Option α) Nat :=
  CallCount.tick (bind (SymmetricCosts.lengthRun xs)
    (fun n => Selection.selectRun ((n - 1) / 2) xs))

theorem pivotRun_value (xs : List α) :
    (pivotRun xs).1 = (ordered xs)[(xs.length - 1) / 2]? := by
  simp only [pivotRun, CallCount.tick_value, bind_value,
    SymmetricCosts.lengthRun_exact, Selection.selectRun_value]

/-- The extra n+2 comprises the actual index-length traversal and entry. -/
theorem pivotRun_cost (xs : List α) :
    (pivotRun xs).2 = xs.length + 2 +
      (Selection.selectRun ((xs.length - 1) / 2) xs).2 := by
  simp only [pivotRun, CallCount.tick_cost, bind, SymmetricCosts.lengthRun_exact]
  omega

theorem pivotRun_some_iff (xs : List α) (p : α) :
    (pivotRun xs).1 = some p ↔ RankedAt xs ((xs.length - 1) / 2) p := by
  rw [pivotRun_value, ← ranked_iff_index]

theorem pivotRun_none (xs : List α) : (pivotRun xs).1 = none ↔ xs = [] := by
  rw [pivotRun_value, List.getElem?_eq_none_iff, (ordered_perm xs).length_eq]
  constructor
  · intro h
    exact List.length_eq_zero_iff.mp (by omega)
  · intro h
    subst xs
    simp

theorem pivot_valid : PivotValid (fun xs : List α => (pivotRun xs).1) := by
  intro xs hx
  cases hp : (pivotRun xs).1 with
  | none => exact (hx ((pivotRun_none xs).mp hp)).elim
  | some p => exact ⟨p, hp, ((pivotRun_some_iff xs p).mp hp).mem⟩

/-- Duplicate-aware rank inequalities imply both strict sides halve. -/
theorem pivot_halving : HalvingSelection.HalvingPolicy (pivotRun (α := α)) := by
  intro xs p hp
  have hr := (pivotRun_some_iff xs p).mp hp
  have hc := hr.count_bounds
  have hl : (partition3 p xs).1.length ≤ (xs.length - 1) / 2 := by
    simpa only [partition3_eq_filters, List.countP_eq_length_filter] using hc.1
  have hu : (partition3 p xs).2.2.length < xs.length - (xs.length - 1) / 2 := by
    simpa only [partition3_eq_filters, List.countP_eq_length_filter] using hc.2
  constructor <;> omega

/-- Reduce a small concrete pivot through the public selector equation, without
unfolding its proof-carrying well-founded worker. This is the same execution. -/
theorem pivotRun_small (xs : List α) (hx : xs ≠ []) (hs : xs.length ≤ 20) :
    pivotRun xs =
      ((SelectionAuxiliary.slowSelectRun ((xs.length - 1) / 2) xs).1,
        2 * xs.length + 4 +
          (SelectionAuxiliary.slowSelectRun ((xs.length - 1) / 2) xs).2) := by
  have hn : 0 < xs.length := List.length_pos_iff.mpr hx
  have hk : (xs.length - 1) / 2 < xs.length := by omega
  simp only [pivotRun, CallCount.tick, bind, SymmetricCosts.lengthRun_exact,
    Selection.selectRun_small _ xs hk hs]
  congr 1
  omega

theorem pivotRun_singleton (x : α) : pivotRun [x] = (some x, 10) := by
  rw [pivotRun_small [x] (by simp) (by simp)]
  simp [SelectionAuxiliary.slowSelectRun, InsertionSort.sortRun,
    InsertionSort.insertRun, ListCalls.lookupRun, bind, CallCount.tick]

/-- One constant precedes the payload type and every intermediate input. -/
theorem pivotRun_exists_uniform_linear_bound :
    ∃ C : Nat, ∀ (β : Type u) [LinearOrder β] (xs : List β),
      0 < xs.length → (pivotRun xs).2 ≤ C * xs.length := by
  obtain ⟨C, bound⟩ := Selection.selectRun_exists_uniform_linear_bound
  refine ⟨C + 3, ?_⟩
  intro β inst xs hx
  have h := bound β xs ((xs.length - 1) / 2) hx
  rw [pivotRun_cost, Nat.add_mul]
  omega

/-- The existing measured policy executor, instantiated with an actual median. -/
def run (fuel k : Nat) (xs : List α) : SelectionPolicy.Observed α :=
  SelectionPolicy.runWith pivotRun fuel k xs

theorem run_value (fuel k : Nat) (xs : List α) (hf : xs.length ≤ fuel) :
    (run fuel k xs).1.1 = (ordered xs)[k]? :=
  SelectionPolicy.runWith_correct pivotRun pivot_valid fuel k xs hf

theorem run_some_iff (fuel k : Nat) (xs : List α) (hf : xs.length ≤ fuel) (p : α) :
    (run fuel k xs).1.1 = some p ↔ RankedAt xs k p := by
  rw [run_value fuel k xs hf, ← ranked_iff_index]

theorem run_none (fuel k : Nat) (xs : List α) (hf : xs.length ≤ fuel) :
    (run fuel k xs).1.1 = none ↔ xs.length ≤ k := by
  rw [run_value fuel k xs hf, List.getElem?_eq_none_iff, (ordered_perm xs).length_eq]

theorem run_trace (fuel k : Nat) (xs : List α) (hk : k < xs.length)
    (hf : xs.length ≤ fuel) : HalvingTrace.Halves xs.length (run fuel k xs).1.2 :=
  HalvingSelection.runWith_trace pivotRun pivot_valid pivot_halving fuel k xs hk hf

theorem run_scan_bounds (fuel k : Nat) (xs : List α) (hk : k < xs.length)
    (hf : xs.length ≤ fuel) :
    xs.length ≤ (run fuel k xs).1.2.sum ∧ (run fuel k xs).1.2.sum ≤ 2 * xs.length :=
  HalvingSelection.runWith_scan_bounds pivotRun pivot_valid pivot_halving fuel k xs hk hf

theorem run_edges_log (fuel k : Nat) (xs : List α) (hk : k < xs.length)
    (hf : xs.length ≤ fuel) : (run fuel k xs).1.2.length - 1 ≤ Nat.log 2 xs.length :=
  HalvingSelection.runWith_edges_log pivotRun pivot_valid pivot_halving fuel k xs hk hf

theorem run_edges_clog (fuel k : Nat) (xs : List α) (hk : k < xs.length)
    (hf : xs.length ≤ fuel) : (run fuel k xs).1.2.length - 1 ≤ Nat.clog 2 xs.length :=
  HalvingSelection.runWith_edges_clog pivotRun pivot_valid pivot_halving fuel k xs hk hf

theorem run_singleton_trace (fuel : Nat) (x : α) :
    (run (fuel + 1) 0 [x]).1.2 = [1] :=
  HalvingSelection.runWith_singleton_trace pivotRun pivot_valid pivot_halving fuel x

/-- Even the terminal singleton pays its actual median construction. -/
theorem run_singleton (fuel : Nat) (x : α) :
    run (fuel + 1) 0 [x] = ((some x, [1]), 19) := by
  have hp : (pivotRun [x]).1 = some x := by rw [pivotRun_singleton]
  rw [run, SelectionPolicy.runWith_step pivotRun fuel 0 [x] (by simp) x hp]
  simp [partition3_eq_filters, pivotRun_singleton]

/-- The coefficient is chosen before payloads, inputs, ranks and adequate fuel.
The lower and upper bounds concern actual source calls, including the pivot. -/
theorem run_exists_uniform_linear_bound :
    ∃ D : Nat, 0 < D ∧ ∀ (β : Type u) [LinearOrder β] (fuel k : Nat) (xs : List β),
      k < xs.length → xs.length ≤ fuel →
        xs.length ≤ (run fuel k xs).2 ∧ (run fuel k xs).2 ≤ D * xs.length := by
  obtain ⟨C, bound⟩ := pivotRun_exists_uniform_linear_bound
  refine ⟨2 * (C + 4) + 2 * (0 + 5), by omega, ?_⟩
  intro β inst fuel k xs hk hf
  apply HalvingSelection.runWith_linear_cost pivotRun pivot_valid pivot_halving C 0
  · intro ys hy
    simpa only [Nat.add_zero] using bound β ys (List.length_pos_iff.mpr hy)
  · exact hk
  · exact hf

end Resources.MedianPolicy
