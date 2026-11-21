import Applications.Selection.CoordinateReadAll
import Applications.Resources.SelectionBounds

/-!
The actual measured book selector after charged coordinate acquisition.

The operation knows only its fixed rank and prior transcript. `readAll` obtains
the list supplied to `Resources.Selection.selectRun`; its measured source calls
are retained in the result. Combined work charges every coordinate query and
adds those actual calls. The existing query model leaves frontend bookkeeping,
plan lookup and projections uncharged. No physical-runtime claim is made.

Correctness permits duplicate inputs. The competitor lower bound keeps the
distinct-input, valid-rank and positive-query-tariff domain of FDSA-3-81 to FDSA-3-83.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection.CoordinateSelection
open Applications.Selection.CoordinateQueries
universe u

variable {n : Nat} {α : Type u}

/-- Read all unknown coordinates before executing the fixed measured selector.
The hidden input is not an argument to this operation. -/
def observedSelect [LinearOrder α] (k : Nat) :
    Protocol n α (Resources.Measured (Option α) Nat) :=
  readAll (Resources.Selection.selectRun k)

/-- An actual execution, including empty inputs and invalid natural ranks. -/
theorem observedSelect_run [LinearOrder α] (k : Nat) (input : Fin n → α) :
    Runs (observedSelect k) input [] (List.ofFn (fun i => (i, input i)))
      (Resources.Selection.selectRun k (List.ofFn input)) :=
  readAll_run (Resources.Selection.selectRun k) input

theorem observedSelect_total [LinearOrder α] (k : Nat) :
    Total (observedSelect (n := n) (α := α) k) :=
  readAll_total (Resources.Selection.selectRun k)

theorem observedSelect_run_iff [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat) :
    Runs (observedSelect k) input [] trace observation ↔
      trace = List.ofFn (fun i => (i, input i)) ∧
        observation = Resources.Selection.selectRun k (List.ofFn input) :=
  readAll_run_iff (Resources.Selection.selectRun k) input trace observation

/-- The chronological answers are exactly the acquired source list. -/
theorem observedSelect_acquired [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) :
    trace.map Prod.snd = List.ofFn input := by
  rw [((observedSelect_run_iff k input trace observation).mp run).1]
  simp only [List.map_ofFn, Function.comp_def]

/-- Both the value and source-call observation come from the actual worker
on acquired answers, not from a separately supplied input or answer. -/
theorem observedSelect_on_acquired [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) :
    observation = Resources.Selection.selectRun k (trace.map Prod.snd) := by
  rw [observedSelect_acquired k input trace observation run]
  exact ((observedSelect_run_iff k input trace observation).mp run).2

theorem observedSelect_some_iff [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) (a : α) :
    observation.1 = some a ↔ RankedAt (List.ofFn input) k a := by
  rw [((observedSelect_run_iff k input trace observation).mp run).2]
  exact Resources.Selection.selectRun_some_iff k (List.ofFn input) a

/-- Invalid ranks retain their actual entry/length-only selector charge. -/
theorem observedSelect_of_invalid [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) (invalid : n ≤ k) :
    observation = (none, n + 2) := by
  rw [((observedSelect_run_iff k input trace observation).mp run).2]
  simpa only [List.length_ofFn] using Resources.Selection.selectRun_of_invalid
    k (List.ofFn input) (by simpa only [List.length_ofFn] using invalid)

theorem observedSelect_length [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) : trace.length = n :=
  readAll_length (Resources.Selection.selectRun k) input trace observation run

theorem observedSelect_query_work [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) (c : Nat) :
    queryWork (fun _ _ => c) trace = c * n :=
  readAll_work (Resources.Selection.selectRun k) input trace observation run c

/-- The declared combined observation pays acquisition and actual selection.
The second summand is the source-call count returned by the measured worker. -/
def work (c : Nat) (trace : Transcript n α)
    (observation : Resources.Measured (Option α) Nat) : Nat :=
  queryWork (fun _ _ => c) trace + observation.2

theorem work_acquisition [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) (c : Nat) :
    work c trace observation = c * n + observation.2 := by
  rw [work, observedSelect_query_work k input trace observation run c]

/-- This exact identity supplies the source-call observation bridge. -/
theorem work_exact [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) (c : Nat) :
    work c trace observation =
      c * n + (Resources.Selection.selectRun k (List.ofFn input)).2 := by
  rw [work_acquisition k input trace observation run c,
    ((observedSelect_run_iff k input trace observation).mp run).2]

/-- Query coverage is proved for this concrete observation, not assumed as a
resource-contract hypothesis. -/
theorem work_covers_queries (c : Nat) (trace : Transcript n α)
    (observation : Resources.Measured (Option α) Nat) :
    queryWork (fun _ _ => c) trace ≤ work c trace observation := by
  unfold work
  omega

theorem source_cost_le_F [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) :
    observation.2 ≤ Resources.SelectionRecurrence.F n := by
  rw [((observedSelect_run_iff k input trace observation).mp run).2]
  simpa only [List.length_ofFn] using
    Resources.Selection.selectRun_cost_le_F k (List.ofFn input)

/-- The paid upper bound uses the checked actual worker recurrence. -/
theorem work_le_F [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) (c : Nat) :
    work c trace observation ≤ c * n + Resources.SelectionRecurrence.F n := by
  rw [work_acquisition k input trace observation run c]
  exact Nat.add_le_add_left (source_cost_le_F k input trace observation run) (c * n)

/-- One pair of constants precedes the type, tariff, size, rank and input.
The affine statement includes empty inputs and every invalid rank. -/
theorem work_exists_uniform_affine_bound :
    ∃ A B : Nat, ∀ (β : Type u) [LinearOrder β] (c m k : Nat)
      (input : Fin m → β) (trace : Transcript m β)
      (observation : Resources.Measured (Option β) Nat),
      Runs (observedSelect k) input [] trace observation →
        work c trace observation ≤ (c + A) * m + B := by
  obtain ⟨A, B, bound⟩ := Resources.Selection.selectRun_exists_uniform_affine_bound.{u}
  refine ⟨A, B, ?_⟩
  intro β inst c m k input trace observation run
  rw [work_exact k input trace observation run c]
  have h := bound β (List.ofFn input) k
  simpa only [List.length_ofFn, Nat.add_mul, Nat.add_assoc] using
    Nat.add_le_add_left h (c * m)

/-- Positive sizes absorb the affine constant. The constants remain uniform
over payload types, inputs, ranks and acquisition tariffs. -/
theorem work_exists_uniform_linear_bound :
    ∃ C : Nat, ∀ (β : Type u) [LinearOrder β] (c m k : Nat)
      (input : Fin m → β) (trace : Transcript m β)
      (observation : Resources.Measured (Option β) Nat),
      Runs (observedSelect k) input [] trace observation → 0 < m →
        work c trace observation ≤ (c + C) * m := by
  obtain ⟨C, bound⟩ := Resources.Selection.selectRun_exists_uniform_linear_bound.{u}
  refine ⟨C, ?_⟩
  intro β inst c m k input trace observation run positive
  rw [work_exact k input trace observation run c]
  have h := bound β (List.ofFn input) k
    (by simpa only [List.length_ofFn] using positive)
  simpa only [List.length_ofFn, Nat.add_mul] using Nat.add_le_add_left h (c * m)

theorem work_lower_acquisition [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) (c : Nat) :
    c * n ≤ work c trace observation := by
  rw [work_acquisition k input trace observation run c]
  omega

theorem work_lower_input [LinearOrder α] (k : Nat) (input : Fin n → α)
    (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) (c : Nat)
    (positive : 1 ≤ c) : n ≤ work c trace observation := by
  have hn : n ≤ c * n := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right n positive
  exact hn.trans (work_lower_acquisition k input trace observation run c)

/-- Any family of actual executions has linear declared work for fixed c.
The run premise identifies execution, not a hypothesized cost bound. -/
theorem work_family_isBigO [LinearOrder α] (c : Nat)
    (inputs : (m : Nat) → Fin m → α) (ranks : Nat → Nat)
    (traces : (m : Nat) → Transcript m α)
    (observations : Nat → Resources.Measured (Option α) Nat)
    (runs : ∀ m, Runs (observedSelect (ranks m)) (inputs m) []
      (traces m) (observations m)) :
    Asymptotics.IsBigO Filter.atTop
      (fun m : Nat => (work c (traces m) (observations m) : ℝ))
      (fun m => (m : ℝ)) := by
  obtain ⟨C, bound⟩ := work_exists_uniform_linear_bound.{u}
  apply Resources.isBigO_of_nat_bound
    (fun m => work c (traces m) (observations m)) (fun m => m) (c + C) 1
  intro m hm
  exact bound α c m (ranks m) (inputs m) (traces m) (observations m)
    (runs m) (by omega)

/-- Valid integer ranks return some actual value before the fixed default is
projected. Duplicates are allowed throughout this correctness statement. -/
theorem observedSelect_valid (k : Fin n) (input : Fin n → Int)
    (trace : Transcript n Int) (observation : Resources.Measured (Option Int) Nat)
    (run : Runs (observedSelect k.val) input [] trace observation) :
    observation.1 = some (observation.1.getD 0) ∧
      RankedAt (List.ofFn input) k.val (observation.1.getD 0) := by
  obtain ⟨a, ha⟩ := Resources.Selection.selectRunWith_exists 5 20
    (by decide) (by decide) k.val (List.ofFn input)
    (by simpa only [List.length_ofFn] using k.isLt)
  change (Resources.Selection.selectRun k.val (List.ofFn input)).1 = some a at ha
  have answer : observation.1 = some a := by
    rw [((observedSelect_run_iff k.val input trace observation).mp run).2]
    exact ha
  have ranked := (observedSelect_some_iff k.val input trace observation run a).mp answer
  constructor
  · simp only [answer, Option.getD_some]
  · simpa only [answer, Option.getD_some] using ranked

/-- The value view projects the final measured result and preserves requests.
Its default is fixed independently of the hidden input. -/
def selectedValue (k : Nat) : Protocol n Int Int :=
  fun history =>
    match observedSelect k history with
    | Sum.inl observation => Sum.inl (observation.1.getD 0)
    | Sum.inr i => Sum.inr i

theorem selectedValue_eq_readAll (k : Nat) :
    selectedValue (n := n) k =
      readAll (fun xs : List Int => (Resources.Selection.selectRun k xs).1.getD 0) := by
  funext history
  cases lookup : (List.finRange n)[history.length]? <;>
    simp only [selectedValue, observedSelect, readAll, readPlan, lookup]

/-- The projected run is the same actual observation and trace. -/
theorem selectedValue_run_iff (k : Nat) (input : Fin n → Int)
    (trace : Transcript n Int) (value : Int) :
    Runs (selectedValue k) input [] trace value ↔
      ∃ observation : Resources.Measured (Option Int) Nat,
        Runs (observedSelect k) input [] trace observation ∧
          value = observation.1.getD 0 := by
  rw [selectedValue_eq_readAll, readAll_run_iff]
  constructor
  · rintro ⟨ht, hv⟩
    refine ⟨Resources.Selection.selectRun k (List.ofFn input), ?_, hv⟩
    rw [ht]
    exact observedSelect_run k input
  · rintro ⟨observation, run, hv⟩
    obtain ⟨ht, ho⟩ := (observedSelect_run_iff k input trace observation).mp run
    rw [ho] at hv
    exact ⟨ht, hv⟩

theorem selectedValue_total (k : Nat) : Total (selectedValue (n := n) k) := by
  intro input
  obtain ⟨trace, observation, run⟩ := observedSelect_total k input
  exact ⟨trace, observation.1.getD 0,
    (selectedValue_run_iff k input trace (observation.1.getD 0)).mpr
      ⟨observation, run, rfl⟩⟩

/-- The existing lower-bound consumer is correct on every integer input. -/
theorem selectedValue_correct (k : Fin n) : Selects (selectedValue k.val) k := by
  intro input trace value run
  obtain ⟨observation, actual, value_eq⟩ :=
    (selectedValue_run_iff k.val input trace value).mp run
  rw [value_eq]
  exact (observedSelect_valid k input trace observation actual).2

private theorem input_injective_of_nodup (input : Fin n → Int)
    (distinct : (List.ofFn input).Nodup) : Function.Injective input := by
  intro i j equal
  have hi : i.val < (List.ofFn input).length := by
    simpa only [List.length_ofFn] using i.isLt
  have hj : j.val < (List.ofFn input).length := by
    simpa only [List.length_ofFn] using j.isLt
  have elements : (List.ofFn input)[i.val]'hi = (List.ofFn input)[j.val]'hj := by
    simpa only [List.getElem_ofFn] using equal
  exact Fin.ext (distinct.getElem_inj.mp elements)

/-- Every correct competitor run on a distinct valid-rank input pays for at
least n query occurrences. Repeated requests remain separately charged. -/
theorem competitor_query_work_lower_bound (k : Fin n) (input : Fin n → Int)
    (distinct : (List.ofFn input).Nodup) (next : Protocol n Int Int)
    (correct : Selects next k) (trace : Transcript n Int) (value : Int)
    (run : Runs next input [] trace value) (c : Nat) :
    c * n ≤ queryWork (fun _ _ => c) trace := by
  rw [queryWork_constant]
  exact Nat.mul_le_mul_left c
    (run.length_lower_bound k correct (input_injective_of_nodup input distinct))

/-- One constant compares the actual paid book algorithm with every correct
competitor's query work, on every distinct valid-rank input and positive tariff.
No assumed resource coverage or linear execution bound is a premise. -/
theorem exists_uniform_competitor_bound :
    ∃ K : Nat, ∀ (c m : Nat) (k : Fin m) (input : Fin m → Int)
      (_distinct : (List.ofFn input).Nodup) (next : Protocol m Int Int)
      (_correct : Selects next k) (trace : Transcript m Int)
      (observation : Resources.Measured (Option Int) Nat)
      (otherTrace : Transcript m Int) (value : Int),
      1 ≤ c → Runs (observedSelect k.val) input [] trace observation →
      Runs next input [] otherTrace value →
        work c trace observation ≤ K * queryWork (fun _ _ => c) otherTrace := by
  obtain ⟨C, bound⟩ := work_exists_uniform_linear_bound.{0}
  refine ⟨C + 1, ?_⟩
  intro c m k input distinct next correct trace observation otherTrace value
    positive run otherRun
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  have upper := bound Int c m k.val input trace observation run hm
  have lower := competitor_query_work_lower_bound
    k input distinct next correct otherTrace value otherRun c
  have size : m ≤ c * m := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right m positive
  calc
    work c trace observation ≤ (c + C) * m := upper
    _ = c * m + C * m := Nat.add_mul c C m
    _ ≤ c * m + C * (c * m) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left C size) (c * m)
    _ = (C + 1) * (c * m) := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _
    _ ≤ (C + 1) * queryWork (fun _ _ => c) otherTrace :=
      Nat.mul_le_mul_left (C + 1) lower

/-- Total correctness supplies both real executions and equal selected values.
This is the concrete optimality comparison in the declared coordinate model. -/
theorem exists_uniform_optimality :
    ∃ K : Nat, ∀ (c m : Nat) (k : Fin m) (input : Fin m → Int)
      (_distinct : (List.ofFn input).Nodup) (next : Protocol m Int Int)
      (_total : Total next) (_correct : Selects next k),
      1 ≤ c → ∃ (trace : Transcript m Int)
        (observation : Resources.Measured (Option Int) Nat)
        (otherTrace : Transcript m Int) (value : Int),
        Runs (observedSelect k.val) input [] trace observation ∧
        Runs next input [] otherTrace value ∧ observation.1 = some value ∧
        m ≤ queryWork (fun _ _ => c) otherTrace ∧
        work c trace observation ≤ K * queryWork (fun _ _ => c) otherTrace := by
  obtain ⟨K, bound⟩ := exists_uniform_competitor_bound
  refine ⟨K, ?_⟩
  intro c m k input distinct next total correct positive
  obtain ⟨trace, observation, run⟩ := observedSelect_total k.val input
  obtain ⟨otherTrace, value, otherRun⟩ := total input
  have lower := competitor_query_work_lower_bound
    k input distinct next correct otherTrace value otherRun c
  have size : m ≤ c * m := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right m positive
  refine ⟨trace, observation, otherTrace, value, run, otherRun, ?_, size.trans lower,
    bound c m k input distinct next correct trace observation otherTrace value
      positive run otherRun⟩
  exact (observedSelect_some_iff k.val input trace observation run value).mpr
    (correct input otherTrace value otherRun)

end Applications.Selection.CoordinateSelection
