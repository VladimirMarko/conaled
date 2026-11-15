import Applications.Selection.CoordinateSensitivity
import Applications.Resources.Growth

/-!
Deterministic adaptive coordinate queries for selection.

The operation receives only its prior index/value history. `Runs` supplies each
answer by the requested coordinate of the hidden input. Histories are newest
first; completed query traces are chronological. Termination, correctness and
resource tariffs are separate laws. The lower bound concerns this query model,
not a tariff that provides an uncharged bulk-input operation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection.CoordinateQueries
universe u v

abbrev Transcript (n : Nat) (α : Type u) := List (Fin n × α)

/-- Either return an answer or request one valid coordinate. No input is passed
to this operation; fixed size and rank may be parameters of the operation. -/
abbrev Protocol (n : Nat) (α : Type u) (β : Type v) :=
  Transcript n α → Sum β (Fin n)

variable {n : Nat} {α : Type u} {β : Type v}

/-- A finite execution. The query constructor is the only access to the input. -/
inductive Runs (next : Protocol n α β) (input : Fin n → α) :
    Transcript n α → Transcript n α → β → Prop where
  | done {history : Transcript n α} {value : β}
      (decision : next history = Sum.inl value) :
      Runs next input history [] value
  | query {history : Transcript n α} {i : Fin n}
      {trace : Transcript n α} {value : β}
      (decision : next history = Sum.inr i)
      (rest : Runs next input ((i, input i) :: history) trace value) :
      Runs next input history ((i, input i) :: trace) value

variable {next : Protocol n α β} {input other : Fin n → α}
variable {history trace trace' : Transcript n α} {value value' : β}

/-- Termination is required on every input, not just on distinct inputs or on
the one execution used by a lower-bound witness. -/
def Total (next : Protocol n α β) : Prop :=
  ∀ input : Fin n → α, ∃ trace value, Runs next input [] trace value

/-- The recorded answer at every query is the actual coordinate value. -/
theorem Runs.answers (run : Runs next input history trace value) :
    ∀ i a, (i, a) ∈ trace → a = input i := by
  induction run with
  | done _ => simp
  | query _ _ ih =>
    intro i a ha
    rcases List.mem_cons.mp ha with ha | ha
    · cases ha
      rfl
    · exact ih i a ha

/-- Agreement on the coordinates actually queried reproduces the complete
terminating transcript and result, including any repeated queries. -/
theorem Runs.replay (run : Runs next input history trace value)
    (agree : ∀ i ∈ trace.map Prod.fst, input i = other i) :
    Runs next other history trace value := by
  revert agree
  induction run with
  | done decision =>
    intro _
    exact Runs.done decision
  | @query history i trace value decision rest ih =>
    intro agree
    have hi : input i = other i := agree i (by simp)
    have ht := ih (fun j hj => agree j (List.mem_cons_of_mem i hj))
    rw [hi] at ht ⊢
    exact Runs.query decision ht

/-- An unqueried coordinate can be changed without changing this execution. -/
theorem Runs.replay_update_of_not_mem (run : Runs next input history trace value)
    (i : Fin n) (a : α) (missing : i ∉ trace.map Prod.fst) :
    Runs next (Function.update input i a) history trace value :=
  run.replay (fun j hj => by
    have hji : j ≠ i := by
      intro he
      subst j
      exact missing hj
    exact (Function.update_of_ne hji a input).symm)

/-- A fixed operation and input cannot produce two different finite results. -/
theorem Runs.deterministic (run : Runs next input history trace value)
    (run' : Runs next input history trace' value') :
    trace = trace' ∧ value = value' := by
  induction run generalizing trace' value' with
  | done decision =>
    cases run' with
    | done decision' => exact ⟨rfl, Sum.inl.inj (decision.symm.trans decision')⟩
    | query decision' _ => cases (decision.symm.trans decision')
  | query decision _ ih =>
    cases run' with
    | done decision' => cases (decision.symm.trans decision')
    | query decision' rest' =>
      cases (Sum.inr.inj (decision.symm.trans decision'))
      obtain ⟨ht, hv⟩ := ih rest'
      exact ⟨by cases ht; rfl, hv⟩

/-- Correctness at the fixed valid rank for every integer input. Duplicates in
the input are allowed. `Total` separately requires an execution on every input. -/
def Selects (next : Protocol n Int Int) (k : Fin n) : Prop :=
  ∀ (input : Fin n → Int) trace value,
    Runs next input [] trace value → RankedAt (List.ofFn input) k.val value

/-- Sensitivity and replay force every coordinate to occur in a correct
terminating execution on a distinct input. -/
theorem Runs.queries_all {next : Protocol n Int Int} {input : Fin n → Int}
    {trace : Transcript n Int} {value : Int} (run : Runs next input [] trace value)
    (k : Fin n) (correct : Selects next k) (distinct : Function.Injective input) :
    ∀ i : Fin n, i ∈ trace.map Prod.fst := by
  intro i
  by_contra missing
  obtain ⟨z, changes⟩ := CoordinateSensitivity.exists_update_changes input k i distinct
  have replay : Runs next (Function.update input i z) [] trace value :=
    run.replay_update_of_not_mem i z missing
  have oldRank := correct input trace value run
  have newRank := correct (Function.update input i z) trace value replay
  exact changes ((ranked_iff_index.mp newRank).trans (ranked_iff_index.mp oldRank).symm)

/-- Repetitions count repeatedly. Covering all coordinates requires at least n
entries in the actual trace, not merely n distinct possible requests. -/
theorem Runs.length_lower_bound {next : Protocol n Int Int} {input : Fin n → Int}
    {trace : Transcript n Int} {value : Int} (run : Runs next input [] trace value)
    (k : Fin n) (correct : Selects next k) (distinct : Function.Injective input) :
    n ≤ trace.length := by
  have hsub : List.finRange n ⊆ trace.map Prod.fst := by
    intro i _
    exact run.queries_all k correct distinct i
  have h := (List.nodup_finRange n).length_le_of_subset hsub
  simpa only [List.length_finRange, List.length_map] using h

/-- The declared per-query resource observation on the actual chronological trace. -/
def queryWork (tariff : Fin n → α → Nat) : Transcript n α → Nat
  | [] => 0
  | (i, a) :: rest => tariff i a + queryWork tariff rest

theorem queryWork_nil (tariff : Fin n → α → Nat) : queryWork tariff [] = 0 := rfl

theorem queryWork_cons (tariff : Fin n → α → Nat) (i : Fin n) (a : α)
    (rest : Transcript n α) :
    queryWork tariff ((i, a) :: rest) = tariff i a + queryWork tariff rest := rfl

theorem queryWork_unit (trace : Transcript n α) :
    queryWork (fun _ _ => 1) trace = trace.length := by
  induction trace with
  | nil => rfl
  | cons entry rest ih =>
    cases entry
    simp only [queryWork, List.length_cons, ih]
    omega

theorem queryWork_constant (c : Nat) (trace : Transcript n α) :
    queryWork (fun _ _ => c) trace = c * trace.length := by
  induction trace with
  | nil => simp [queryWork]
  | cons entry rest ih =>
    cases entry
    simp only [queryWork, List.length_cons, ih, Nat.mul_add, Nat.mul_one]
    omega

/-- Each actual query must be charged at least one unit for this transfer. -/
theorem length_le_queryWork (tariff : Fin n → α → Nat)
    (positive : ∀ i a, 1 ≤ tariff i a) (trace : Transcript n α) :
    trace.length ≤ queryWork tariff trace := by
  induction trace with
  | nil => exact Nat.le_refl 0
  | cons entry rest ih =>
    obtain ⟨i, a⟩ := entry
    have hp := positive i a
    simp only [queryWork, List.length_cons]
    omega

theorem Runs.work_lower_bound {next : Protocol n Int Int} {input : Fin n → Int}
    {trace : Transcript n Int} {value : Int} (run : Runs next input [] trace value)
    (k : Fin n) (correct : Selects next k) (distinct : Function.Injective input)
    (tariff : Fin n → Int → Nat) (positive : ∀ i a, 1 ≤ tariff i a) :
    n ≤ queryWork tariff trace :=
  (run.length_lower_bound k correct distinct).trans
    (length_le_queryWork tariff positive trace)

/-- Explicit resource-contract transfer. Applying this to a source-call model
requires a separate proof of `coversQueries` for that actual execution. -/
theorem Runs.resource_lower_bound {next : Protocol n Int Int} {input : Fin n → Int}
    {trace : Transcript n Int} {value : Int} (run : Runs next input [] trace value)
    (k : Fin n) (correct : Selects next k) (distinct : Function.Injective input)
    (tariff : Fin n → Int → Nat) (positive : ∀ i a, 1 ≤ tariff i a)
    (resource : Nat) (coversQueries : queryWork tariff trace ≤ resource) :
    n ≤ resource :=
  (run.work_lower_bound k correct distinct tariff positive).trans coversQueries

/-- Total correctness yields a concrete distinct-input worst-case witness at
every valid size and rank. The increasing integer input supplies distinctness. -/
theorem exists_linear_run (next : Protocol n Int Int) (k : Fin n)
    (total : Total next) (correct : Selects next k) :
    ∃ (input : Fin n → Int) (trace : Transcript n Int) (value : Int),
      Function.Injective input ∧ Runs next input [] trace value ∧ n ≤ trace.length := by
  let input : Fin n → Int := fun i => (i.val : Int)
  have distinct : Function.Injective input := by
    intro i j he
    exact Fin.ext (Int.ofNat.inj he)
  obtain ⟨trace, value, run⟩ := total input
  exact ⟨input, trace, value, distinct, run, run.length_lower_bound k correct distinct⟩

/-- Every uniform worst-case bound for a family of correct total protocols is
at least the positive input size. No finite worst-case supremum is presumed. -/
theorem linear_worst_case_bound
    (next : (m : Nat) → Protocol (m + 1) Int Int) (k : (m : Nat) → Fin (m + 1))
    (total : ∀ m, Total (next m)) (correct : ∀ m, Selects (next m) (k m))
    (bound : Nat → Nat)
    (upper : ∀ m input trace value,
      Runs (next m) input [] trace value → trace.length ≤ bound (m + 1))
    (m : Nat) : m + 1 ≤ bound (m + 1) := by
  obtain ⟨input, trace, value, _, run, lower⟩ :=
    exists_linear_run (next m) (k m) (total m) (correct m)
  exact lower.trans (upper m input trace value run)

/-- The usual Ω(n) consequence: the size function is O of any uniform
worst-case query bound. This does not assert a physical-runtime lower bound. -/
theorem linear_isBigO_of_query_bound
    (next : (m : Nat) → Protocol (m + 1) Int Int) (k : (m : Nat) → Fin (m + 1))
    (total : ∀ m, Total (next m)) (correct : ∀ m, Selects (next m) (k m))
    (bound : Nat → Nat)
    (upper : ∀ m input trace value,
      Runs (next m) input [] trace value → trace.length ≤ bound (m + 1)) :
    Asymptotics.IsBigO Filter.atTop (fun m : Nat => (m : ℝ))
      (fun m => (bound m : ℝ)) := by
  apply Resources.isBigO_of_nat_bound (fun m => m) bound 1 1
  intro m hm
  have h := linear_worst_case_bound next k total correct bound upper (m - 1)
  have he : m - 1 + 1 = m := by omega
  simpa only [he, Nat.one_mul] using h

end Applications.Selection.CoordinateQueries
