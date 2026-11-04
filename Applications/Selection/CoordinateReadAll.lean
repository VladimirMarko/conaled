import Applications.Selection.CoordinateQueries

/-!
A fixed coordinate-reading frontend for a computation on observed values.

`readPlan` sees only the fixed plan, the pure final computation, and the prior
transcript. Its input values are acquired by the existing charged `Runs.query`
transitions. `readAll` reads every coordinate in increasing index order before
applying the computation to those values. These query counts do not charge the
computation itself, transcript reversal, or plan lookup. Connecting a measured
selection implementation and its source-call tariff is a separate obligation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection.CoordinateQueries
universe u v

variable {n : Nat} {α : Type u} {β : Type v}

/-- Query the next planned coordinate, then compute using the chronological
observed answers. The hidden input is not an argument to the operation. -/
def readPlan (indices : List (Fin n)) (compute : List α → β) : Protocol n α β :=
  fun history =>
    match indices[history.length]? with
    | some i => Sum.inr i
    | none => Sum.inl (compute (history.reverse.map Prod.snd))

theorem readPlan_query (indices : List (Fin n)) (compute : List α → β)
    (history : Transcript n α) (i : Fin n)
    (query : indices[history.length]? = some i) :
    readPlan indices compute history = Sum.inr i := by
  simp only [readPlan, query]

theorem readPlan_done (indices : List (Fin n)) (compute : List α → β)
    (history : Transcript n α) (done : indices[history.length]? = none) :
    readPlan indices compute history = Sum.inl (compute (history.reverse.map Prod.snd)) := by
  simp only [readPlan, done]

/-- The prefix history is generated from actual answers. An arbitrary supplied
history is not presumed to satisfy this execution invariant. -/
private theorem readPlan_run_from (input : Fin n → α) (compute : List α → β)
    (prior remaining : List (Fin n)) :
    Runs (readPlan (prior ++ remaining) compute) input
      (prior.map (fun i => (i, input i))).reverse
      (remaining.map (fun i => (i, input i)))
      (compute ((prior ++ remaining).map input)) := by
  induction remaining generalizing prior with
  | nil =>
    apply Runs.done
    simp [readPlan, Function.comp_def]
  | cons i remaining ih =>
    apply Runs.query
    · have query : (prior ++ i :: remaining)[prior.length]? = some i := by
        rw [List.getElem?_append_right (Nat.le_refl prior.length)]
        simp
      simp only [readPlan, List.length_reverse, List.length_map, query]
    · simpa only [List.append_assoc, List.singleton_append, List.map_append,
        List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append] using ih (prior ++ [i])

/-- Every finite plan has this actual execution, including repeated indices. -/
theorem readPlan_run (indices : List (Fin n)) (compute : List α → β)
    (input : Fin n → α) :
    Runs (readPlan indices compute) input []
      (indices.map (fun i => (i, input i))) (compute (indices.map input)) := by
  simpa only [List.nil_append, List.map_nil, List.reverse_nil] using
    readPlan_run_from input compute [] indices

theorem readPlan_total (indices : List (Fin n)) (compute : List α → β) :
    Total (readPlan indices compute) :=
  fun input => ⟨_, _, readPlan_run indices compute input⟩

/-- Determinism identifies every terminating execution from an empty history;
the reverse implication supplies existence rather than assuming it. -/
theorem readPlan_run_iff (indices : List (Fin n)) (compute : List α → β)
    (input : Fin n → α) (trace : Transcript n α) (value : β) :
    Runs (readPlan indices compute) input [] trace value ↔
      trace = indices.map (fun i => (i, input i)) ∧
        value = compute (indices.map input) := by
  constructor
  · intro run
    exact run.deterministic (readPlan_run indices compute input)
  · rintro ⟨rfl, rfl⟩
    exact readPlan_run indices compute input

/-- Repeated plan entries remain separate charged queries. -/
theorem readPlan_length (indices : List (Fin n)) (compute : List α → β)
    (input : Fin n → α) (trace : Transcript n α) (value : β)
    (run : Runs (readPlan indices compute) input [] trace value) :
    trace.length = indices.length := by
  rw [((readPlan_run_iff indices compute input trace value).mp run).1]
  exact List.length_map _

theorem readPlan_work (indices : List (Fin n)) (compute : List α → β)
    (input : Fin n → α) (trace : Transcript n α) (value : β)
    (run : Runs (readPlan indices compute) input [] trace value) (c : Nat) :
    queryWork (fun _ _ => c) trace = c * indices.length := by
  rw [queryWork_constant, readPlan_length indices compute input trace value run]

/-- Read each of the n coordinates once, in increasing index order. -/
def readAll (compute : List α → β) : Protocol n α β :=
  readPlan (List.finRange n) compute

/-- The final computation consumes precisely the values actually read. -/
theorem readAll_run (compute : List α → β) (input : Fin n → α) :
    Runs (readAll compute) input [] (List.ofFn (fun i => (i, input i)))
      (compute (List.ofFn input)) := by
  simpa only [readAll, List.finRange, List.map_ofFn, Function.comp_def] using
    readPlan_run (List.finRange n) compute input

theorem readAll_total (compute : List α → β) : Total (readAll (n := n) compute) :=
  fun input => ⟨_, _, readAll_run compute input⟩

theorem readAll_run_iff (compute : List α → β) (input : Fin n → α)
    (trace : Transcript n α) (value : β) :
    Runs (readAll compute) input [] trace value ↔
      trace = List.ofFn (fun i => (i, input i)) ∧ value = compute (List.ofFn input) := by
  constructor
  · intro run
    exact run.deterministic (readAll_run compute input)
  · rintro ⟨rfl, rfl⟩
    exact readAll_run compute input

theorem readAll_coordinates (compute : List α → β) (input : Fin n → α)
    (trace : Transcript n α) (value : β)
    (run : Runs (readAll compute) input [] trace value) :
    trace.map Prod.fst = List.finRange n := by
  rw [((readAll_run_iff compute input trace value).mp run).1]
  simp only [List.map_ofFn, Function.comp_def, List.finRange]

theorem readAll_length (compute : List α → β) (input : Fin n → α)
    (trace : Transcript n α) (value : β)
    (run : Runs (readAll compute) input [] trace value) : trace.length = n := by
  rw [((readAll_run_iff compute input trace value).mp run).1]
  exact List.length_ofFn

/-- Exact acquisition tariff. This includes c=0; a positive-tariff lower bound
must separately assume positivity, as in `Runs.work_lower_bound`. -/
theorem readAll_work (compute : List α → β) (input : Fin n → α)
    (trace : Transcript n α) (value : β)
    (run : Runs (readAll compute) input [] trace value) (c : Nat) :
    queryWork (fun _ _ => c) trace = c * n := by
  rw [queryWork_constant, readAll_length compute input trace value run]

/-- Transfer a length-n value specification of the pure computation. This
conditional theorem supplies no selection algorithm or computation-cost bound. -/
theorem readAll_correct (compute : List α → β) (spec : List α → β → Prop)
    (correct : ∀ xs : List α, xs.length = n → spec xs (compute xs))
    (input : Fin n → α) (trace : Transcript n α) (value : β)
    (run : Runs (readAll compute) input [] trace value) :
    spec (List.ofFn input) value := by
  rw [((readAll_run_iff compute input trace value).mp run).2]
  exact correct (List.ofFn input) List.length_ofFn

end Applications.Selection.CoordinateQueries
