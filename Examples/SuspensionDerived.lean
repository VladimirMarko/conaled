import Applications.Suspensions.Derived

/-!
# Clients of the exact derived-form contracts

These cases use the public finite-run laws. The reference case distinguishes
evaluation after suspension allocation from evaluation in the original state;
the lazy-function cases distinguish strict arguments from delayed matching.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionDerived
open Suspensions Suspensions.Core Suspensions.Core.Machine Suspensions.Core.Derived

def parameters : Parameters Empty :=
  ⟨(fun operation _ => nomatch operation), 0, 1⟩

def initial : Memory Empty := { Suspensions.empty with exceptionNames := {0, 1} }

def integer (value : Int) : Expr Empty := .atom (.integer value)

theorem literal_retains_private_cache :
    ∃ answer,
      Progress.Evaluates (step parameters)
        (start initial [] (force (.delay (integer 7)))) answer 14 ∧
      answer.result = .value (.atom (.integer 7)) ∧
      answer.memory.memory 0 = some (.value (.atom (.integer 7))) ∧ answer.memory.next = 1 := by
  refine ⟨_, force_delay_atom parameters initial [] (.integer 7), rfl, ?_, rfl⟩
  exact memoize_lookup _ _ _

def referenceBody : Expr Empty := .reference (integer 7)

/-- The newly created reference has different concrete addresses in the two
runs; no literal equality with evaluation in the original memory is claimed. -/
theorem body_starts_after_allocation :
    ∃ suspended direct,
      Progress.Evaluates (step parameters)
        (start initial [] (force (.delay referenceBody))) suspended 16 ∧
      Progress.Evaluates (step parameters) (start initial [] referenceBody) direct 4 ∧
      suspended.result = .value (.address 1) ∧ direct.result = .value (.address 0) ∧
      suspended.memory.memory 0 = some (.value (.address 1)) ∧
      suspended.memory.memory 1 = some (.value (.atom (.integer 7))) := by
  let created := Suspensions.delay initial referenceBody []
  let afterBody := (Suspensions.allocate created.1 (.value (.atom (.integer 7)))).1
  have body : Progress.Evaluates (step parameters) (start created.1 [] referenceBody)
      ⟨afterBody, .value (.address 1)⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  have suspended := force_delay_value (memory := initial) (environment := [])
    (body := referenceBody) body
  have direct : Progress.Evaluates (step parameters) (start initial [] referenceBody)
      ⟨(Suspensions.allocate initial (.value (.atom (.integer 7)))).1, .value (.address 0)⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  refine ⟨_, _, suspended, direct, rfl, rfl, ?_, ?_⟩
  · exact memoize_lookup _ _ _
  · exact (memoize_other afterBody 0 (.address 1) (by decide : 1 ≠ 0)).trans
      (allocate_lookup created.1 (.value (.atom (.integer 7))))

def exceptionMemory : Memory Empty := { initial with exceptionNames := {0, 1, 2} }

def exceptionEnvironment : Env Empty := [(3, .exception 2 none)]

def raisingBody : Expr Empty := .raise (.variable 3)

/-- An exceptional body leaves the allocated thunk present and unforced. -/
theorem raised_body_keeps_thunk :
    ∃ answer,
      Progress.Evaluates (step parameters)
        (start exceptionMemory exceptionEnvironment (force (.delay raisingBody))) answer 14 ∧
      answer.result = .raised (.exception 2 none) ∧
      answer.memory.memory 0 = some (.thunk raisingBody exceptionEnvironment) ∧
      answer.memory.next = 1 := by
  let created := Suspensions.delay exceptionMemory raisingBody exceptionEnvironment
  have body : Progress.Evaluates (step parameters)
      (start created.1 exceptionEnvironment raisingBody) ⟨created.1, .raised (.exception 2 none)⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  refine ⟨_, force_delay_raised (memory := exceptionMemory) (environment := exceptionEnvironment)
    (body := raisingBody) body, rfl, ?_, rfl⟩
  exact delay_captures exceptionMemory raisingBody exceptionEnvironment

def clauses : List (Pattern × Expr Empty) :=
  [(.reference (.atom (.integer 7)), .delay (integer 9))]

/-- The argument's reference exists before the suspended match is created;
the selected right side has not allocated its own suspension yet. -/
theorem lazy_creation_after_strict_argument :
    ∃ answer,
      Progress.Evaluates (step parameters)
        (start initial []
          (.apply (lazyFunction (lazyBinder ([] : Env Empty) clauses) clauses) referenceBody))
        answer 13 ∧
      answer.result = .value (.address 1) ∧ answer.memory.next = 2 ∧
      answer.memory.memory 0 = some (.value (.atom (.integer 7))) ∧
      answer.memory.memory 1 = some (.thunk
        (lazyBody (lazyBinder ([] : Env Empty) clauses) clauses)
        [(lazyBinder ([] : Env Empty) clauses, .address 0)]) ∧
      lazyBinder ([] : Env Empty) clauses ∉ Names.clauseNames clauses := by
  let afterArgument := (Suspensions.allocate initial (.value (.atom (.integer 7)))).1
  have argument : Progress.Evaluates (step parameters) (start initial [] referenceBody)
      ⟨afterArgument, .value (.address 0)⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  refine ⟨_, lazy_function_value (clauses := clauses) argument, rfl, rfl, rfl, ?_, ?_⟩
  · exact delay_captures afterArgument _ _
  · exact (lazyBinder_fresh ([] : Env Empty) clauses).2

/-- A raised argument is observed before a lazy result can be allocated. -/
theorem lazy_argument_remains_strict :
    ∃ answer,
      Progress.Evaluates (step parameters)
        (start exceptionMemory exceptionEnvironment
          (.apply (lazyFunction (lazyBinder exceptionEnvironment clauses) clauses) raisingBody))
        answer 8 ∧
      answer.result = .raised (.exception 2 none) ∧ answer.memory.next = 0 ∧
      answer.memory.memory 0 = none := by
  have argument : Progress.Evaluates (step parameters)
      (start exceptionMemory exceptionEnvironment raisingBody)
      ⟨exceptionMemory, .raised (.exception 2 none)⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  exact ⟨_, lazy_function_raised (clauses := clauses) argument, rfl, rfl, rfl⟩

/-- The converse recovers the actual body run from any normal completed force.
The original-memory reference would still use address0 instead. -/
theorem force_reference_outcome_iff (after : Memory Empty) (value : Value Empty) (steps : Nat) :
    let created := Suspensions.delay initial referenceBody []
    let reached := (Suspensions.allocate created.1 (.value (.atom (.integer 7)))).1
    Progress.Evaluates (step parameters)
      (start initial [] (force (.delay referenceBody))) ⟨after, .value value⟩ steps ↔
      after = Suspensions.memoize reached created.2 (.address 1) ∧
      value = .address 1 ∧ steps = 16 := by
  let created := Suspensions.delay initial referenceBody []
  let reached := (Suspensions.allocate created.1 (.value (.atom (.integer 7)))).1
  have body : Progress.Evaluates (step parameters) (start created.1 [] referenceBody)
      ⟨reached, .value (.address 1)⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  constructor
  · intro run
    obtain ⟨bodyState, bodySteps, bodyRun, state, count⟩ := force_delay_value_iff.mp run
    have same := body.unique bodyRun
    have states : reached = bodyState := congrArg Answer.memory same.1
    have values := Result.value.inj (congrArg Answer.result same.1)
    have times := same.2
    subst bodyState
    subst value
    subst bodySteps
    exact ⟨state, rfl, count⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact force_delay_value (memory := initial) (environment := []) (body := referenceBody) body

/-- An arbitrary finite raised result is traced back to the same four-step body
run. No cache update can be inserted by the derived-force continuation. -/
theorem force_raise_outcome_iff (after : Memory Empty) (packet : Value Empty) (steps : Nat) :
    Progress.Evaluates (step parameters)
      (start exceptionMemory exceptionEnvironment (force (.delay raisingBody)))
      ⟨after, .raised packet⟩ steps ↔
      after = (Suspensions.delay exceptionMemory raisingBody exceptionEnvironment).1 ∧
      packet = .exception 2 none ∧ steps = 14 := by
  let created := Suspensions.delay exceptionMemory raisingBody exceptionEnvironment
  have body : Progress.Evaluates (step parameters)
      (start created.1 exceptionEnvironment raisingBody) ⟨created.1, .raised (.exception 2 none)⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  constructor
  · intro run
    obtain ⟨bodySteps, bodyRun, count⟩ := force_delay_raised_iff.mp run
    have same := body.unique bodyRun
    have states : created.1 = after := congrArg Answer.memory same.1
    have packets := Result.raised.inj (congrArg Answer.result same.1)
    have times := same.2
    subst after
    subst packet
    subst bodySteps
    exact ⟨rfl, rfl, count⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact force_delay_raised (memory := exceptionMemory) (environment := exceptionEnvironment)
      (body := raisingBody) body

/-- Recovering the strict argument run fixes both allocations and the count;
the selected right side's suspension is still only stored code. -/
theorem lazy_reference_outcome_iff (after : Memory Empty) (value : Value Empty) (steps : Nat) :
    let binder := lazyBinder ([] : Env Empty) clauses
    let afterArgument := (Suspensions.allocate initial (.value (.atom (.integer 7)))).1
    let created := Suspensions.delay afterArgument (lazyBody binder clauses) [(binder, .address 0)]
    Progress.Evaluates (step parameters)
      (start initial [] (.apply (lazyFunction binder clauses) referenceBody))
      ⟨after, .value value⟩ steps ↔
      after = created.1 ∧ value = .address 1 ∧ steps = 13 := by
  let afterArgument := (Suspensions.allocate initial (.value (.atom (.integer 7)))).1
  have argument : Progress.Evaluates (step parameters) (start initial [] referenceBody)
      ⟨afterArgument, .value (.address 0)⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  constructor
  · intro run
    obtain ⟨argumentState, argumentValue, argumentSteps, argumentRun, state, result, count⟩ :=
      lazy_function_value_iff.mp run
    have same := argument.unique argumentRun
    have states : afterArgument = argumentState := congrArg Answer.memory same.1
    have values := Result.value.inj (congrArg Answer.result same.1)
    have times := same.2
    subst argumentState
    subst argumentValue
    subst argumentSteps
    exact ⟨state, result, count⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact lazy_function_value (clauses := clauses) argument

/-- The exceptional converse confirms that lazy syntax still evaluates its
argument before any suspended clause matching is created. -/
theorem lazy_raise_outcome_iff (after : Memory Empty) (packet : Value Empty) (steps : Nat) :
    Progress.Evaluates (step parameters)
      (start exceptionMemory exceptionEnvironment
        (.apply (lazyFunction (lazyBinder exceptionEnvironment clauses) clauses) raisingBody))
      ⟨after, .raised packet⟩ steps ↔
      after = exceptionMemory ∧ packet = .exception 2 none ∧ steps = 8 := by
  have argument : Progress.Evaluates (step parameters)
      (start exceptionMemory exceptionEnvironment raisingBody)
      ⟨exceptionMemory, .raised (.exception 2 none)⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  constructor
  · intro run
    obtain ⟨argumentSteps, argumentRun, count⟩ := lazy_function_raised_iff.mp run
    have same := argument.unique argumentRun
    have states : exceptionMemory = after := congrArg Answer.memory same.1
    have packets := Result.raised.inj (congrArg Answer.result same.1)
    have times := same.2
    subst after
    subst packet
    subst argumentSteps
    exact ⟨rfl, rfl, count⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact lazy_function_raised (clauses := clauses) argument

/-- The second clause is selected only after the reference changes. Both
right sides return suspensions, as the book's lazy-function sugar requires. -/
def deferredClauses : List (Pattern × Expr Empty) :=
  [(.reference (.atom (.integer 7)), .delay (integer 9)),
   (.wildcard, .delay (integer 11))]

private theorem deferred_binder_eq : lazyBinder ([] : Env Empty) deferredClauses = 1 := by
  simp [lazyBinder, Names.fresh, deferredClauses, Names.clauseNames,
    Names.patternNames, Names.expressionNames, integer]

/-- Public lazy formation feeds an actual assignment and later force through
their exact reached states. The stored fresh binding remains literal; matching
sees the changed reference and reaches the second ordered clause. -/
theorem lazy_formation_then_force :
    let binder := lazyBinder ([] : Env Empty) deferredClauses
    let afterArgument := (Suspensions.allocate initial (.value (.atom (.integer 7)))).1
    let captured : Env Empty := [(binder, .address 0)]
    let created := Suspensions.delay afterArgument (lazyBody binder deferredClauses) captured
    let caller : Env Empty := [(2, .address 0), (3, .address 1)]
    let changed := Suspensions.memoize created.1 0 (.atom (.integer 8))
    ∃ creationEvents answer events,
      Progress.Evaluates (step parameters)
        (start initial [] (.apply (lazyFunction binder deferredClauses) referenceBody))
        ⟨created.1, .value (.address 1)⟩ 13 ∧
      Progress.Evaluates (tracedStep parameters)
        (start initial [] (.apply (lazyFunction binder deferredClauses) referenceBody), [])
        (⟨created.1, .value (.address 1)⟩, creationEvents) 13 ∧
      creationEvents.count (.referenceRead 0) = 0 ∧
      creationEvents.count (.body 1) = 0 ∧
      created.1.memory 1 = some (.thunk (lazyBody binder deferredClauses) captured) ∧
      Progress.Evaluates (step parameters)
        (start created.1 caller (.assign (.variable 2) (integer 8)))
        ⟨changed, .value (.record [])⟩ 6 ∧
      changed.memory 1 = some (.thunk (lazyBody binder deferredClauses) captured) ∧
      Progress.Evaluates (tracedStep parameters)
        (start changed caller (force (.variable 3)), []) (answer, events) 39 ∧
      answer.result = .value (.atom (.integer 11)) ∧ answer.memory.next = 3 ∧
      answer.memory.memory 0 = some (.value (.atom (.integer 8))) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 11))) ∧
      answer.memory.memory 2 = some (.value (.atom (.integer 11))) ∧
      events.count (.allocate 2) = 1 ∧
      events.count (.referenceRead 0) = 1 ∧
      events.count (.body 1) = 1 ∧ events.count (.body 2) = 1 ∧
      events.count (.cacheWrite 1) = 1 ∧ events.count (.cacheWrite 2) = 1 ∧
      events.count (.hit 1) = 0 ∧ events.count (.hit 2) = 0 := by
  let binder := lazyBinder ([] : Env Empty) deferredClauses
  let afterArgument := (Suspensions.allocate initial (.value (.atom (.integer 7)))).1
  let captured : Env Empty := [(binder, .address 0)]
  let created := Suspensions.delay afterArgument (lazyBody binder deferredClauses) captured
  let caller : Env Empty := [(2, .address 0), (3, .address 1)]
  let changed := Suspensions.memoize created.1 0 (.atom (.integer 8))
  have argument : Progress.Evaluates (step parameters) (start initial [] referenceBody)
      ⟨afterArgument, .value (.address 0)⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  have formation := lazy_function_value (clauses := deferredClauses) argument
  have assigned : Progress.Evaluates (step parameters)
      (start created.1 caller (.assign (.variable 2) (integer 8)))
      ⟨changed, .value (.record [])⟩ 6 :=
    .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))))
  refine ⟨_, _, _, formation,
    Progress.search_sound (step := tracedStep parameters) (fuel := 20) (by rfl),
    rfl, rfl, ?_, assigned, ?_,
    Progress.search_sound (step := tracedStep parameters) (fuel := 60)
      (by rw [deferred_binder_eq]; rfl), ?_⟩
  · exact delay_captures afterArgument (lazyBody binder deferredClauses) captured
  · exact (memoize_other created.1 0 (.atom (.integer 8)) (by decide : 1 ≠ 0)).trans
      (delay_captures afterArgument (lazyBody binder deferredClauses) captured)
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Examples.SuspensionDerived
