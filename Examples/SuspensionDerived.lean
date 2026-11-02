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

def parameters : Parameters Empty := ⟨fun operation _ => nomatch operation, 0, 1⟩

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

end Examples.SuspensionDerived
