import Applications.Suspensions.Continuation
import Applications.Suspensions.Names

/-!
# Exact execution contracts for the derived suspension forms

Force-after-delay evaluates its body from the state after the suspension has
been allocated. Normal return then updates that cell; exceptional return keeps
the body's reached state. No invariance under allocation or equality with a
body run from the original memory is assumed. Counts refer to the explicit
machine transitions, including final delivery, rather than host running time.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Derived
open Machine

variable {Primitive : Type}

private def forceFrames (environment : Env Primitive) (address : Nat) :
    List (Frame Primitive) :=
  [.memoize address environment (.variable 0),
   .clause environment (.variable 0) [] (.address address), .applicationResult]

private theorem finite_after {parameters : Parameters Primitive}
    {before after : Config Primitive} {answer : Answer Primitive}
    (run : ∃ steps, Progress.Evaluates (step parameters) before answer steps)
    (moved : step parameters before = .inr after) :
    ∃ steps, Progress.Evaluates (step parameters) after answer steps := by
  obtain ⟨steps, run⟩ := run
  cases run with
  | done finished => rw [moved] at finished; cases finished
  | next edge rest =>
      rw [moved] at edge
      cases edge
      exact ⟨_, rest⟩

private theorem force_delay_intro {parameters : Parameters Primitive}
    {memory : Memory Primitive} {environment : Env Primitive} {body : Expr Primitive}
    {answer : Answer Primitive} {steps : Nat}
    (run : Progress.Evaluates (step parameters)
      ⟨(Suspensions.delay memory body environment).1, .eval environment body,
        forceFrames environment (Suspensions.delay memory body environment).2⟩ answer steps) :
    Progress.Evaluates (step parameters)
      (start memory environment (force (.delay body))) answer (steps + 7) := by
  have enter : step parameters
      ⟨(Suspensions.delay memory body environment).1,
        .pattern environment (.suspended (.variable 0))
          (.address (Suspensions.delay memory body environment).2),
        [.clause environment (.variable 0) []
          (.address (Suspensions.delay memory body environment).2), .applicationResult]⟩ =
      .inr ⟨(Suspensions.delay memory body environment).1, .eval environment body,
        forceFrames environment (Suspensions.delay memory body environment).2⟩ :=
    congrArg Prod.fst (body_transition parameters
      (Suspensions.delay memory body environment).1 environment environment (.variable 0)
      (Suspensions.delay memory body environment).2 body
      [.clause environment (.variable 0) []
        (.address (Suspensions.delay memory body environment).2), .applicationResult]
      (Suspensions.delay_captures memory body environment))
  exact .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.next enter run))))))

/-- A finite normal body run is followed by memoization and the derived-force
return. The body premise starts from the allocated state, including its thunk. -/
theorem force_delay_value {parameters : Parameters Primitive}
    {memory afterBody : Memory Primitive} {environment : Env Primitive}
    {body : Expr Primitive} {value : Value Primitive} {steps : Nat}
    (run : Progress.Evaluates (step parameters)
      (start (Suspensions.delay memory body environment).1 environment body)
      ⟨afterBody, .value value⟩ steps) :
    Progress.Evaluates (step parameters)
      (start memory environment (force (.delay body)))
      ⟨Suspensions.memoize afterBody (Suspensions.delay memory body environment).2 value,
        .value value⟩ (steps + 12) := by
  have residual : Progress.Evaluates (step parameters)
      ⟨afterBody, .value value,
        forceFrames environment (Suspensions.delay memory body environment).2⟩
      ⟨Suspensions.memoize afterBody (Suspensions.delay memory body environment).2 value,
        .value value⟩ 6 :=
    .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))))
  have inside := evaluates_append run rfl
    (forceFrames environment (Suspensions.delay memory body environment).2) residual
  have entered : Progress.Evaluates (step parameters)
      ⟨(Suspensions.delay memory body environment).1, .eval environment body,
        forceFrames environment (Suspensions.delay memory body environment).2⟩
      ⟨Suspensions.memoize afterBody (Suspensions.delay memory body environment).2 value,
        .value value⟩ ((steps - 1) + 6) := by
    simpa only [appendFrames, start, List.nil_append] using inside
  have whole := force_delay_intro (memory := memory) (environment := environment)
    (body := body) entered
  have count : ((steps - 1) + 6) + 7 = steps + 12 := by
    cases run <;> omega
  simpa only [count] using whole

/-- An exceptional body return unwinds the force frames without its own cache
write. Any body/reentrant effects are retained in `afterBody` exactly. -/
theorem force_delay_raised {parameters : Parameters Primitive}
    {memory afterBody : Memory Primitive} {environment : Env Primitive}
    {body : Expr Primitive} {packet : Value Primitive} {steps : Nat}
    (run : Progress.Evaluates (step parameters)
      (start (Suspensions.delay memory body environment).1 environment body)
      ⟨afterBody, .raised packet⟩ steps) :
    Progress.Evaluates (step parameters)
      (start memory environment (force (.delay body)))
      ⟨afterBody, .raised packet⟩ (steps + 10) := by
  have residual : Progress.Evaluates (step parameters)
      ⟨afterBody, .raised packet,
        forceFrames environment (Suspensions.delay memory body environment).2⟩
      ⟨afterBody, .raised packet⟩ 4 :=
    .next rfl (.next rfl (.next rfl (.done rfl)))
  have inside := evaluates_append run rfl
    (forceFrames environment (Suspensions.delay memory body environment).2) residual
  have entered : Progress.Evaluates (step parameters)
      ⟨(Suspensions.delay memory body environment).1, .eval environment body,
        forceFrames environment (Suspensions.delay memory body environment).2⟩
      ⟨afterBody, .raised packet⟩ ((steps - 1) + 4) := by
    simpa only [appendFrames, start, List.nil_append] using inside
  have whole := force_delay_intro (memory := memory) (environment := environment)
    (body := body) entered
  have count : ((steps - 1) + 4) + 7 = steps + 10 := by
    cases run <;> omega
  simpa only [count] using whole

/-- Split a finite non-stuck force at its stored body. Inappropriate successful
pattern boundaries would hit an invalid continuation; no value-type safety
premise is used to exclude them. -/
private theorem force_delay_complete {parameters : Parameters Primitive}
    {memory : Memory Primitive} {environment : Env Primitive} {body : Expr Primitive}
    {answer : Answer Primitive} {steps : Nat} {finalControl : Control Primitive}
    (run : Progress.Evaluates (step parameters)
      (start memory environment (force (.delay body))) answer steps)
    (finalBoundary : boundaryControl answer.result = some finalControl) :
    (∃ afterBody value n,
      Progress.Evaluates (step parameters)
        (start (Suspensions.delay memory body environment).1 environment body)
        ⟨afterBody, .value value⟩ n ∧
      answer = ⟨Suspensions.memoize afterBody
        (Suspensions.delay memory body environment).2 value, .value value⟩ ∧
      steps = n + 12) ∨
    (∃ afterBody packet n,
      Progress.Evaluates (step parameters)
        (start (Suspensions.delay memory body environment).1 environment body)
        ⟨afterBody, .raised packet⟩ n ∧
      answer = ⟨afterBody, .raised packet⟩ ∧ steps = n + 10) := by
  have first := finite_after ⟨steps, run⟩ (by rfl)
  have second := finite_after first (by rfl)
  have third := finite_after second (by rfl)
  have fourth := finite_after third (by rfl)
  have fifth := finite_after fourth (by rfl)
  have sixth := finite_after fifth (by rfl)
  have enter := congrArg Prod.fst (body_transition parameters
    (Suspensions.delay memory body environment).1 environment environment (.variable 0)
    (Suspensions.delay memory body environment).2 body
    [.clause environment (.variable 0) []
      (.address (Suspensions.delay memory body environment).2), .applicationResult]
    (Suspensions.delay_captures memory body environment))
  obtain ⟨insideSteps, inside⟩ := finite_after sixth enter
  have plugged : Progress.Evaluates (step parameters)
      (appendFrames (start (Suspensions.delay memory body environment).1 environment body)
        (forceFrames environment (Suspensions.delay memory body environment).2))
      answer insideSteps := by
    simpa only [appendFrames, start, List.nil_append, forceFrames] using inside
  obtain ⟨bodyAnswer, control, n, m, bodyRun, boundary, residual, _⟩ :=
    evaluates_split plugged finalBoundary
  have notStuck (state : Memory Primitive) (fault : Fault) :
      (⟨state, .stuck fault⟩ : Answer Primitive) ≠ answer := by
    intro equal
    have same := congrArg (fun output : Answer Primitive => boundaryControl output.result) equal
    rw [finalBoundary] at same
    cases same
  rcases bodyAnswer with ⟨afterBody, result⟩
  cases result with
  | value value =>
      have canonical := force_delay_value (memory := memory) (environment := environment)
        (body := body) bodyRun
      have same := run.unique canonical
      exact Or.inl ⟨afterBody, value, n, bodyRun, same.1, same.2⟩
  | raised packet =>
      have canonical := force_delay_raised (memory := memory) (environment := environment)
        (body := body) bodyRun
      have same := run.unique canonical
      exact Or.inr ⟨afterBody, packet, n, bodyRun, same.1, same.2⟩
  | matched bindings =>
      simp only [boundaryControl, Option.some.injEq] at boundary
      subst control
      have fault : Progress.Evaluates (step parameters)
          ⟨afterBody, .matched bindings,
            forceFrames environment (Suspensions.delay memory body environment).2⟩
          ⟨afterBody, .stuck .invalidContinuation⟩ 1 := .done rfl
      exact False.elim (notStuck _ _ (fault.unique residual).1)
  | mismatch =>
      simp only [boundaryControl, Option.some.injEq] at boundary
      subst control
      have fault : Progress.Evaluates (step parameters)
          ⟨afterBody, .mismatch,
            forceFrames environment (Suspensions.delay memory body environment).2⟩
          ⟨afterBody, .stuck .invalidContinuation⟩ 1 := .done rfl
      exact False.elim (notStuck _ _ (fault.unique residual).1)
  | stuck fault => cases boundary

/-- Every finite normal force-after-delay run comes from a normal run of the
body in the allocated state, with exactly its final memoization and overhead. -/
theorem force_delay_value_iff {parameters : Parameters Primitive}
    {memory afterForce : Memory Primitive} {environment : Env Primitive}
    {body : Expr Primitive} {value : Value Primitive} {steps : Nat} :
    Progress.Evaluates (step parameters)
      (start memory environment (force (.delay body))) ⟨afterForce, .value value⟩ steps ↔
    ∃ afterBody bodySteps,
      Progress.Evaluates (step parameters)
        (start (Suspensions.delay memory body environment).1 environment body)
        ⟨afterBody, .value value⟩ bodySteps ∧
      afterForce = Suspensions.memoize afterBody
        (Suspensions.delay memory body environment).2 value ∧ steps = bodySteps + 12 := by
  constructor
  · intro run
    rcases force_delay_complete run rfl with
      ⟨afterBody, bodyValue, n, bodyRun, same, count⟩ |
      ⟨afterBody, packet, n, bodyRun, same, count⟩
    · have values := Result.value.inj (congrArg Answer.result same)
      subst bodyValue
      exact ⟨afterBody, n, bodyRun, congrArg Answer.memory same, count⟩
    · cases congrArg Answer.result same
  · rintro ⟨afterBody, bodySteps, bodyRun, rfl, rfl⟩
    exact force_delay_value bodyRun

/-- A finite raised force-after-delay run comes from a raised body run. Its
body-reached state is retained exactly, including any reentrant cache write. -/
theorem force_delay_raised_iff {parameters : Parameters Primitive}
    {memory afterBody : Memory Primitive} {environment : Env Primitive}
    {body : Expr Primitive} {packet : Value Primitive} {steps : Nat} :
    Progress.Evaluates (step parameters)
      (start memory environment (force (.delay body))) ⟨afterBody, .raised packet⟩ steps ↔
    ∃ bodySteps,
      Progress.Evaluates (step parameters)
        (start (Suspensions.delay memory body environment).1 environment body)
        ⟨afterBody, .raised packet⟩ bodySteps ∧ steps = bodySteps + 10 := by
  constructor
  · intro run
    rcases force_delay_complete run rfl with
      ⟨state, value, n, bodyRun, same, count⟩ |
      ⟨state, bodyPacket, n, bodyRun, same, count⟩
    · cases congrArg Answer.result same
    · have states : afterBody = state := congrArg Answer.memory same
      have packets := Result.raised.inj (congrArg Answer.result same)
      subst state
      subst bodyPacket
      exact ⟨n, bodyRun, count⟩
  · rintro ⟨bodySteps, bodyRun, rfl⟩
    exact force_delay_raised bodyRun

/-- The first pure specialization concerns only a literal result. The chosen
allocation cell contains its cache; freshness additionally follows from Bounded. -/
theorem force_delay_atom (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (atom : Atom) :
    Progress.Evaluates (step parameters)
      (start memory environment (force (.delay (.atom atom))))
      ⟨Suspensions.memoize (Suspensions.delay memory (.atom atom) environment).1
        (Suspensions.delay memory (.atom atom) environment).2 (.atom atom),
        .value (.atom atom)⟩ 14 :=
  force_delay_value (.next rfl (.done rfl))

/-- A binder absent from both the caller's keys and all conservative clause
names, using the shared source-specific name analysis. -/
def lazyBinder (environment : Env Primitive) (clauses : List (Pattern × Expr Primitive)) : Nat :=
  Suspensions.Names.fresh (environment.map Prod.fst).toFinset clauses

theorem lazyBinder_fresh (environment : Env Primitive)
    (clauses : List (Pattern × Expr Primitive)) :
    lazyBinder environment clauses ∉ (environment.map Prod.fst).toFinset ∧
    lazyBinder environment clauses ∉ Suspensions.Names.clauseNames clauses :=
  ⟨Suspensions.Names.fresh_context _ _, Suspensions.Names.fresh_clauses _ _⟩

/-- This code is stored, rather than evaluated, by lazy-function application. -/
def lazyBody (binder : Nat) (clauses : List (Pattern × Expr Primitive)) : Expr Primitive :=
  force (.apply (.function clauses) (.variable binder))

/-- Strict argument evaluation precedes creation of the suspended ordered
match. The fresh argument binding remains explicit in the captured environment;
no equality between arbitrary later closure environments is asserted. -/
theorem lazy_function_value {parameters : Parameters Primitive}
    {memory afterArgument : Memory Primitive} {environment : Env Primitive}
    {clauses : List (Pattern × Expr Primitive)} {argument : Expr Primitive}
    {value : Value Primitive} {steps : Nat}
    (run : Progress.Evaluates (step parameters) (start memory environment argument)
      ⟨afterArgument, .value value⟩ steps) :
    let binder := lazyBinder environment clauses
    let created := Suspensions.delay afterArgument (lazyBody binder clauses)
      (Env.extend environment [(binder, value)])
    Progress.Evaluates (step parameters)
      (start memory environment (.apply (lazyFunction binder clauses) argument))
      ⟨created.1, .value (.address created.2)⟩ (steps + 9) := by
  let binder := lazyBinder environment clauses
  let code := lazyBody binder clauses
  let function := Value.closure [(.variable binder, .delay code)] environment []
  let created := Suspensions.delay afterArgument code (Env.extend environment [(binder, value)])
  have residual : Progress.Evaluates (step parameters)
      ⟨afterArgument, .value value, [.argument function]⟩
      ⟨created.1, .value (.address created.2)⟩ 7 :=
    .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done rfl))))))
  have inside := evaluates_append run rfl [.argument function] residual
  have entered : Progress.Evaluates (step parameters)
      ⟨memory, .eval environment argument, [.argument function]⟩
      ⟨created.1, .value (.address created.2)⟩ ((steps - 1) + 7) := by
    simpa only [appendFrames, start, List.nil_append] using inside
  have whole : Progress.Evaluates (step parameters)
      (start memory environment (.apply (lazyFunction binder clauses) argument))
      ⟨created.1, .value (.address created.2)⟩ (((steps - 1) + 7) + 3) :=
    .next rfl (.next rfl (.next rfl entered))
  have count : ((steps - 1) + 7) + 3 = steps + 9 := by
    cases run <;> omega
  simpa only [count] using whole

/-- Lazy-function sugar remains strict in its argument. A raised argument
does not allocate the suspension for the ordered match. -/
theorem lazy_function_raised {parameters : Parameters Primitive}
    {memory afterArgument : Memory Primitive} {environment : Env Primitive}
    {clauses : List (Pattern × Expr Primitive)} {argument : Expr Primitive}
    {packet : Value Primitive} {steps : Nat}
    (run : Progress.Evaluates (step parameters) (start memory environment argument)
      ⟨afterArgument, .raised packet⟩ steps) :
    Progress.Evaluates (step parameters)
      (start memory environment
        (.apply (lazyFunction (lazyBinder environment clauses) clauses) argument))
      ⟨afterArgument, .raised packet⟩ (steps + 4) := by
  let binder := lazyBinder environment clauses
  let function := Value.closure [(.variable binder, .delay (lazyBody binder clauses))] environment []
  have residual : Progress.Evaluates (step parameters)
      ⟨afterArgument, .raised packet, [.argument function]⟩
      ⟨afterArgument, .raised packet⟩ 2 := .next rfl (.done rfl)
  have inside := evaluates_append run rfl [.argument function] residual
  have entered : Progress.Evaluates (step parameters)
      ⟨memory, .eval environment argument, [.argument function]⟩
      ⟨afterArgument, .raised packet⟩ ((steps - 1) + 2) := by
    simpa only [appendFrames, start, List.nil_append] using inside
  have whole : Progress.Evaluates (step parameters)
      (start memory environment (.apply (lazyFunction binder clauses) argument))
      ⟨afterArgument, .raised packet⟩ (((steps - 1) + 2) + 3) :=
    .next rfl (.next rfl (.next rfl entered))
  have count : ((steps - 1) + 2) + 3 = steps + 4 := by
    cases run <;> omega
  simpa only [count] using whole

private theorem lazy_function_complete {parameters : Parameters Primitive}
    {memory : Memory Primitive} {environment : Env Primitive}
    {clauses : List (Pattern × Expr Primitive)} {argument : Expr Primitive}
    {answer : Answer Primitive} {steps : Nat} {finalControl : Control Primitive}
    (run : Progress.Evaluates (step parameters)
      (start memory environment
        (.apply (lazyFunction (lazyBinder environment clauses) clauses) argument)) answer steps)
    (finalBoundary : boundaryControl answer.result = some finalControl) :
    (∃ afterArgument value n,
      let binder := lazyBinder environment clauses
      let created := Suspensions.delay afterArgument (lazyBody binder clauses)
        (Env.extend environment [(binder, value)])
      Progress.Evaluates (step parameters) (start memory environment argument)
        ⟨afterArgument, .value value⟩ n ∧
      answer = ⟨created.1, .value (.address created.2)⟩ ∧ steps = n + 9) ∨
    (∃ afterArgument packet n,
      Progress.Evaluates (step parameters) (start memory environment argument)
        ⟨afterArgument, .raised packet⟩ n ∧
      answer = ⟨afterArgument, .raised packet⟩ ∧ steps = n + 4) := by
  let binder := lazyBinder environment clauses
  let function := Value.closure [(.variable binder, .delay (lazyBody binder clauses))]
    environment []
  have first := finite_after ⟨steps, run⟩ (by rfl)
  have second := finite_after first (by rfl)
  obtain ⟨insideSteps, inside⟩ := finite_after second (by rfl)
  have plugged : Progress.Evaluates (step parameters)
      (appendFrames (start memory environment argument) [.argument function])
      answer insideSteps := by
    simpa only [appendFrames, start, List.nil_append, function, binder, lazyBody] using inside
  obtain ⟨argumentAnswer, control, n, m, argumentRun, boundary, residual, _⟩ :=
    evaluates_split plugged finalBoundary
  have notStuck (state : Memory Primitive) (fault : Fault) :
      (⟨state, .stuck fault⟩ : Answer Primitive) ≠ answer := by
    intro equal
    have same := congrArg (fun output : Answer Primitive => boundaryControl output.result) equal
    rw [finalBoundary] at same
    cases same
  rcases argumentAnswer with ⟨afterArgument, result⟩
  cases result with
  | value value =>
      have canonical := lazy_function_value (memory := memory) (environment := environment)
        (clauses := clauses) argumentRun
      have same := run.unique canonical
      exact Or.inl ⟨afterArgument, value, n, argumentRun, same.1, same.2⟩
  | raised packet =>
      have canonical := lazy_function_raised (memory := memory) (environment := environment)
        (clauses := clauses) argumentRun
      have same := run.unique canonical
      exact Or.inr ⟨afterArgument, packet, n, argumentRun, same.1, same.2⟩
  | matched bindings =>
      simp only [boundaryControl, Option.some.injEq] at boundary
      subst control
      have fault : Progress.Evaluates (step parameters)
          ⟨afterArgument, .matched bindings, [.argument function]⟩
          ⟨afterArgument, .stuck .invalidContinuation⟩ 1 := .done rfl
      exact False.elim (notStuck _ _ (fault.unique residual).1)
  | mismatch =>
      simp only [boundaryControl, Option.some.injEq] at boundary
      subst control
      have fault : Progress.Evaluates (step parameters)
          ⟨afterArgument, .mismatch, [.argument function]⟩
          ⟨afterArgument, .stuck .invalidContinuation⟩ 1 := .done rfl
      exact False.elim (notStuck _ _ (fault.unique residual).1)
  | stuck fault => cases boundary

/-- Normal lazy-function formation is precisely a normal strict-argument run
followed by allocation of the delayed ordered match. No clause has yet run. -/
theorem lazy_function_value_iff {parameters : Parameters Primitive}
    {memory afterCreation : Memory Primitive} {environment : Env Primitive}
    {clauses : List (Pattern × Expr Primitive)} {argument : Expr Primitive}
    {result : Value Primitive} {steps : Nat} :
    Progress.Evaluates (step parameters)
      (start memory environment
        (.apply (lazyFunction (lazyBinder environment clauses) clauses) argument))
      ⟨afterCreation, .value result⟩ steps ↔
    ∃ afterArgument value argumentSteps,
      let binder := lazyBinder environment clauses
      let created := Suspensions.delay afterArgument (lazyBody binder clauses)
        (Env.extend environment [(binder, value)])
      Progress.Evaluates (step parameters) (start memory environment argument)
        ⟨afterArgument, .value value⟩ argumentSteps ∧
      afterCreation = created.1 ∧ result = .address created.2 ∧ steps = argumentSteps + 9 := by
  constructor
  · intro run
    rcases lazy_function_complete run rfl with
      ⟨afterArgument, value, n, argumentRun, same, count⟩ |
      ⟨afterArgument, packet, n, argumentRun, same, count⟩
    · exact ⟨afterArgument, value, n, argumentRun, congrArg Answer.memory same,
        Result.value.inj (congrArg Answer.result same), count⟩
    · cases congrArg Answer.result same
  · rintro ⟨afterArgument, value, argumentSteps, argumentRun, rfl, rfl, rfl⟩
    exact lazy_function_value argumentRun

/-- A raised lazy-function application comes exactly from its strict argument;
the delayed ordered match has not been allocated. -/
theorem lazy_function_raised_iff {parameters : Parameters Primitive}
    {memory afterArgument : Memory Primitive} {environment : Env Primitive}
    {clauses : List (Pattern × Expr Primitive)} {argument : Expr Primitive}
    {packet : Value Primitive} {steps : Nat} :
    Progress.Evaluates (step parameters)
      (start memory environment
        (.apply (lazyFunction (lazyBinder environment clauses) clauses) argument))
      ⟨afterArgument, .raised packet⟩ steps ↔
    ∃ argumentSteps,
      Progress.Evaluates (step parameters) (start memory environment argument)
        ⟨afterArgument, .raised packet⟩ argumentSteps ∧ steps = argumentSteps + 4 := by
  constructor
  · intro run
    rcases lazy_function_complete run rfl with
      ⟨state, value, n, argumentRun, same, count⟩ |
      ⟨state, argumentPacket, n, argumentRun, same, count⟩
    · cases congrArg Answer.result same
    · have states : afterArgument = state := congrArg Answer.memory same
      have packets := Result.raised.inj (congrArg Answer.result same)
      subst state
      subst argumentPacket
      exact ⟨n, argumentRun, count⟩
  · rintro ⟨argumentSteps, argumentRun, rfl⟩
    exact lazy_function_raised argumentRun

end Suspensions.Core.Derived
