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

/-- The first pure specialization concerns only a literal result. Its memory
still contains the additional cached suspension. -/
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

end Suspensions.Core.Derived
