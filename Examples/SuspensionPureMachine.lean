import Applications.Suspensions.Pure.Machine
import Mathlib.Logic.Function.Iterate

/-!
# Executions of the auxiliary unshared interpretation

These clients retain the same source terms used by the suspension core. Their
expected answers, exact body meanings and positive transition counts are
stated before the search proofs. Each finite execution is obtained through
`Progress.search_sound`, and erasure uses the public instrumentation theorem.
They do not establish a bridge to a heap, a cache theorem or nonreentrancy.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureMachine
open Suspensions.Pure Suspensions.Pure.Machine
open Suspensions.Core (Expr Pattern force)

def parameters : Parameters Empty where
  primitive := fun operation => nomatch operation
  matchException := 0
  bindException := 1

def integer (n : Int) : Expr Empty := .atom (.integer n)

def boolean (b : Bool) : Expr Empty := .atom (.boolean b)

def lexical : Expr Empty :=
  .bind (.variable 1) (integer 1)
    (.bind (.variable 2) (.delay (.variable 1))
      (.bind (.variable 1) (integer 2) (force (.variable 2))))

/-- Three ordinary bindings add15 transitions to the14-step force. The body
looks up the captured1, even though its caller has since shadowed that name. -/
theorem lexical_capture :
    ∃ events,
      Progress.Evaluates (tracedStep parameters) (start [] lexical, [])
        (.value (.atom (.integer 1)), events) 29 ∧
      bodyEntries events = [(.variable 1, [(1, .atom (.integer 1))], none)] := by
  refine ⟨_, Progress.search_sound (step := tracedStep parameters)
    (fuel := 29) (by rfl), ?_⟩
  rfl

def repeated : Expr Empty :=
  .bind (.variable 1) (.delay (integer 7))
    (.bind .wildcard (force (.variable 1)) (force (.variable 1)))

theorem repeated_allowed : ExpressionAllowed (fun _ : Empty => False) repeated := by
  unfold repeated integer force
  repeat' constructor

/-- Both forces enter exactly the same code/capture/descriptor. Two14-step
forces plus the enclosing bindings take36 auxiliary transitions. -/
theorem repeated_forcing_enters_twice :
    ∃ events,
      Progress.Evaluates (tracedStep parameters) (start [] repeated, [])
        (.value (.atom (.integer 7)), events) 36 ∧
      bodyEntries events = [(integer 7, [], none), (integer 7, [], none)] := by
  refine ⟨_, Progress.search_sound (step := tracedStep parameters)
    (fuel := 36) (by rfl), ?_⟩
  rfl

/-- The observations erase to the existing finite evaluation judgment, and
every transition contributes one event, including continuation returns. -/
theorem repeated_uninstrumented :
    Progress.Evaluates (step parameters) (start [] repeated)
      (.value (.atom (.integer 7))) 36 ∧
    ∃ events, events.length = 36 ∧
      bodyEntries events = [(integer 7, [], none), (integer 7, [], none)] := by
  obtain ⟨events, evaluated, bodies⟩ := repeated_forcing_enters_twice
  refine ⟨traced_evaluates_erases evaluated, events, ?_, bodies⟩
  simpa only [List.length_nil, Nat.zero_add] using traced_evaluates_length evaluated

def mutualClauses : List (Pattern × Expr Empty) :=
  [(.variable 3, .branch (.variable 3) (integer 7) (force (.variable 2)))]

def mutualDefinitions : List (Nat × Rhs Empty) :=
  [(1, .function mutualClauses), (2, .delay (.apply (.variable 1) (boolean true)))]

def mutualGroup : Suspensions.Pure.Group Empty := .mk mutualDefinitions []

def mutualTerm : Expr Empty :=
  .recursive (Rhs.toBindings mutualDefinitions) (.apply (.variable 1) (boolean false))

theorem mutual_allowed : ExpressionAllowed (fun _ : Empty => False) mutualTerm := by
  simp only [mutualTerm, mutualDefinitions, mutualClauses, Rhs.toBindings, Rhs.toExpr,
    List.map_cons, List.map_nil, boolean, integer, force]
  repeat' constructor

/-- The outer false application takes the suspension branch; its captured
group resolves f again, now at true. Recursive formation costs one auxiliary
step, then the function/force path takes38 and returns7. -/
theorem mutual_function_suspension :
    ∃ events,
      Progress.Evaluates (tracedStep parameters) (start [] mutualTerm, [])
        (.value (.atom (.integer 7)), events) 39 ∧
      bodyEntries events = [(.apply (.variable 1) (boolean true), [], some mutualGroup)] := by
  refine ⟨_, Progress.search_sound (step := tracedStep parameters)
    (fuel := 39) (by rfl), ?_⟩
  rfl

def returningClauses : List (Pattern × Expr Empty) :=
  [(.variable 2, .branch (.variable 2) (integer 7)
    (.apply (force (.variable 1)) (boolean true)))]

def returningDefinitions : List (Nat × Rhs Empty) := [(1, .delay (.function returningClauses))]

def returningGroup : Suspensions.Pure.Group Empty := .mk returningDefinitions []

def returningClosure : Expr Empty :=
  .recursive (Rhs.toBindings returningDefinitions)
    (.apply (force (.variable 1)) (boolean false))

theorem returning_closure_allowed :
    ExpressionAllowed (fun _ : Empty => False) returningClosure := by
  simp only [returningClosure, returningDefinitions, returningClauses, Rhs.toBindings,
    Rhs.toExpr, List.map_cons, List.map_nil, boolean, integer, force]
  repeat' constructor

/-- The first force returns a closure. Applying it to false forces the same
suspension after that body has returned, then applies the new closure to true.
The finite descriptor does not grow on this second entry. Formation plus the
two nested applications take51 transitions and return7. No cache is present. -/
theorem recursive_closure_forcing_after_return :
    ∃ events,
      Progress.Evaluates (tracedStep parameters) (start [] returningClosure, [])
        (.value (.atom (.integer 7)), events) 51 ∧
      bodyEntries events =
        [(.function returningClauses, [], some returningGroup),
         (.function returningClauses, [], some returningGroup)] := by
  refine ⟨_, Progress.search_sound (step := tracedStep parameters)
    (fuel := 51) (by rfl), ?_⟩
  rfl

def cycleClauses : List (Pattern × Expr Empty) :=
  [(.record [], force (.variable 2))]

def cycleBody : Expr Empty := .apply (.variable 1) (.record [])

def cycleDefinitions : List (Nat × Rhs Empty) :=
  [(1, .function cycleClauses), (2, .delay cycleBody)]

def cycleGroup : Suspensions.Pure.Group Empty := .mk cycleDefinitions []

def cycleTerm : Expr Empty :=
  .recursive (Rhs.toBindings cycleDefinitions) (force (.variable 2))

theorem cycle_allowed : ExpressionAllowed (fun _ : Empty => False) cycleTerm := by
  simp only [cycleTerm, cycleDefinitions, cycleClauses, cycleBody, Rhs.toBindings,
    Rhs.toExpr, List.map_cons, List.map_nil, force]
  repeat' constructor

/-- A local observation adapter for this unfinished concrete run. Completed
answers are absorbing; the theorem below observes an unfinished configuration. -/
private def advanceTrace :
    (Result Empty × List (Event Empty)) ⊕ (Config Empty × List (Event Empty)) →
      (Result Empty × List (Event Empty)) ⊕ (Config Empty × List (Event Empty))
  | .inl answer => .inl answer
  | .inr config => tracedStep parameters config

/-- After eight transitions the first body starts. Fifteen more enter the same
body again through f. This proves a finite prefix with identical meanings; it
does not infer divergence from an exhausted observation budget. -/
theorem cyclic_group_two_body_entries :
    ∃ config events,
      advanceTrace^[23] (.inr (start [] cycleTerm, [])) = .inr (config, events) ∧
      config.control = .eval (bodyEnvironment [] (some cycleGroup)) cycleBody ∧
      bodyEntries events = [(cycleBody, [], some cycleGroup), (cycleBody, [], some cycleGroup)] ∧
      events.length = 23 := by
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

def orderedSuspensions : Expr Empty :=
  .apply (.function [(.suspended (.atom (.integer 0)), integer 0),
    (.suspended (.variable 1), .variable 1)]) (.delay (integer 7))

/-- The first inner literal pattern fails after evaluating the body. The next
ordered clause reevaluates that same suspension and binds7. The five-step
application setup, six-step failed clause and nine-step success total20. -/
theorem failed_clause_enters_again :
    ∃ events,
      Progress.Evaluates (tracedStep parameters) (start [] orderedSuspensions, [])
        (.value (.atom (.integer 7)), events) 20 ∧
      bodyEntries events = [(integer 7, [], none), (integer 7, [], none)] := by
  refine ⟨_, Progress.search_sound (step := tracedStep parameters)
    (fuel := 20) (by rfl), ?_⟩
  rfl

def fixedException : Expr Empty :=
  .handle (.bind (.variable 1) (.delay (.raise (.variable 10))) (force (.variable 1)))
    [(.exception 10 none, integer 7)]

/-- A fixed exception raised by the body crosses its force continuation and
is matched by the surrounding handler. No new exception name is generated. -/
theorem fixed_exception_handler :
    ∃ events,
      Progress.Evaluates (tracedStep parameters)
        (start [(10, .exception 99 none)] fixedException, [])
        (.value (.atom (.integer 7)), events) 26 ∧
      bodyEntries events = [(.raise (.variable 10), [(10, .exception 99 none)], none)] := by
  refine ⟨_, Progress.search_sound (step := tracedStep parameters)
    (fuel := 26) (by rfl), ?_⟩
  rfl

/-- Effect restriction does not silently implement a reference operation. -/
theorem reference_is_excluded :
    (¬ ExpressionAllowed (fun _ : Empty => False) (.reference (integer 7))) ∧
    Progress.Evaluates (step parameters) (start [] (.reference (integer 7)))
      (.stuck (.excludedEffect .reference)) 1 := by
  refine ⟨reference_excluded _ _, ?_⟩
  exact Progress.search_sound (fuel := 1) (by rfl)

/-- The effect predicate alone permits this malformed recursive RHS. The
machine reports that shape fault instead of assuming source well-formedness. -/
theorem effect_restriction_is_not_recursive_wellformedness :
    ExpressionAllowed (fun _ : Empty => False) (.recursive [(1, integer 7)] (integer 1)) ∧
    Progress.Evaluates (step parameters) (start [] (.recursive [(1, integer 7)] (integer 1)))
      (.stuck (.invalidRecursiveRhs 1)) 1 := by
  constructor
  · unfold integer
    repeat' constructor
  · exact Progress.search_sound (fuel := 1) (by rfl)

end Examples.SuspensionPureMachine
