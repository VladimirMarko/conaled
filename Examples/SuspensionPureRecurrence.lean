import Applications.Suspensions.Pure.Recurrence
import Examples.SuspensionPureMachine

/-!
# Continuation boundaries and an actual recurring pure body

The cyclic source example has a fifteen-transition recurrence from an isolated
body to that identical body with caller frames appended. Its source entry takes
eight transitions. These are independently counted, checked prefix equations;
the recurrence theorem then rules out every finite result. The earlier bounded
twenty-three-step observation is not used as a divergence argument.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureRecurrence
open Suspensions.Pure Suspensions.Pure.Machine Suspensions.Pure.Recurrence
open Examples.SuspensionPureMachine

theorem wildcard_after_literal :
    Progress.Evaluates (step parameters)
      (appendFrames (start [] (integer 7)) [.force [] .wildcard]) (.matched []) 4 := by
  have body : Progress.Evaluates (step parameters) (start [] (integer 7))
      (.value (.atom (.integer 7))) 2 := .next rfl (.done rfl)
  exact force_wildcard_after_body body []

/-- A machine fault is not converted into a source exception by adding a
handler. Both the answer and its single transition are retained. -/
theorem handler_cannot_catch_body_fault :
    Progress.Evaluates (step parameters)
      (appendFrames (start [] (.variable 99)) [.handler [] [(.wildcard, integer 7)]])
      (.stuck (.unboundVariable 99)) 1 := by
  have body : Progress.Evaluates (step parameters) (start [] (.variable 99))
      (.stuck (.unboundVariable 99)) 1 := .done rfl
  exact evaluates_stuck_append body rfl _

/-- The same caller can handle a raised packet. The body's four transitions
and caller's seven overlap at the isolated delivery, giving ten in total. -/
theorem handler_can_catch_source_exception :
    Progress.Evaluates (step parameters)
      (appendFrames (start [(10, .exception 99 none)] (.raise (.variable 10)))
        [.handler [] [(.wildcard, integer 7)]])
      (.value (.atom (.integer 7))) 10 := by
  have body : Progress.Evaluates (step parameters)
      (start [(10, .exception 99 none)] (.raise (.variable 10))) (.raised (.exception 99 none)) 4 :=
    Progress.search_sound (fuel := 4) (by rfl)
  have residual : Progress.Evaluates (step parameters)
      ⟨.raised (.exception 99 none), [.handler [] [(.wildcard, integer 7)]]⟩
      (.value (.atom (.integer 7))) 7 := Progress.search_sound (fuel := 7) (by rfl)
  exact evaluates_append body rfl _ residual

/-- A caller fault does not imply that the isolated body faulted. The all-outcome
split recovers its normal value in two steps and a one-step failing caller. -/
theorem caller_fault_decomposes :
    ∃ bodyAnswer control n m,
      Progress.Evaluates (step parameters) (start [] (integer 7)) bodyAnswer n ∧
      boundaryControl bodyAnswer = some control ∧
      Progress.Evaluates (step parameters)
        ⟨control, [.argument (.atom (.integer 9))]⟩ (.stuck .expectedFunction) m ∧
      bodyAnswer = .value (.atom (.integer 7)) ∧ n = 2 ∧ m = 1 := by
  have body : Progress.Evaluates (step parameters) (start [] (integer 7))
      (.value (.atom (.integer 7))) 2 := .next rfl (.done rfl)
  have residual : Progress.Evaluates (step parameters)
      ⟨.value (.atom (.integer 7)), [.argument (.atom (.integer 9))]⟩
      (.stuck .expectedFunction) 1 := .done rfl
  have whole := evaluates_append body rfl [.argument (.atom (.integer 9))] residual
  rcases evaluates_split_all whole with ⟨isolated, _⟩ |
    ⟨bodyAnswer, control, n, m, isolated, boundary, caller, count⟩
  · have impossible := (body.unique isolated).1
    cases impossible
  · have same := body.unique isolated
    exact ⟨bodyAnswer, control, n, m, isolated, boundary, caller,
      same.1.symm, same.2.symm, by omega⟩

/-- A zero-length recurrence exists even for a terminating literal. The
strictly positive prefix premise of the recurrence theorem is essential. -/
theorem zero_prefix_is_not_obstruction :
    Reaches parameters 0 (start [] (integer 7)) (appendFrames (start [] (integer 7)) []) ∧
    Progress.Terminates (step parameters) (start [] (integer 7)) := by
  exact ⟨rfl, .value (.atom (.integer 7)), 2, .next rfl (.done rfl)⟩

def cycleEnvironment : Env Empty := bodyEnvironment [] (some cycleGroup)

def cycleSuspension : Value Empty := .suspension cycleBody [] (some cycleGroup)

def cycleInput : Config Empty := start cycleEnvironment cycleBody

/-- The last two frames belong to force and f(), respectively. -/
def recurringCaller : List (Frame Empty) :=
  [.force cycleEnvironment (.variable 0),
   .clause cycleEnvironment (.variable 0) [] cycleSuspension,
   .applicationResult, .applicationResult]

def enteringCaller : List (Frame Empty) :=
  [.force cycleEnvironment (.variable 0),
   .clause cycleEnvironment (.variable 0) [] cycleSuspension,
   .applicationResult]

/-- The unrolling preserves the exact code/capture/descriptor body event. -/
theorem cycle_body_entry_identity :
    transition parameters
      ⟨.pattern cycleEnvironment (.suspended (.variable 0)) cycleSuspension,
        recurringCaller.tail⟩ =
      proceed (.eval cycleEnvironment cycleBody) recurringCaller
        (.body cycleBody [] (some cycleGroup)) :=
  body_transition parameters cycleEnvironment [] (some cycleGroup)
    (.variable 0) cycleBody recurringCaller.tail

/-- Eight steps select f's body; seven more enter s at the identical body
input. This is an actual recurrent prefix, with its full residual stack. -/
theorem cycle_body_recurs :
    Reaches parameters 15 cycleInput (appendFrames cycleInput recurringCaller) := rfl

theorem cycle_body_has_no_finite_result :
    ¬ Progress.Terminates (step parameters) cycleInput :=
  recurring_prefix_not_terminates (by decide) cycle_body_recurs

/-- Group formation takes one auxiliary step; derived force reaches the stored
body in seven more. The original source term is used without modification. -/
theorem cycle_source_enters_body :
    Reaches parameters 8 (start [] cycleTerm) (appendFrames cycleInput enteringCaller) := rfl

theorem cycle_source_has_no_finite_result :
    ¬ Progress.Terminates (step parameters) (start [] cycleTerm) :=
  cycle_source_enters_body.not_terminates
    (not_terminates_append cycle_body_has_no_finite_result enteringCaller)

/-- The negative execution result has an inhabited effect-restricted source
domain, as established independently of the recurrence proof. -/
theorem pure_cycle_has_no_finite_result :
    ExpressionAllowed (fun _ : Empty => False) cycleTerm ∧
    ¬ Progress.Terminates (step parameters) (start [] cycleTerm) :=
  ⟨cycle_allowed, cycle_source_has_no_finite_result⟩

theorem cycle_search_none (fuel : Nat) :
    Progress.search (step parameters) fuel (start [] cycleTerm) = none :=
  search_none_of_not_terminates cycle_source_has_no_finite_result fuel

end Examples.SuspensionPureRecurrence
