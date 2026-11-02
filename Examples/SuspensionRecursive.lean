import Applications.Suspensions.Recursive
import Applications.Suspensions.Invariant

/-!
# Recursive creation supplies its own source applicability premise

A function and a delayed self-reference are created together beside an old
reference and an old thunk. The generic creation proof establishes the target
thunks before SRec; its independent closing relation supplies the footprint.
The function's identifier 1 does not select heap address 1: only address-valued
bindings determine the target range. A rejected raw right side separately
shows that preceding allocation is retained in the reached fault state.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionRecursive
open Suspensions Suspensions.Core Suspensions.Core.Machine Suspensions.Core.Recursive

private def parameters : Parameters Unit where
  primitive := fun _ _ => .stuck .primitive
  matchException := 20
  bindException := 21

private def base : Memory Unit := { Suspensions.empty with exceptionNames := {20, 21} }
private theorem base_bounded : Bounded base := fun _ _ => rfl
private def reference := Suspensions.allocate base (.value (.atom (.integer 41)))
private def oldThunk := Suspensions.delay reference.1 (.atom (.integer 99)) []
private def initial : Memory Unit := oldThunk.1
private def environment : Env Unit := [(42, .address reference.2)]

private theorem initial_bounded : Bounded initial :=
  Suspensions.delay_bounded
    (Suspensions.allocate_bounded base_bounded (.value (.atom (.integer 41))))
    (.atom (.integer 99)) []

private def clauses : List (Pattern × Expr Unit) := [(.wildcard, .atom (.integer 7))]
private def bindings : List (Nat × Expr Unit) :=
  [(1, .function clauses), (2, .delay (.variable 2))]
private def allocated := Suspensions.delay initial (.variable 2) environment
private def accumulated : Env Unit :=
  Env.extend (Env.extend [] [(1, .closure clauses environment [])]) [(2, .address allocated.2)]
private def prepared : Memory Unit × Env Unit := (allocated.1, accumulated)
private def closed := closeMemory prepared.1 prepared.2
private def closedEnv := closeEnvironment environment prepared.2

private theorem bindings_permitted : Permitted bindings := by
  apply (permitted_cons 1 (.function clauses) [(2, .delay (.variable 2))]).mpr
  refine ⟨.function clauses, ?_⟩
  apply (permitted_cons 2 (.delay (.variable 2)) []).mpr
  exact ⟨.delay (.variable 2), trivial⟩

private theorem creation_receipt :
    create initial environment bindings [] = .ok prepared := rfl

private theorem target_ready :
    RecursiveTargets prepared.1 (addressRange (Env.rec prepared.2)) := by
  have held := (create_preserves bindings_permitted initial_bounded
    (CreatedThunks.nil initial) creation_receipt).2.1
  exact held.targets

private theorem closing : Closes prepared.1 prepared.2 closed := close_correct target_ready

/-- The unforced-target premise and the source SRec footprint both follow
from the actual permitted creation fold and its reached machine prefix. -/
theorem recursive_creation_establishes_source_premise :
    create initial environment bindings [] = .ok prepared ∧
      RecursiveTargets prepared.1 (addressRange (Env.rec prepared.2)) ∧
      Closes prepared.1 prepared.2 closed ∧ Bounded closed ∧
      Prefix.observe parameters 8 (start initial environment (.recursive bindings (.variable 2))) =
        .inr (start closed closedEnv (.variable 2)) := by
  have bounded := (create_preserves bindings_permitted initial_bounded
    (CreatedThunks.nil initial) creation_receipt).1
  exact ⟨creation_receipt, target_ready, closing, close_bounded bounded prepared.2,
    enter_body_prefix bindings_permitted creation_receipt (.variable 2)⟩

/-- Heap address 1 remains the older thunk even though the new function's
identifier is 1. The new thunk at address 2 captures its recursive environment. -/
theorem closing_footprint :
    closed.next = 3 ∧ closed.exceptionNames = {20, 21} ∧
      closed.memory 0 = some (.value (.atom (.integer 41))) ∧
      closed.memory 1 = some (.thunk (.atom (.integer 99)) []) ∧
      closed.memory 2 = some (.thunk (.variable 2) closedEnv) ∧
      Env.lookup closedEnv 2 = some (.address 2) ∧
      Env.lookup closedEnv 1 = some (.closure clauses environment accumulated) := by
  have referenceKept := (closing.outside 0 (by decide)).trans
    (show prepared.1.memory 0 = some (.value (.atom (.integer 41))) from rfl)
  have oldThunkKept := (closing.outside 1 (by decide)).trans
    (show prepared.1.memory 1 = some (.thunk (.atom (.integer 99)) []) from rfl)
  have rebound := closing.thunks 2 (.variable 2) environment (by decide)
    (show prepared.1.memory 2 = some (.thunk (.variable 2) environment) from rfl)
  exact ⟨close_next prepared.1 prepared.2, closing.exceptionNames,
    referenceKept, oldThunkKept, rebound, rfl, rfl⟩

private theorem body_run :
    Progress.Evaluates (step parameters) (start closed closedEnv (.variable 2))
      ⟨closed, .value (.address 2)⟩ 2 := .next rfl (.done rfl)

/-- The complete source expression returns the fresh suspension without
forcing its cyclic body. The finite-memory conclusion also consumes Invariant. -/
theorem recursive_expression_returns_its_fresh_suspension :
    Progress.Evaluates (step parameters) (start initial environment (.recursive bindings (.variable 2)))
        ⟨closed, .value (.address 2)⟩ 10 ∧ Bounded closed := by
  have run : Progress.Evaluates (step parameters)
      (start initial environment (.recursive bindings (.variable 2)))
      ⟨closed, .value (.address 2)⟩ 10 :=
    evaluates_from_body bindings_permitted creation_receipt body_run
  exact ⟨run, start_evaluates_bounded initial_bounded run⟩

private def rejectedCode : Expr Unit := .atom (.integer 8)
private def rejectedBindings : List (Nat × Expr Unit) :=
  [(5, .delay rejectedCode), (7, .variable 999)]
private def beforeRejection := Suspensions.delay initial rejectedCode environment
private def rejectedAnswer : Answer Unit :=
  ⟨beforeRejection.1, .stuck (.invalidRecursiveRhs 7)⟩
private def rejectedProgram : Expr Unit := .recursive rejectedBindings (.atom (.integer 0))

private theorem rejection_run :
    Progress.Evaluates (step parameters) (start initial environment rejectedProgram) rejectedAnswer 5 :=
  .next rfl (.next rfl (.next rfl (.next rfl (.done rfl))))

/-- Outside the permitted source domain the raw helper retains the same
allocated cell and fault state as the explicit machine, with no rollback. -/
theorem raw_rejection_retains_allocations :
    create initial environment rejectedBindings [] = .error rejectedAnswer ∧
      Progress.Evaluates (step parameters) (start initial environment rejectedProgram) rejectedAnswer 5 ∧
      beforeRejection.1.next = 3 ∧
      beforeRejection.1.memory 2 = some (.thunk rejectedCode environment) ∧
      Bounded beforeRejection.1 :=
  ⟨rfl, rejection_run, rfl, Suspensions.delay_captures initial rejectedCode environment,
    start_evaluates_bounded initial_bounded rejection_run⟩

end Examples.SuspensionRecursive
