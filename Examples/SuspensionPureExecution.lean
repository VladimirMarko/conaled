import Applications.Suspensions.Pure.Execution

/-!
# Finite interpretation across cache reuse and runtime faults

One delayed literal is forced twice through the same binding. The actual raw
run has 21 transitions, while the pure run has 23 because its second force
replays the body. The generic finite-correspondence theorem supplies the final
represented cache; deterministic uniqueness identifies its returned witness
with the independently calculated pure run. A separate admitted application
fault retains its fault class without a source typing assumption.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureExecution
open Suspensions Suspensions.Pure
open Suspensions.Pure.Representation Suspensions.Pure.Domain
open Suspensions.Pure.DomainState Suspensions.Pure.WorldDomain
open Suspensions.Pure.Compatibility Suspensions.Pure.Simulation

private def rawParameters : Core.Machine.Parameters Empty where
  primitive := fun impossible _ => nomatch impossible
  matchException := 20
  bindException := 21

private def pureParameters : Machine.Parameters Empty where
  primitive := fun impossible _ => nomatch impossible
  matchException := 20
  bindException := 21

private def Operations : Empty → Prop := fun _ => False

private theorem compatible : ParametersCompatible Operations rawParameters pureParameters where
  primitive impossible := nomatch impossible
  matchException := rfl
  bindException := rfl

private theorem preserve : ParametersPreserve Operations pureParameters := by
  intro impossible
  cases impossible

private def literal : Core.Expr Empty := .atom (.integer 42)
private def program : Core.Expr Empty :=
  .bind (.variable 0) (.delay literal)
    (.bind (.suspended .wildcard) (.variable 0)
      (.bind (.suspended .wildcard) (.variable 0) (.atom (.integer 9))))
private def allocated : Core.Machine.Memory Empty := (Suspensions.delay Suspensions.empty literal []).1
private def finalMemory : Core.Machine.Memory Empty :=
  Suspensions.memoize allocated 0 (.atom (.integer 42))
private def answer : Core.Machine.Answer Empty := ⟨finalMemory, .value (.atom (.integer 9))⟩

private theorem program_allowed : CodeAllowed Operations program := by
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨.variable 0, (CodeAllowed.delay_iff _).mpr (CodeAllowed.atom (.integer 42)), ?_⟩
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨.suspended .wildcard, CodeAllowed.variable 0, ?_⟩
  apply (CodeAllowed.bind_iff _ _ _).mpr
  exact ⟨.suspended .wildcard, CodeAllowed.variable 0, CodeAllowed.atom (.integer 9)⟩

private theorem raw_execution : Progress.Evaluates (Core.Machine.step rawParameters)
    (Core.Machine.start Suspensions.empty [] program) answer 21 :=
  Progress.search_sound (fuel := 21) rfl

private theorem pure_execution : Progress.Evaluates (Machine.step pureParameters)
    (Machine.start [] program) (.value (.atom (.integer 9))) 23 :=
  Progress.search_sound (fuel := 23) rfl

/-- The correspondence constructs the final semantic world and validates the
actual cached memory; the different counts are both finite-machine counts. -/
theorem cached_run_has_pure_interpretation :
    Progress.Evaluates (Core.Machine.step rawParameters)
      (Core.Machine.start Suspensions.empty [] program) answer 21 ∧
    ∃ world,
      Durability.Extends (fun _ => none) world ∧ WorldAllowed Operations world ∧
      Memory.StateRep pureParameters world finalMemory ∧
      ResultRep world answer.result (.value (.atom (.integer 9))) ∧
      Progress.Evaluates (Machine.step pureParameters)
        (Machine.start [] program) (.value (.atom (.integer 9))) 23 := by
  obtain ⟨world, result, steps, extension, allowed, state, resultRep, evaluation⟩ :=
    finite_correspondence compatible preserve WorldAllowed.empty
      (ConfigRep.start (Memory.StateRep.empty pureParameters) EnvRep.nil program)
      (start_allowed EnvAllowed.nil program_allowed) raw_execution
  obtain ⟨resultEqual, countEqual⟩ := evaluation.unique pure_execution
  subst result
  subst steps
  exact ⟨raw_execution, world, extension, allowed, state, resultRep, evaluation⟩

private def malformed : Core.Expr Empty := .apply (.atom (.integer 1)) (.atom (.integer 2))
private def faultAnswer : Core.Machine.Answer Empty := ⟨Suspensions.empty, .stuck .expectedFunction⟩

private theorem malformed_allowed : CodeAllowed Operations malformed :=
  (CodeAllowed.apply_iff _ _).mpr ⟨CodeAllowed.atom (.integer 1), CodeAllowed.atom (.integer 2)⟩

private theorem raw_fault : Progress.Evaluates (Core.Machine.step rawParameters)
    (Core.Machine.start Suspensions.empty [] malformed) faultAnswer 5 :=
  Progress.search_sound (fuel := 5) rfl

private theorem pure_fault : Progress.Evaluates (Machine.step pureParameters)
    (Machine.start [] malformed) (.stuck .expectedFunction) 5 :=
  Progress.search_sound (fuel := 5) rfl

/-- Effect purity does not erase an actual application fault. Its pure
counterpart comes from the same general finite-execution theorem. -/
theorem application_fault_is_preserved :
    ∃ world,
      Memory.StateRep pureParameters world Suspensions.empty ∧
      ResultRep world faultAnswer.result (.stuck .expectedFunction) ∧
      Progress.Evaluates (Machine.step pureParameters)
        (Machine.start [] malformed) (.stuck .expectedFunction) 5 := by
  obtain ⟨world, result, steps, _, _, state, resultRep, evaluation⟩ :=
    finite_correspondence compatible preserve WorldAllowed.empty
      (ConfigRep.start (Memory.StateRep.empty pureParameters) EnvRep.nil malformed)
      (start_allowed EnvAllowed.nil malformed_allowed) raw_fault
  obtain ⟨resultEqual, countEqual⟩ := evaluation.unique pure_fault
  subst result
  subst steps
  exact ⟨world, state, resultRep, evaluation⟩

end Examples.SuspensionPureExecution
