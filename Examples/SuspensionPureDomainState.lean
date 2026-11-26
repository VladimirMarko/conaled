import Applications.Suspensions.Pure.DomainState
import Examples.SuspensionPureDomain
import Examples.SuspensionPureMachine

/-!
# Connected preservation cases for actual pure execution

The recursive returned-closure program keeps its existing 51-transition run
and its two exact body-entry meanings. The new theorem supplies domain facts
at the final result and at the actual unfinished 50-transition prefix. A
separate formation case returns a closure with the cyclic group in its capture.

The admitted bad application still faults after five transitions. Successful
scalar applications take six transitions, including final value delivery, under the
independent primitive-output preservation law. No example assumes type safety.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureDomainState
open Suspensions.Pure Suspensions.Pure.Domain Suspensions.Pure.DomainState
open Suspensions.Pure.Machine

private theorem no_operations_preserve {Primitive : Type} (parameters : Parameters Primitive) :
    ParametersPreserve (fun _ => False) parameters :=
  fun _ impossible => False.elim impossible

namespace Returned
open Examples.SuspensionPureMachine

private theorem clauses_code :
    ClausesCodeAllowed (fun _ : Empty => False) returningClauses := by
  apply (ClausesCodeAllowed.cons_iff _ _ []).mpr
  refine ⟨.variable 2, ?_, ClausesCodeAllowed.nil⟩
  apply (CodeAllowed.branch_iff _ _ _).mpr
  exact ⟨CodeAllowed.variable 2, CodeAllowed.atom (.integer 7),
    (CodeAllowed.apply_iff _ _).mpr
      ⟨(CodeAllowed.variable 1).force, CodeAllowed.atom (.boolean true)⟩⟩

theorem program_code : CodeAllowed (fun _ : Empty => False) returningClosure := by
  apply (CodeAllowed.recursive_iff _ _).mpr
  refine ⟨?_, ?_, Rhs.toBindings_permitted returningDefinitions, by decide⟩
  · apply (NamedCodeAllowed.cons_iff _ _ []).mpr
    exact ⟨(CodeAllowed.delay_iff _).mpr ((CodeAllowed.function_iff _).mpr clauses_code),
      NamedCodeAllowed.nil⟩
  · apply (CodeAllowed.apply_iff _ _).mpr
    exact ⟨(CodeAllowed.variable 1).force, CodeAllowed.atom (.boolean false)⟩

/-- The old execution and event expectation are retained verbatim; the domain
conclusions are obtained through the universal finite-run and prefix laws. -/
theorem execution_preserves :
    (∃ events,
      Progress.Evaluates (tracedStep parameters) (start [] returningClosure, [])
        (.value (.atom (.integer 7)), events) 51 ∧
      bodyEntries events =
        [(.function returningClauses, [], some returningGroup),
         (.function returningClauses, [], some returningGroup)]) ∧
    ResultAllowed (fun _ : Empty => False) (.value (.atom (.integer 7))) ∧
    Recurrence.Reaches parameters 50 (start [] returningClosure)
      ⟨.value (.atom (.integer 7)), []⟩ ∧
    ConfigAllowed (fun _ : Empty => False) ⟨.value (.atom (.integer 7)), []⟩ := by
  obtain ⟨events, run, entries⟩ := recursive_closure_forcing_after_return
  have initial := start_allowed (EnvAllowed.nil (operations := fun _ : Empty => False)) program_code
  have ordinary := traced_evaluates_erases run
  have reached := Recurrence.evaluates_boundary_reaches ordinary rfl
  exact ⟨⟨events, run, entries⟩,
    evaluates_preserves (no_operations_preserve parameters) initial ordinary,
    reached, reaches_preserves (no_operations_preserve parameters) initial reached⟩

end Returned

namespace Capture
open Examples.SuspensionPureValues Examples.SuspensionPureDomain

/-- Formation returns the actual closure with its recursive suspension still
reachable through the capture. The output domain is derived from the run. -/
theorem returned_capture_preserves (parameters : Parameters Unit) :
    Progress.Evaluates (step parameters) (start cachedBodyEnvironment cachedCode)
      (.value cachedClosure) 2 ∧
    ValueAllowed (fun _ : Unit => False) cachedClosure ∧
    Env.lookup cachedBodyEnvironment 1 =
      some (.suspension cachedCode cachedOuter (some cachedGroup)) := by
  obtain ⟨_, run, lookup⟩ := returned_closure_connected parameters
  have capture : EnvAllowed (fun _ : Unit => False) cachedBodyEnvironment :=
    bodyEnvironment_allowed cached_group_allowed.outer (.some cached_group_allowed)
  have delayed : CodeAllowed (fun _ : Unit => False) (.delay cachedCode) :=
    cached_group_allowed.definitions.member (name := 1) (by
      change (1, Suspensions.Core.Expr.delay cachedCode) ∈ [(1, .delay cachedCode)]
      exact List.mem_cons_self)
  have initial := start_allowed capture ((CodeAllowed.delay_iff cachedCode).mp delayed)
  exact ⟨run, evaluates_preserves (no_operations_preserve parameters) initial run, lookup⟩

end Capture

/-- The hereditary domain admits this fault. The actual five-step run remains
part of the conclusion, so the allowed diagnostic is not a success claim. -/
theorem expected_function_fault_preserved (raw : Suspensions.Core.Machine.Parameters Unit)
    (pure : Parameters Unit) :
    ConfigAllowed (fun _ : Unit => False)
      (start [] (.apply (.atom (.integer 3)) (.atom (.integer 4)))) ∧
    Progress.Evaluates (step pure)
      (start [] (.apply (.atom (.integer 3)) (.atom (.integer 4))))
      (.stuck .expectedFunction) 5 ∧
    ResultAllowed (fun _ : Unit => False) (.stuck .expectedFunction) := by
  obtain ⟨code, _, run, _⟩ := Examples.SuspensionPureDomain.admitted_application_faults raw pure
  have initial := start_allowed EnvAllowed.nil code
  exact ⟨initial, run, evaluates_preserves (no_operations_preserve pure) initial run⟩

namespace Scalar
open Suspensions.Pure.Compatibility

private def parameters : Parameters BasicOperation := basicPureParameters 10 11
private def Selected : BasicOperation → Prop := fun _ => True

private theorem scalar_start (operation : BasicOperation) (input : Suspensions.Core.Atom) :
    ConfigAllowed Selected (start [] (.apply (.primitive operation) (.atom input))) :=
  start_allowed EnvAllowed.nil ((CodeAllowed.apply_iff _ _).mpr
    ⟨(CodeAllowed.primitive_iff operation).mpr trivial, CodeAllowed.atom input⟩)

theorem successor_preserved :
    Progress.Evaluates (step parameters)
      (start [] (.apply (.primitive .successor) (.atom (.integer 41))))
      (.value (.atom (.integer 42))) 6 ∧
    ResultAllowed Selected (.value (.atom (.integer 42))) := by
  have run : Progress.Evaluates (step parameters)
      (start [] (.apply (.primitive .successor) (.atom (.integer 41))))
      (.value (.atom (.integer 42))) 6 :=
    .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))))
  exact ⟨run, evaluates_preserves (basic_parameters_preserve Selected 10 11)
    (scalar_start .successor (.integer 41)) run⟩

theorem boolean_preserved :
    Progress.Evaluates (step parameters)
      (start [] (.apply (.primitive .isZero) (.atom (.integer 0))))
      (.value (.atom (.boolean true))) 6 ∧
    ResultAllowed Selected (.value (.atom (.boolean true))) := by
  have run : Progress.Evaluates (step parameters)
      (start [] (.apply (.primitive .isZero) (.atom (.integer 0))))
      (.value (.atom (.boolean true))) 6 :=
    .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))))
  exact ⟨run, evaluates_preserves (basic_parameters_preserve Selected 10 11)
    (scalar_start .isZero (.integer 0)) run⟩

end Scalar
end Examples.SuspensionPureDomainState
